import GoLean.StrictJson
import Lean.Data.Json.Parser

/-! Lossless JSON input for the I1 declaration envelope.

`Lean.Json` stores object members in a map: duplicate keys have already
disappeared by the time `requireExactKeys` sees an object. This input layer
rejects duplicates, including differently escaped spellings of the same
decoded key, before insertion. It also refuses unpaired surrogate escapes
instead of substituting U+FFFD into an identity or signature.

The parser reuses the pinned Lean JSON numeric/escape primitives. Its
container grammar follows Lean/Data/Json/Parser.lean (Apache-2.0, Gabriel
Ebner and Marc Huisinga). Recursive parsing stays outside the total GoCore
semantic model. This module is not yet wired into production NativeToIR;
parsed-JSON schema validation and executable admission remain separate.
-/

namespace GoLean.StrictJson

open Lean Std.Internal.Parsec Std.Internal.Parsec.String

private def losslessEscape : Parser Char := do
  if (← peek!) != 'u' then
    return ← Lean.Json.Parser.escapedChar
  skip
  let a ← Lean.Json.Parser.hexChar
  let b ← Lean.Json.Parser.hexChar
  let c ← Lean.Json.Parser.hexChar
  let d ← Lean.Json.Parser.hexChar
  let value := (a <<< 12) ||| (b <<< 8) ||| (c <<< 4) ||| d
  if h : value < 0xD800 then
    return ⟨value.toUInt32, Or.inl h⟩
  else if h' : value < 0xE000 then
    if value < 0xDC00 then
      attempt (Lean.Json.Parser.finishSurrogatePair value) <|>
        fail "unpaired high surrogate in JSON string"
    else
      fail "unpaired low surrogate in JSON string"
  else
    return ⟨value.toUInt32, Or.inr ⟨Nat.not_lt.mp h',
      Nat.lt_trans value.toFin.isLt (by decide)⟩⟩

private partial def losslessString (acc : String := "") : Parser String := do
  let c ← any
  if c == '"' then return acc
  else if c == '\\' then
    losslessString (acc.push (← losslessEscape))
  else if c.val < 0x20 then
    fail "unescaped control character in JSON string"
  else
    losslessString (acc.push c)

mutual

private partial def inputValue (path : String) : Parser Json := do
  let c ← peek!
  if c == '[' then
    skip; ws
    if (← peek!) == ']' then
      skip; ws
      return .arr #[]
    else
      return .arr (← inputArray path #[])
  else if c == '{' then
    skip; ws
    if (← peek!) == '}' then
      skip; ws
      return .obj ∅
    else
      return .obj (← inputObject path ∅)
  else if c == '"' then
    skip
    let value ← losslessString
    ws
    return .str value
  else if c == 'f' then
    skipString "false"; ws
    return .bool false
  else if c == 't' then
    skipString "true"; ws
    return .bool true
  else if c == 'n' then
    skipString "null"; ws
    return .null
  else if c == '-' || ('0' <= c && c <= '9') then
    let value ← Lean.Json.Parser.num
    ws
    return .num value
  else
    fail s!"{path}: expected JSON value"

private partial def inputArray (path : String) (values : Array Json) :
    Parser (Array Json) := do
  let value ← inputValue s!"{path}[{values.size}]"
  let values := values.push value
  let separator ← any
  if separator == ']' then
    ws
    return values
  else if separator == ',' then
    ws
    inputArray path values
  else
    fail s!"{path}: expected ',' or ']'"

private partial def inputObject (path : String) (values : Obj) : Parser Obj := do
  Lean.Json.Parser.lookahead (fun c => c == '"') "object key"
  skip
  let key ← losslessString
  if values.contains key then
    fail s!"{path}: duplicate JSON object key {repr key}"
  ws
  Lean.Json.Parser.lookahead (fun c => c == ':') ":"
  skip; ws
  let value ← inputValue s!"{path}[{repr key}]"
  let values := values.insert key value
  let separator ← any
  if separator == '}' then
    ws
    return values
  else if separator == ',' then
    ws
    inputObject path values
  else
    fail s!"{path}: expected ',' or '}}'"

end

/-- Parse textual JSON without collapsing duplicate keys or replacing
malformed Unicode escapes. This does not check a declaration schema. -/
def parse (input : String) : Except String Json :=
  Parser.run (do
    ws
    let value ← inputValue "$"
    eof
    return value) input

/-- The file-input boundary must validate UTF-8 before constructing String.
Raw non-UTF-8 bytes refuse; a replacement character is never substituted. -/
def parseBytes (input : ByteArray) : Except String Json := do
  let some text := String.fromUTF8? input
    | throw "JSON input is not valid UTF-8"
  parse text

end GoLean.StrictJson
