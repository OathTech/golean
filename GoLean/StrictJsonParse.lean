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

/-- Adapter resource limits, not restrictions on Go semantic types. -/
def maxNestingDepth : Nat := 64
def maxNumberChars : Nat := 256
def maxNumberExponent : Nat := 1024

private def numberDelimiter (c : Char) : Bool :=
  c.isWhitespace || c == ',' || c == ']' || c == '}' || c == ':' ||
    c == '[' || c == '{' || c == '"'

private partial def numberToken (path : String) (acc : String := "") : Parser String := do
  if ← isEof then return acc
  let c ← peek!
  if numberDelimiter c then return acc
  if acc.length >= maxNumberChars then
    fail s!"{path}: JSON number exceeds {maxNumberChars} characters"
  skip
  numberToken path (acc.push c)

-- Check grammar and exponent magnitude BEFORE Lean's numeric constructor
-- materializes any power of ten. Token collection is itself bounded.
private def checkNumber (path token : String) : Except String Unit := do
  let chars := token.toList
  let chars := if chars.head? == some '-' then chars.tail else chars
  let whole := chars.takeWhile Char.isDigit
  if whole.isEmpty then throw s!"{path}: invalid JSON number: expected integer digit"
  if whole.length > 1 && whole.head? == some '0' then
    throw s!"{path}: leading zero in JSON number"
  let rest := chars.drop whole.length
  let rest ← if rest.head? == some '.' then do
      let fraction := rest.tail.takeWhile Char.isDigit
      if fraction.isEmpty then throw s!"{path}: JSON number fraction needs a digit"
      pure (rest.tail.drop fraction.length)
    else pure rest
  if rest.isEmpty then return ()
  unless rest.head? == some 'e' || rest.head? == some 'E' do
    throw s!"{path}: invalid character in JSON number"
  let digits := rest.tail
  let digits := if digits.head? == some '+' || digits.head? == some '-' then
      digits.tail else digits
  if digits.isEmpty || !digits.all Char.isDigit then
    throw s!"{path}: JSON number exponent needs decimal digits"
  let some exponent := (String.ofList digits).toNat?
    | throw s!"{path}: invalid JSON number exponent"
  if exponent > maxNumberExponent then
    throw s!"{path}: JSON number exponent exceeds {maxNumberExponent} in magnitude"

private def boundedNumber (path : String) : Parser JsonNumber := do
  let token ← numberToken path
  match checkNumber path token with
  | .error message => fail message
  | .ok () =>
    match Parser.run (do let n ← Lean.Json.Parser.num; eof; pure n) token with
    | .ok n => return n
    | .error message => fail s!"{path}: invalid JSON number: {message}"

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

private partial def inputValue (remaining : Nat) (path : String) : Parser Json := do
  let c ← peek!
  if (c == '[' || c == '{') && remaining == 0 then
    fail s!"{path}: JSON nesting deeper than {maxNestingDepth}"
  if c == '[' then
    skip; ws
    if (← peek!) == ']' then
      skip; ws
      return .arr #[]
    else
      return .arr (← inputArray (remaining - 1) path #[])
  else if c == '{' then
    skip; ws
    if (← peek!) == '}' then
      skip; ws
      return .obj ∅
    else
      return .obj (← inputObject (remaining - 1) path ∅)
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
  else if c == '-' || c == '+' || c == '.' || c == 'N' || c == 'I' || c.isDigit then
    let value ← boundedNumber path
    ws
    return .num value
  else
    fail s!"{path}: expected JSON value"

private partial def inputArray (remaining : Nat) (path : String) (values : Array Json) :
    Parser (Array Json) := do
  let value ← inputValue remaining s!"{path}[{values.size}]"
  let values := values.push value
  let separator ← any
  if separator == ']' then
    ws
    return values
  else if separator == ',' then
    ws
    inputArray remaining path values
  else
    fail s!"{path}: expected ',' or ']'"

private partial def inputObject (remaining : Nat) (path : String) (values : Obj) : Parser Obj := do
  Lean.Json.Parser.lookahead (fun c => c == '"') "object key"
  skip
  let key ← losslessString
  if values.contains key then
    fail s!"{path}: duplicate JSON object key {repr key}"
  ws
  Lean.Json.Parser.lookahead (fun c => c == ':') ":"
  skip; ws
  let value ← inputValue remaining s!"{path}[{repr key}]"
  let values := values.insert key value
  let separator ← any
  if separator == '}' then
    ws
    return values
  else if separator == ',' then
    ws
    inputObject remaining path values
  else
    fail s!"{path}: expected ',' or '}}'"

end

/-- Parse textual JSON without collapsing duplicate keys or replacing
malformed Unicode escapes. This does not check a declaration schema. -/
def parse (input : String) : Except String Json :=
  Parser.run (do
    ws
    let value ← inputValue maxNestingDepth "$"
    eof
    return value) input

/-- The file-input boundary must validate UTF-8 before constructing String.
Raw non-UTF-8 bytes refuse; a replacement character is never substituted. -/
def parseBytes (input : ByteArray) : Except String Json := do
  let some text := String.fromUTF8? input
    | throw "JSON input is not valid UTF-8"
  parse text

end GoLean.StrictJson
