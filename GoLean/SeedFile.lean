import GoLean.GoCore.SeedPool
import GoLean.StrictJson
import GoLean.StrictJsonParse

/-!
# The seed file `golean-seed-v1` — the CLI's decoder (seeded-heap slice B)

[AGENT worker, lane `cli/seeded-heap-b-1012`] 2026-10-12, slice B of the design note
`docs/2026-10-09_seeded-heap-design.md` (§1 the grammar, §6 the flags; [USER] Mike 2026-10-12
«Agree on the two strategic questions, let's do it», relayed — GO, three slices; gc-verified
CONFIRMED D2/D3/D6/D7/D9/D10, the six deviations and the v1 value set the same day, relayed).

OUTSIDE the semantic core: this module decodes the SHAPE of a seed file onto slice A's
`SeedCell`/`SeedValue` (`GoLean/GoCore/Seed.lean`); the TYPING of every value (ints at their kind,
struct fields complete, refs against the declared leaf type, `nil` at pointers only) is the core
resolver's, decided once at setup (§1: «the CLI decodes the SHAPE, the core decides the TYPING
once»). What IS decided here, by name, before any machine step:

* the bytes: the strict byte parser (`StrictJson.parseBytes` — duplicate keys, invalid UTF-8,
  unpaired surrogates refuse there: BUG-110's discipline), and a lexical pre-scan refusing any
  JSON number with a fraction or an exponent (the parsed `JsonNumber` cannot tell `100` from
  `1e2`, so the TOKEN is judged);
* the envelope: exact keys at every level (`requireExactKeys`, the observation decoder's rule),
  the literal schema, `cells` an array, each cell exactly `{type, value}`;
* the type spelling (§1 `TypeSpelling ::= bool | int | int8 | … | uint64 | [<nat>]T | *T |
  <Ident>`): spellings outside the grammar refuse «not in golean-seed-v1» naming the class
  (`uintptr`, floats, complex, `string`, `byte`/`rune`, slices, maps, channels, functions,
  interfaces, anonymous structs, `sync.*`, any other qualified name); an `<Ident>` resolves by
  `TypeId.unqualified` over the program's type table — the observation channel's own naming —
  and refuses when it names NO declared type or MORE THAN ONE (D2: ambiguity refuses, never
  picks). The two reserved entries (`struct{}`, `$runtime.Error`) are not declared types and are
  never candidates. A declared type spelled like a builtin (`type int …`) makes that builtin
  spelling ambiguous and it refuses too;
* the value shape (§1 `SeedJson`): integers, `true`/`false`, objects as struct values keyed by
  field name, arrays, `{"ref":{"cell":<nat>,"path":[…]}}`, `{"nil":true}`. An object carrying a
  `ref` or `nil` key IS that form and must carry nothing else — so ANY struct with a field named
  `ref` or `nil` (lower-case) is not expressible in v1 (stated limit of the §1 grammar; the
  refusal names it).
  `null` and strings are not seed values.

Recursion is FUEL-bounded by the parse's own nesting bound (`wireNestingDepth`), so every
function here is total; exhaustion refuses by name and is unreachable on a parsed file.

Recorded, not changed (the slice B pre-merge review's NITs, 2026-10-12): `isIdent` is ASCII-only,
so a declared type with a Unicode name refuses «not in the grammar» (fails closed); the D2
ambiguity text names the internal keys (`main.T·1`), as other refusals do; `declaredCandidates`
matches non-`main` declared types by their unqualified name too — which spelling the Go twin's
prologue pastes for them is slice C's concern.
-/

namespace GoLean.SeedFile

open Lean
open GoLean.GoCore
open GoLean.GoCore.Machine

/-- The literal schema of a seed file. -/
def seedSchema : String := "golean-seed-v1"

/-! ## The lexical number pre-scan -/

/-- A number token the seed grammar refuses: a fraction or an exponent (`.`, `e`, `E`), or the
NEGATIVE ZERO `-0` (review NIT-1, 2026-10-12: the parsed value is `0` and the sign is lost, so the
token is judged — refused at every kind, since the kind is resolved only in the core; the Go twin
refuses the same token). -/
def badNumberTok (t : String) : Bool :=
  t.any (fun c => c == '.' || c == 'e' || c == 'E') || t == "-0"

/-- The first JSON number token OUTSIDE strings that `badNumberTok` refuses, if any. A char-by-char state machine: `inStr`/`esc` track string state, `tok`
the number token being read (`none` outside one). Structural on the char list. -/
def badNumberToken : List Char → (inStr esc : Bool) → Option String → Option String
  | [], _, _, tok => tok.bind (fun t => if badNumberTok t then some t else none)
  | c :: cs, inStr, esc, tok =>
      if inStr then
        if esc then badNumberToken cs true false none
        else if c == '\\' then badNumberToken cs true true none
        else if c == '"' then badNumberToken cs false false none
        else badNumberToken cs true false none
      else
        match tok with
        | some t =>
            if c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-' then
              badNumberToken cs false false (some (t.push c))
            else if badNumberTok t then some t
            else badNumberToken (c :: cs) false false none
        | none =>
            if c == '"' then badNumberToken cs true false none
            else if c.isDigit || c == '-' then badNumberToken cs false false (some (String.singleton c))
            else badNumberToken cs false false none
termination_by cs _ _ tok => (cs.length, if tok.isSome then 1 else 0)

/-! ## Type spellings -/

/-- The integer kinds of the grammar, by their Go spelling. -/
def intKindOfSpelling? : String → Option IntKind
  | "int" => some .int | "uint" => some .uint
  | "int8" => some .int8 | "uint8" => some .uint8
  | "int16" => some .int16 | "uint16" => some .uint16
  | "int32" => some .int32 | "uint32" => some .uint32
  | "int64" => some .int64 | "uint64" => some .uint64
  | _ => none

/-- The builtin spellings of the grammar (a declared type spelled like one makes it ambiguous). -/
def builtinSpellings : List String :=
  ["bool", "int", "uint", "int8", "uint8", "int16", "uint16", "int32", "uint32", "int64", "uint64"]

/-- Go builtin type spellings OUTSIDE v1, each refused by name (D9). -/
def outsideBuiltin? : String → Option String
  | "uintptr" => some "uintptr"
  | "float32" => some "a float type (float32)"
  | "float64" => some "a float type (float64)"
  | "complex64" => some "a complex type (complex64)"
  | "complex128" => some "a complex type (complex128)"
  | "string" => some "string"
  | "byte" => some "byte (spell it uint8)"
  | "rune" => some "rune (spell it int32)"
  | "any" => some "an interface type (any)"
  | "error" => some "an interface type (error)"
  | _ => none

/-- An ASCII Go identifier: a letter or `_`, then letters, digits, `_`; not the blank `_`. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_') && s != "_"

/-- The declared types spelled `ident` (by `TypeId.unqualified`), outside the reserved prefix. -/
def declaredCandidates (types : TypeEnv) (ident : String) : List (Nat × TypeId) :=
  ((List.range types.size).filterMap fun i =>
    if i < TypeEnv.reserved.size then none else
    match types[i]? with
    | some (tid, _) => if tid.unqualified == ident then some (i, tid) else none
    | none => none)

/-- Resolve an `<Ident>` to its declared type: exactly one candidate, else a named refusal. -/
def resolveIdent (types : TypeEnv) (ident : String) : Except String Ty :=
  match declaredCandidates types ident with
  | [(i, _)] => .ok (.defined i)
  | [] => .error s!"type {ident}: no declared type of that name in the program"
  | cs => .error s!"type {ident}: ambiguous — {cs.length} declared types are spelled {ident} ({", ".intercalate (cs.map (·.2.key))}); golean-seed-v1 refuses, never picks (D2)"

/-- The refusal for a spelling OUTSIDE the grammar's v1 classes. -/
def notInV1 (spelling what : String) : String :=
  s!"type spelling {spelling}: {what} is not in golean-seed-v1"

/-- Parse a decimal nat without a sign or leading zeros (`0` itself allowed). -/
def parseDecimalNat? (s : String) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none
  else if s.length > 1 && s.front == '0' then none
  else s.toNat?

/-- Go KEYWORDS that head a type literal: never a declared type's name, so a bare one is that
class's refusal rather than an `<Ident>` lookup. -/
def typeKeywordClass? : String → Option String
  | "chan" => some "a channel type"
  | "func" => some "a function type"
  | "interface" => some "an interface type"
  | "struct" => some "an anonymous struct type"
  | "map" => some "a map type"
  | _ => none

/-- The class of a NON-identifier spelling outside v1 (a type literal), if any. Tested only
after the `<Ident>` branch has declined, so a declared type named `channel`, `funcTable`,
`structure` or `interfaceSet` is never mistaken for a literal (review MEDIUM-1). -/
def typeLiteralClass? (s : String) : Option String :=
  if s.startsWith "map[" then some "a map type"
  else if s.startsWith "chan " || s.startsWith "chan<-" || s.startsWith "<-chan" then some "a channel type"
  else if s.startsWith "func(" || s.startsWith "func (" then some "a function type"
  else if s.startsWith "interface{" || s.startsWith "interface {" then some "an interface type"
  else if s.startsWith "struct{" || s.startsWith "struct {" then some "an anonymous struct type"
  else if s.startsWith "sync." then some "a sync type"
  else none

/-- Parse a type spelling (§1). `outer` is the WHOLE spelling as written in the file — every
refusal names it (a refusal inside `*T` or `[3]T` names `*T`/`[3]T`, never the bare remainder);
`fuel` bounds the nesting (the spelling's length suffices).

Order (review MEDIUM-1 / NIT-2): `*T`, `[]T` (refused), `[n]T`; then an IDENTIFIER — a keyword
(`chan`, `func`, …) is its class's refusal; a builtin spelling (in v1 or outside it, `int` or
`float64`) that a declared type also spells is the D2 ambiguity; a builtin in v1 resolves; one
outside v1 is refused naming its class; anything else is an `<Ident>` resolved over the table;
then the non-identifier type literals and qualified names, each refused by class; anything else
is outside the grammar. -/
def parseTypeSpelling (types : TypeEnv) (outer : String) : Nat → String → Except String Ty
  | 0, _ => .error s!"type spelling {outer}: nesting exceeds the spelling's length (internal bound)"
  | fuel + 1, s =>
      if s.startsWith "*" then
        (parseTypeSpelling types outer fuel (s.drop 1).toString).map Ty.pointer
      else if s.startsWith "[]" then .error (notInV1 outer "a slice type")
      else if s.startsWith "[" then
        match (s.drop 1).toString.splitOn "]" with
        | len :: rest@(_ :: _) =>
            match parseDecimalNat? len with
            | some n => (parseTypeSpelling types outer fuel ("]".intercalate rest)).map (Ty.array n)
            | none => .error s!"type spelling {outer}: array length {len} is not a decimal nat (no sign, no leading zeros, no constant expression)"
        | _ => .error s!"type spelling {outer}: unterminated array length"
      else if isIdent s then
        match typeKeywordClass? s with
        | some what => .error (notInV1 outer what)
        | none =>
          let builtin := builtinSpellings.contains s || (outsideBuiltin? s).isSome
          if builtin && !(declaredCandidates types s).isEmpty then
            .error s!"type {s}: ambiguous — the builtin {s} and a declared type spelled {s}; golean-seed-v1 refuses, never picks (D2)"
          else if s == "bool" then .ok .bool
          else match intKindOfSpelling? s with
            | some k => .ok (.int k)
            | none =>
              match outsideBuiltin? s with
              | some what => .error (notInV1 outer what)
              | none => resolveIdent types s
      else
        match typeLiteralClass? s with
        | some what => .error (notInV1 outer what)
        | none =>
          if (s.splitOn ".").length > 1 && (s.splitOn ".").all isIdent then
            .error (notInV1 outer "a package-qualified type (write the declared type's unqualified Go name)")
          else .error s!"type spelling {outer}: not in the golean-seed-v1 type grammar (bool | int | int8 | … | uint64 | [<nat>]T | *T | <Ident>)"

/-! ## Values -/

/-- A JSON number as an integer: exponent 0 (the pre-scan already refused fractions and
exponents by token; this is the backstop on the parsed value). -/
def jsonInt? (n : JsonNumber) : Option Int :=
  if n.exponent == 0 then some n.mantissa else none

/-- One path element: a field name (a string) or an index (a nat). -/
def decodePathElem (path : String) : Json → Except String SeedPathElem
  | .str f => .ok (.field f)
  | .num n =>
      match jsonInt? n with
      | some i => if i ≥ 0 then .ok (.index i.toNat) else .error s!"{path}: negative index {i}"
      | none => .error s!"{path}: not an integer index"
  | _ => .error s!"{path}: a path element is a field name (string) or an index (nat)"

/-- The v1 limit the `ref`/`nil` forms impose (§1's grammar; review LOW-1): ANY struct with a
field named `ref` or `nil` cannot be written as a seed value. -/
def refNilLimit : String :=
  "a struct with a field named ref or nil is not expressible in golean-seed-v1"

/-- A reference body `{"cell":<nat>,"path":[…]}` (exact keys). -/
def decodeRefBody (path : String) (json : Json) : Except String SeedValue := do
  let obj ← match json with
    | .obj o => pure o
    | _ => throw s!"{path}: expected {"{"}\"cell\":<nat>,\"path\":[…]} — {refNilLimit}"
  StrictJson.requireExactKeys path obj ["cell", "path"]
  let cell ← match ← StrictJson.field path obj "cell" with
    | .num n =>
        match jsonInt? n with
        | some i => if i ≥ 0 then pure i.toNat else throw s!"{path}.cell: negative cell index {i}"
        | none => throw s!"{path}.cell: not an integer"
    | _ => throw s!"{path}.cell: expected a nat (the cell's index in the seed)"
  let elems ← StrictJson.array s!"{path}.path" (← StrictJson.field path obj "path")
  let p ← StrictJson.mapArrayIdx elems (fun i e => decodePathElem s!"{path}.path[{i}]" e)
  return .ref cell p.toList

/-- A seed value (§1 `SeedJson`); `fuel` bounds the nesting (the parse's own bound suffices). -/
def decodeSeedValue : Nat → String → Json → Except String SeedValue
  | 0, path, _ => .error s!"{path}: seed value nesting exceeds the parse bound (internal)"
  | fuel + 1, path, json =>
      match json with
      | .num n =>
          match jsonInt? n with
          | some i => .ok (.int i)
          | none => .error s!"{path}: a number with a fraction or exponent is not a seed value"
      | .bool b => .ok (.bool b)
      | .null => .error s!"{path}: null is not a seed value (a nil pointer is {"{"}\"nil\":true})"
      | .str _ => .error s!"{path}: a string is not a seed value in golean-seed-v1"
      | .arr xs => do
          let vs ← StrictJson.mapArrayIdx xs (fun i x => decodeSeedValue fuel s!"{path}[{i}]" x)
          return .array vs.toList
      | .obj kvs => do
          if kvs.contains "ref" || kvs.contains "nil" then
            -- An object with a `ref` or `nil` key IS that form (§1): anything else beside it is
            -- the v1 limit, named (review LOW-1), never a generic exact-keys text.
            if !(StrictJson.exactKeys kvs ["ref"] || StrictJson.exactKeys kvs ["nil"]) then
              throw s!"{path}: an object with a `ref` or `nil` key is the reference / nil form and carries nothing else (got keys {repr (StrictJson.keys kvs)}) — {refNilLimit}"
            if kvs.contains "ref" then
              decodeRefBody s!"{path}.ref" (← StrictJson.field path kvs "ref")
            else
              match ← StrictJson.field path kvs "nil" with
              | .bool true => return .nil
              | _ => throw s!"{path}.nil: expected true (a nil pointer is {"{"}\"nil\":true}) — {refNilLimit}"
          else
            let fs ← kvs.toList.mapM (fun (k, v) => do
              let w ← decodeSeedValue fuel s!"{path}.{k}" v
              pure (k, w))
            return .struct fs

/-! ## The file -/

/-- Decode a parsed seed file against the program's type table: the cells, in order. -/
def decodeSeedJson (types : TypeEnv) (json : Json) : Except String (Array SeedCell) := do
  let obj ← StrictJson.obj "seed" json
  StrictJson.requireExactKeys "seed" obj ["cells", "schema"]
  let schema ← StrictJson.string "seed.schema" (← StrictJson.field "seed" obj "schema")
  if schema != seedSchema then
    throw s!"seed.schema: expected {repr seedSchema}, got {repr schema}"
  let cells ← StrictJson.array "seed.cells" (← StrictJson.field "seed" obj "cells")
  StrictJson.mapArrayIdx cells (fun k cj => do
    let path := s!"seed.cells[{k}]"
    let cobj ← StrictJson.obj path cj
    StrictJson.requireExactKeys path cobj ["type", "value"]
    let spelling ← StrictJson.string s!"{path}.type" (← StrictJson.field path cobj "type")
    let typ ← (parseTypeSpelling types spelling (spelling.length + 1) spelling).mapError (s!"{path}.type: " ++ ·)
    let value ← decodeSeedValue (StrictJson.wireNestingDepth + 1) s!"{path}.value" (← StrictJson.field path cobj "value")
    pure ({ typ, value } : SeedCell))

/-- Decode a seed file from its BYTES: UTF-8 and the strict parse, the number pre-scan, then
the shape (exact keys, schema, cells) and the type spellings. Every refusal names its cause. -/
def decodeSeedBytes (types : TypeEnv) (bytes : ByteArray) : Except String (Array SeedCell) := do
  let json ← (StrictJson.parseBytes bytes StrictJson.wireNestingDepth).mapError (s!"JSON parse error: " ++ ·)
  -- The parse succeeded, so the bytes ARE UTF-8; the pre-scan reads the same text.
  let some text := String.fromUTF8? bytes | throw "JSON input is not valid UTF-8"
  if let some tok := badNumberToken text.toList false false none then
    if tok == "-0" then
      throw s!"number -0: a negative zero is not a golean-seed-v1 integer (write 0; the sign would be lost, and an unsigned kind refuses a sign)"
    throw s!"number {tok}: a fraction or exponent is not allowed in golean-seed-v1 (integers only)"
  decodeSeedJson types json

/-! ## `--arg-ref` -/

/-- Read the steps after the cell index: `.ident` / `[nat]`; `fuel` bounds the steps (the
spec's length suffices — every step consumes at least two chars). -/
def parseRefSteps : Nat → List Char → Option (List SeedPathElem)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, '.' :: cs =>
      let name := cs.takeWhile (fun c => c.isAlphanum || c == '_')
      if isIdent (String.ofList name) then
        (parseRefSteps fuel (cs.drop name.length)).map (.field (String.ofList name) :: ·)
      else none
  | fuel + 1, '[' :: cs =>
      let digits := cs.takeWhile Char.isDigit
      match cs.drop digits.length with
      | ']' :: rest =>
          match parseDecimalNat? (String.ofList digits) with
          | some i => (parseRefSteps fuel rest).map (.index i :: ·)
          | none => none
      | _ => none
  | _, _ => none

/-- `--arg-ref`'s grammar `k ( "." ident | "[" nat "]" )*` (§6): `0`, `0.next`, `1[2]`, `0.a[3].b`. -/
def parseArgRef (spec : String) : Except String (Nat × List SeedPathElem) :=
  let cs := spec.toList
  let digits := cs.takeWhile Char.isDigit
  match parseDecimalNat? (String.ofList digits), parseRefSteps (cs.length + 1) (cs.drop digits.length) with
  | some k, some steps => .ok (k, steps)
  | _, _ => .error s!"--arg-ref: malformed reference {spec} (expected k(.field|[i])*, e.g. 0, 0.next, 1[2], 0.a[3].b)"

end GoLean.SeedFile
