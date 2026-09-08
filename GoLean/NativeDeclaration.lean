import GoLean.StrictJsonParse
import GoLean.GoCore.Declaration
import GoLean.DeclarationUnicode

/-! I1 declaration-wire decoding, separate from executable lowering.

This consumes already parsed JSON objects and checks their exact schema.
It does not validate source-level Go typing, authorize executable demand, or
provide missing layouts/bodies. `decodeBytes` rejects raw duplicate keys and
malformed Unicode before parsing; `decode` alone consumes an already parsed
`Json` object, which has already lost duplicate-key information.
The production emitter and NativeToIR do not yet use this separate channel.
-/
namespace GoLean.NativeDeclaration

open Lean GoLean.GoCore.Declaration
open GoLean.StrictJson

private def stringField (path : String) (o : Obj) (key : String) : Except String String := do
  string (path ++ "." ++ key) (← field path o key)

private def boolField (path : String) (o : Obj) (key : String) : Except String Bool := do
  bool (path ++ "." ++ key) (← field path o key)

private def basic (path name : String) : Except String Basic :=
  match name with
  | "bool" => .ok .boolean
  | "string" => .ok .string
  | "int" => .ok .int
  | "int8" => .ok .int8
  | "int16" => .ok .int16
  | "int32" => .ok .int32
  | "int64" => .ok .int64
  | "uint" => .ok .uint
  | "uint8" => .ok .uint8
  | "uint16" => .ok .uint16
  | "uint32" => .ok .uint32
  | "uint64" => .ok .uint64
  | "uintptr" => .ok .uintptr
  | "float32" => .ok (.float .float32)
  | "float64" => .ok (.float .float64)
  | "complex64" => .ok .complex64
  | "complex128" => .ok .complex128
  | "unsafe.Pointer" => .ok .unsafePointer
  | _ => .error s!"{path}: unknown closed declaration basic '{name}'"

private def memberId (path : String) (json : Json) : Except String MemberId := do
  let o ← obj path json
  requireExactKeys path o ["name", "package"]
  let name ← stringField path o "name"
  let some first := name.toList.head? | throw s!"{path}: empty member name"
  let pkg ← stringField path o "package"
  if DeclarationUnicode.isUpperCode first.toNat then
    unless pkg.isEmpty do throw s!"{path}: exported member carries a package identity"
  else
    if pkg.isEmpty then throw s!"{path}: unexported member has no package identity"
  return ⟨name, pkg⟩

private def bytes (path : String) (json : Json) : Except String (Array UInt8) := do
  mapArrayIdx (← array path json) fun i value => do
    let n ← nat s!"{path}[{i}]" value
    if n < 256 then return UInt8.ofNat n
    else throw s!"{path}[{i}]: byte outside [0,255]"

private def checkVariadic (path : String) (params : List Ty) (variadic : Bool) :
    Except String Unit := do
  if variadic then
    match params.getLast? with
    | some (.slice _) => pure ()
    | _ => throw s!"{path}: variadic signature needs a final slice parameter"

private def methodId : Method → MemberId
  | .mk id _ _ _ => id

private def uniqueFields (path : String) (fields : Array Field) : Except String Unit := do
  let mut seen : List MemberId := []
  for .mk id _ _ _ in fields do
    -- Go allows repeated blank fields; retain their order and type/tag facts.
    if id.name != "_" then
      if seen.contains id then throw s!"{path}: duplicate struct field '{id.name}'"
      seen := id :: seen

/-- Method-set order is semantically irrelevant. Normalize by the exact
package/name pair; do not depend on Go emitter enumeration order. -/
private def canonicalMethods (path : String) (methods : List Method) :
    Except String (List Method) := do
  let mut seen : List MemberId := []
  for method in methods do
    let id := methodId method
    if seen.contains id then throw s!"{path}: duplicate interface method '{id.name}'"
    seen := id :: seen
  return methods.mergeSort fun a b =>
    let i := methodId a
    let j := methodId b
    if i.package == j.package then i.name ≤ j.name else i.package ≤ j.package

/-- The separate nominal inventory supplies declaration arity, without a
layout or executable support flag. The enclosing package must supply the
complete inventory from its checked source declaration envelope. -/
abbrev Nominals := List (TypeId × Nat)

private def nominalArity (ns : Nominals) (id : TypeId) : Option Nat :=
  (ns.find? fun item => item.1 == id).map Prod.snd

private def checkNominals (ns : Nominals) : Except String Unit := do
  let mut seen : List TypeId := []
  for (id, _) in ns do
    if id.key.isEmpty then throw "declarations: empty nominal identity"
    if seen.contains id then throw s!"declarations: duplicate nominal identity '{id.key}'"
    seen := id :: seen

/- Like NativeToIR's existing JSON descent, this adapter is outside the
total semantic core. The resulting declaration operations are total and
their equality is kernel-checked in GoCore.Declaration. -/
private partial def decodeType (remaining : Nat) (ns : Nominals) (path : String) (json : Json) :
    Except String Ty := do
  let remaining + 1 := remaining
    | throw s!"{path}: declaration nesting deeper than {maxNestingDepth}"
  let o ← obj path json
  let kind ← stringField path o "kind"
  let listField := fun key => do
    let values ← array (path ++ "." ++ key) (← field path o key)
    return (← mapArrayIdx values fun i value =>
      decodeType remaining ns s!"{path}.{key}[{i}]" value).toList
  let elem := fun key => do decodeType remaining ns (path ++ "." ++ key) (← field path o key)
  match kind with
  | "basic" =>
      requireExactKeys path o ["kind", "basic"]
      return .basic (← basic (path ++ ".basic") (← stringField path o "basic"))
  | "named" =>
      requireExactKeys path o ["kind", "id", "args"]
      let id : TypeId := ⟨← stringField path o "id"⟩
      let some arity := nominalArity ns id
        | throw s!"{path}: unknown nominal declaration '{id.key}'"
      let args ← listField "args"
      if args.length != arity then
        throw s!"{path}: nominal '{id.key}' expects {arity} arguments, got {args.length}"
      return .named id args
  | "pointer" | "slice" =>
      requireExactKeys path o ["kind", "elem"]
      let value ← elem "elem"
      return if kind == "pointer" then .pointer value else .slice value
  | "array" =>
      requireExactKeys path o ["kind", "len", "elem"]
      return .array (← nat (path ++ ".len") (← field path o "len")) (← elem "elem")
  | "map" =>
      requireExactKeys path o ["kind", "key", "elem"]
      return .map (← elem "key") (← elem "elem")
  | "chan" =>
      requireExactKeys path o ["kind", "direction", "elem"]
      let direction ← stringField path o "direction"
      let dir ← match direction with
        | "both" => pure GoCore.ChanDir.both
        | "send" => pure GoCore.ChanDir.send
        | "recv" => pure GoCore.ChanDir.recv
        | _ => throw s!"{path}: unknown channel direction '{direction}'"
      return .chan dir (← elem "elem")
  | "func" =>
      requireExactKeys path o ["kind", "params", "results", "variadic"]
      let params ← listField "params"
      let results ← listField "results"
      let variadic ← boolField path o "variadic"
      checkVariadic path params variadic
      return .function params results variadic
  | "struct" =>
      requireExactKeys path o ["kind", "fields"]
      let values ← array (path ++ ".fields") (← field path o "fields")
      let fields ← mapArrayIdx values fun i value => do
        let fp := s!"{path}.fields[{i}]"
        let fo ← obj fp value
        requireExactKeys fp fo ["id", "type", "embedded", "tagBytes"]
        return Field.mk (← memberId (fp ++ ".id") (← field fp fo "id"))
          (← decodeType remaining ns (fp ++ ".type") (← field fp fo "type"))
          (← boolField fp fo "embedded")
          (← bytes (fp ++ ".tagBytes") (← field fp fo "tagBytes"))
      uniqueFields (path ++ ".fields") fields
      return .structureType fields.toList
  | "interface" =>
      requireExactKeys path o ["kind", "methods"]
      let values ← array (path ++ ".methods") (← field path o "methods")
      let methods ← mapArrayIdx values fun i value => do
        let mp := s!"{path}.methods[{i}]"
        let mo ← obj mp value
        requireExactKeys mp mo ["id", "signature"]
        let id ← memberId (mp ++ ".id") (← field mp mo "id")
        let sig ← decodeType remaining ns (mp ++ ".signature") (← field mp mo "signature")
        match sig with
        | .function ps rs v => return Method.mk id ps rs v
        | _ => throw s!"{mp}: method signature is not a function"
      return .interfaceType (← canonicalMethods path methods.toList)
  | _ => throw s!"{path}: unknown declaration type kind '{kind}'"

/-- Decode the positive schema against an explicit nominal inventory.
This is declaration parsing; it supplies no executable admission evidence. -/
def decode (ns : Nominals) (json : Json) : Except String Ty := do
  checkNominals ns
  decodeType maxNestingDepth ns "declaration" json

/-- A standalone positive declaration's checked byte-input boundary.
Package envelopes must use the same strict parser before projecting fields.
This still supplies no source-typing, layout or executable admission fact. -/
def decodeBytes (ns : Nominals) (input : ByteArray) : Except String Ty := do
  decode ns (← GoLean.StrictJson.parseBytes input)

end GoLean.NativeDeclaration
