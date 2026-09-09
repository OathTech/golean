import GoLean.NativeToIR
import GoLean.GoCore.SyntaxEqb

open Lean GoLean GoLean.GoCore

namespace GoLean.MethodIdentityTests

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def member (name pkg : String) : Json :=
  Json.mkObj [("name", .str name), ("package", .str pkg)]

private def requirement (id : Json) : Json :=
  Json.mkObj [("id", id), ("params", .arr #[]), ("results", .arr #[]),
    ("variadic", .bool false)]

private def method (id : Json) : Json :=
  Json.mkObj [("id", id), ("recvType", .str "main.T"),
    ("recv", Json.mkObj [("id", .str "$recv"),
      ("type", Json.mkObj [("kind", .str "named"), ("name", .str "main.T")])]),
    ("params", .arr #[]), ("results", .arr #[]), ("variadic", .bool false),
    ("unsupported", .str "identity-only test stub")]

private def program (requirements methods : Array Json) : Json :=
  Json.mkObj [("schema", .str "golean-native-v1"), ("funcs", .arr #[]),
    ("methods", .arr methods), ("methodSets", .arr #[]),
    ("types", .arr #[
      Json.mkObj [("name", .str "main.T"), ("display", .str "main.T"), ("pkg", .str "main"),
        ("def", Json.mkObj [("kind", .str "struct"), ("fields", .arr #[])])],
      Json.mkObj [("name", .str "main.I"), ("display", .str "main.I"), ("pkg", .str "main"),
        ("def", Json.mkObj [("kind", .str "interface"), ("methods", .arr requirements)])]])]

private def reject (wire : Json) (path reason : String) : IO Unit := do
  match NativeToIR.decodeProgram wire with
  | .ok _ => throw (IO.userError s!"accepted malformed identity: {wire.compress}")
  | .error message =>
    check ((message.splitOn path).length > 1 && (message.splitOn reason).length > 1)
      s!"wrong refusal; wanted {path} / {reason}, got {message}"

/-- Runtime record equality must retain the new field, before matching changes. -/
theorem requirement_identity_is_semantic :
    MethodSig.eqb ⟨⟨"m", "p"⟩, #[], #[], false⟩ ⟨⟨"m", "q"⟩, #[], #[], false⟩ = false := by
  decide +kernel

theorem method_identity_is_semantic :
    MethodInfo.eqb ⟨⟨"m", "p"⟩, ⟨"body"⟩, .int⟩ ⟨⟨"m", "q"⟩, ⟨"body"⟩, .int⟩ = false := by
  decide +kernel

def main (args : List String) : IO Unit := do
  let [fixture] := args | throw (IO.userError "expected fresh executable member fixture")
  let p ← IO.ofExcept (NativeToIR.decodeProgram (← IO.ofExcept
    (StrictJson.parseBytes (← IO.FS.readBinFile fixture))))
  for recv in ["main.T", "main.S", "main.I"] do
    for (name, pkg) in [("m", "main"), ("M", ""), ("é", "main"), ("É", ""),
        ("ǅ", "main"), ("𐐀", "")] do
      check (p.methods.any fun m => m.funcId.key == recv ++ "." ++ name &&
        m.id == Declaration.MemberId.mk name pkg) s!"lost checked identity {recv}.{pkg}:{name}"
  for (name, pkg) in [("M", ""), ("É", ""), ("Σ", ""), ("𐐀", ""),
      ("m", "red/inner"), ("é", "blue/inner"), ("ǅ", "main")] do
    let id := member name pkg
    check (NativeToIR.decodeProgram (program #[requirement id] #[method id])).isOk
      s!"valid executable identity refused: {id.compress}"
  for (id, reason) in [
      (member "m" "", "unexported member has no package identity"),
      (member "ǅ" "", "unexported member has no package identity"),
      (member "M" "p", "exported member carries a package identity"),
      (member "𐐀" "p", "exported member carries a package identity"),
      (member "" "p", "empty member name"),
      (Json.mkObj [("name", .str "m")], "package"),
      (Json.mkObj [("name", .str "m"), ("package", .num 4)], "String expected"),
      (Json.mkObj [("name", .num 4), ("package", .str "p")], "String expected"),
      (Json.mkObj [("name", .str "m"), ("package", .str "p"), ("pkg", .str "q")], "pkg")] do
    reject (program #[requirement id] #[]) "program.types[1].def.methods[0].id" reason
    reject (program #[] #[method id]) "program.methods[0].id" reason
  let id := member "m" "p"
  let oldReq := Json.mkObj [("name", .str "m"), ("params", .arr #[]),
    ("results", .arr #[]), ("variadic", .bool false)]
  reject (program #[oldReq] #[]) "program.types[1].def.methods[0]" "name"
  let withoutId := Json.mkObj [("params", .arr #[]), ("results", .arr #[]), ("variadic", .bool false)]
  reject (program #[withoutId] #[]) "program.types[1].def.methods[0]" "missing field 'id'"
  let methodObj ← IO.ofExcept ((method id).getObj?)
  let legacyMethod := Json.mkObj ((methodObj.toList.filter fun x => x.1 != "id") ++ [("name", .str "m")])
  reject (program #[] #[legacyMethod]) "program.methods[0]" "name"
  let missingMethod := Json.mkObj (methodObj.toList.filter fun x => x.1 != "id")
  reject (program #[] #[missingMethod]) "program.methods[0]" "missing field 'id'"
  let conflicting := Json.mkObj (methodObj.toList ++ [("name", .str "other")])
  reject (program #[] #[conflicting]) "program.methods[0]" "name"
  reject (program #[requirement id, requirement id] #[]) "program.types[1]" "duplicate interface member"
  check (NativeToIR.decodeProgram (program #[requirement id, requirement (member "m" "q")] #[])).isOk
    "distinct package requirements collapsed"
  IO.println "Method identity: PASS; fresh checked-object fixture, exact member schema, named malformed controls"

end GoLean.MethodIdentityTests

def main := GoLean.MethodIdentityTests.main
