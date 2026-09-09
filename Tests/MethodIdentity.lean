import GoLean.GoCore.Ops
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

-- [AGENT] Full-identity satisfaction controls, independent of the frontend guard.
private def signature (id : Declaration.MemberId) (params : Array Ty := #[]) (variadic := false) : MethodSig :=
  { id, params, results := #[.int .int], variadic }

private def implementing (req : MethodSig) (recv : Ty := .defined 2) : ExecState :=
  let target : Func :=
    { id := ⟨"body"⟩,
      args := #[{ id := "$recv", typ := recv }] ++ req.params.map (fun t => { id := "arg", typ := t }),
      results := req.results.map (fun t => { id := "result", typ := t }),
      variadic := req.variadic, body := .unsupported "signature-only control" }
  { types := TypeEnv.reserved ++ #[(⟨"main.T"⟩, .struct #[])],
    functions := #[target],
    methods := #[{ id := req.id, funcId := ⟨"body"⟩, recv }],
    methodSets := #[{ key := "main.T", coverage := .full }],
    typeDisplays := #[(⟨"main.T"⟩, { name := "main.T", pkg := "main" })] }

private def privateP := signature ⟨"m", "red/inner"⟩
private def privateQ := signature ⟨"m", "blue/inner"⟩

theorem private_same_package_accepted :
    satisfiesMethodSig (implementing privateP) (.defined 2) privateP = true := by decide +kernel

theorem private_cross_package_rejected :
    satisfiesMethodSig (implementing privateP) (.defined 2) privateQ = false := by decide +kernel

theorem pointer_inherits_private_value :
    satisfiesMethodSig (implementing privateP) (.pointer (.defined 2)) privateP = true := by decide +kernel

theorem value_does_not_inherit_private_pointer :
    satisfiesMethodSig (implementing privateP (.pointer (.defined 2))) (.defined 2) privateP = false := by decide +kernel

theorem variadic_is_part_of_signature :
    satisfiesMethodSig (implementing (signature ⟨"m", "p"⟩ #[.slice (.int .int)] true))
      (.defined 2) (signature ⟨"m", "p"⟩ #[.slice (.int .int)] false) = false := by decide +kernel

private def satisfactionControls : IO Unit := do
  let ids : List Declaration.MemberId := [⟨"m", "red/inner"⟩, ⟨"m", "blue/inner"⟩,
    ⟨"M", ""⟩, ⟨"é", "red/inner"⟩, ⟨"é", "blue/inner"⟩, ⟨"É", ""⟩,
    ⟨"ǅ", "red/inner"⟩, ⟨"ǅ", "blue/inner"⟩, ⟨"𐐀", ""⟩]
  for a in ids do
    for b in ids do
      for pointerImpl in [false, true] do
        for pointerQuery in [false, true] do
          let recv := if pointerImpl then Ty.pointer (.defined 2) else .defined 2
          let dyn := if pointerQuery then Ty.pointer (.defined 2) else .defined 2
          for shape in [0:5] do
            let impl := signature a #[.slice (.int .int)] true
            let req := match shape with
              | 0 => signature b #[.slice (.int .int)] true
              | 1 => signature b #[.slice (.int .int)] false
              | 2 => signature b #[.slice .bool] true
              | 3 => { signature b #[.slice (.int .int)] true with results := #[.bool] }
              | _ => signature b #[] false
            let want := a == b && (!pointerImpl || pointerQuery) && shape == 0
            check (satisfiesMethodSig (implementing impl recv) dyn req == want)
              s!"identity/signature/receiver matrix: {repr a}/{repr b}/{pointerImpl}/{pointerQuery}/{shape}"
  -- Coverage and rendering both consume the same requirement record.
  for req in [privateQ, signature ⟨"É", ""⟩, signature ⟨"ǅ", "blue/inner"⟩] do
    let base := implementing privateP
    let withIface := { base with types := base.types ++ #[(⟨"main.I"⟩, .interfaceDef #[req])] }
    match firstUnsatisfiedMethod? withIface (.defined 2) ⟨"main.I"⟩ with
    | .ok name => check (name == some req.name) "missing-method display contains package identity"
    | .error e => throw (IO.userError s!"full coverage refused: {repr e}")
    let unknown := { withIface with methodSets := #[] }
    match firstUnsatisfiedMethod? unknown (.defined 2) ⟨"main.I"⟩ with
    | .error e => check (e.status == "unsupported") "absent coverage did not refuse"
    | .ok _ => throw (IO.userError "absent coverage answered from no record")
    let exportedOnly := { withIface with methodSets := #[{ key := "main.T", coverage := .exported }] }
    match firstUnsatisfiedMethod? exportedOnly (.defined 2) ⟨"main.I"⟩ with
    | .ok name => check (req.id.package.isEmpty && name == some req.name) "private exported-only query answered"
    | .error e => check (!req.id.package.isEmpty && e.status == "unsupported") "public Unicode requirement refused"
  IO.println "Method satisfaction: PASS; 1620 identity/signature/receiver cells; full/exported/absent coverage and bare display"

def main (args : List String) : IO Unit := do
  satisfactionControls
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
