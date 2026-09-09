import GoLean.ChoiceTrace
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

-- [AGENT] Audit R1: the independent nil-text validator must not borrow
-- another package's wrapper bit, or invent a target from its bare spelling.
private def nilTextState (members : Array MethodInfo) : ExecState :=
  let target := fun (id : String) (recv : Ty) (wrapper : Bool) =>
    ({ id := ⟨id⟩, args := #[{ id := "$recv", typ := recv }], results := #[],
       body := .unsupported "validator-only control", wrapper } : Func)
  { types := TypeEnv.reserved ++ #[(⟨"main.T"⟩, .struct #[])],
    functions := #[target "anchor" (.interface ⟨"main.I"⟩) false,
      target "plain" (.defined 2) false, target "wrapper" (.defined 2) true],
    methods := #[{ id := privateP.id, funcId := ⟨"anchor"⟩, recv := .interface ⟨"main.I"⟩ }] ++ members }

private def nilTextChecks (members : Array MethodInfo) : List Bool :=
  (ChoiceTrace.nilTextFacts (nilTextState members) ⟨"anchor"⟩
    [.interface (.pointer (.defined 2)) .nil]).invariants.map Prod.snd

private def nilTarget (id : Declaration.MemberId) (body : String) : MethodInfo :=
  { id, funcId := ⟨body⟩, recv := .defined 2 }

theorem nil_text_ignores_foreign_wrapper :
    nilTextChecks #[nilTarget privateQ.id "wrapper", nilTarget privateP.id "plain"] =
      [true, true, true, true] := by decide +kernel

theorem nil_text_does_not_borrow_foreign_body :
    nilTextChecks #[nilTarget privateQ.id "plain", nilTarget privateP.id "wrapper"] =
      [true, true, true, false] := by decide +kernel

theorem nil_text_requires_matching_package :
    nilTextChecks #[nilTarget privateQ.id "plain"] =
      [true, true, false, false] := by decide +kernel

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
    | .error e =>
        check (!req.id.package.isEmpty && e.status == "unsupported") "public Unicode requirement refused"
        check (e.message == s!"interface satisfaction for main.T: requirement {req.name} is UNEXPORTED and the dynamic type's record covers exported methods only — this record cannot decide whether the private requirement is satisfied")
          "exported-only refusal does not describe the record's coverage limit"
  IO.println "Method satisfaction: PASS; 1620 identity/signature/receiver cells; full/exported/absent coverage and bare display"

theorem private_targets_are_distinct :
    methodFuncId "main.Mix" ⟨"m", "red/inner"⟩ ≠
      methodFuncId "main.Mix" ⟨"m", "blue/inner"⟩ := by decide +kernel

theorem utf8_target_vector :
    (methodFuncId "main.Δ" ⟨"é", "p"⟩).key = "$method$7:main.Δ1:pé" := by decide +kernel

private def receiverControls : IO Unit := do
  let named := fun name => Json.mkObj [("kind", .str "named"), ("name", .str name)]
  let pointer := fun elem => Json.mkObj [("kind", .str "pointer"), ("elem", elem)]
  let iface := fun name => Json.mkObj [("kind", .str "interface"), ("name", .str name)]
  let sync := Json.mkObj [("kind", .str "sync"), ("sync", .str "Mutex")]
  let receiverMethod := fun key ty => do
    let obj ← (method (member "M" "")).getObj?
    return Json.mkObj ((obj.toList.filter fun x => x.1 != "recv" && x.1 != "recvType") ++
      [("recvType", .str key), ("recv", Json.mkObj [("id", .str "$recv"), ("type", ty)])])
  for (key, ty) in [("main.T", named "main.T"), ("main.T", pointer (named "main.T")),
      ("main.I", iface "main.I"), ("sync.Mutex", sync), ("sync.Mutex", pointer sync)] do
    let m ← IO.ofExcept (receiverMethod key ty)
    check (NativeToIR.decodeProgram (program #[] #[m])).isOk "valid receiver identity refused"
  for (key, ty) in [("main.I", named "main.T"), ("main.T", named "main.I"),
      ("main.T", iface "main.I"), ("main.I", pointer (iface "main.I")),
      ("sync.Once", sync), ("sync.Once", pointer sync),
      ("main.T", pointer (pointer (named "main.T")))] do
    let m ← IO.ofExcept (receiverMethod key ty)
    reject (program #[] #[m]) "program.methods[0].recvType / program.methods[0].recv.type"
      "method receiver identity disagrees"
  reject (program #[] #[method (member "m" "p"), method (member "m" "p")])
    "duplicate function id" "$method$6:main.T1:pm"
  check (NativeToIR.decodeProgram
    (program #[] #[method (member "m" "p"), method (member "m" "q")])).isOk
    "distinct promoted function ids collided"
  IO.println "Method targets: PASS; UTF-8 key vector, receiver agreement, duplicate target control"

def main (args : List String) : IO Unit := do
  satisfactionControls
  receiverControls
  let [fixture] := args | throw (IO.userError "expected fresh executable member fixture")
  let p ← IO.ofExcept (NativeToIR.decodeProgram (← IO.ofExcept
    (StrictJson.parseBytes (← IO.FS.readBinFile fixture))))
  for recv in ["main.T", "main.S", "main.I"] do
    for (name, pkg) in [("m", "main"), ("M", ""), ("é", "main"), ("É", ""),
        ("ǅ", "main"), ("𐐀", "")] do
      check (p.methods.any fun m => m.funcId == methodFuncId recv ⟨name, pkg⟩ &&
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
