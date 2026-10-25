import GoLean.ChoiceTrace
import GoLean.GoCore.Ops
import GoLean.NativeToIR
import GoLean.GoCore.SyntaxEqb

/-! Package-correct method identity (I1): the twelve theorems below and the two in-memory controls
(`satisfactionControls`, `receiverControls`) are BUILD-TIME checks — each control is an `#eval` of an
`IO` action that throws on the first failed cell, so a failure fails this module's elaboration (the
build, `lake check`, the gate) and a pass logs the control's PASS line into the build output, which
`scripts/check-method-identity` reads (fresh or replayed from Lake's saved log). No top-level `main`
since 2026-10-25 (lane `gate/contract-pins-1025`, release-readiness row 42's follow-up): the library
`MethodIdentityTests` is a DEFAULT target, so `lake check` exports and kernel-replays the theorems.
The one check that cannot run at build time — the FRESH executable member wire produced by the
frontend's own Go tests, read by the strict decoder — is `Tests/MethodIdentityFixture.lean` (library
`MethodIdentityFixtureTests`, built by name, run by `lean --run` with the fixture path), which imports
this module for the wire-building helpers `member`/`requirement`/`method`/`program`/`reject`/`check`. -/

open Lean GoLean GoLean.GoCore

namespace GoLean.MethodIdentityTests
/-- B6 (2026-09-30): a spelling interned injectively into a `VarId` (test-local). -/
def vid (s : String) : GoLean.GoCore.VarId := s.toUTF8.foldl (fun n b => n * 256 + b.toNat) 0

def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def member (name pkg : String) : Json :=
  Json.mkObj [("name", .str name), ("package", .str pkg)]

def requirement (id : Json) : Json :=
  Json.mkObj [("id", id), ("params", .arr #[]), ("results", .arr #[]),
    ("variadic", .bool false)]

def method (id : Json) : Json :=
  Json.mkObj [("id", id), ("recvType", .str "main.T"),
    ("recv", Json.mkObj [("id", .str "$recv"),
      ("type", Json.mkObj [("kind", .str "named"), ("name", .str "main.T")])]),
    ("params", .arr #[]), ("results", .arr #[]), ("variadic", .bool false), ("locals", .arr #[]),
    ("unsupported", .str "identity-only test stub")]

def program (requirements methods : Array Json) : Json :=
  Json.mkObj [("schema", .str "golean-native-v3"), ("funcs", .arr #[]),
    ("buildContext", Json.mkObj [("goos", .str "linux"), ("goarch", .str "amd64"),
      ("compiler", .str "gc"), ("cgoEnabled", .bool true), ("buildTags", .arr #[])]),
    ("methods", .arr methods), ("methodSets", .arr #[]), ("promotions", .arr #[]),
    ("types", .arr #[
      Json.mkObj [("name", .str "main.T"), ("display", .str "main.T"), ("pkg", .str "main"),
        ("def", Json.mkObj [("kind", .str "struct"), ("fields", .arr #[])])],
      Json.mkObj [("name", .str "main.I"), ("display", .str "main.I"), ("pkg", .str "main"),
        ("def", Json.mkObj [("kind", .str "interface"), ("methods", .arr requirements)])]])]

def reject (wire : Json) (path reason : String) : IO Unit := do
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

private def implementing (req : MethodSig) (recv : Ty := .defined 2) : ProgramCtx :=
  let target : Func :=
    { id := ⟨"body"⟩,
      args := #[{ id := vid "$recv", typ := recv }] ++ req.params.map (fun t => { id := vid "arg", typ := t }),
      results := req.results.map (fun t => { id := vid "result", typ := t }),
      variadic := req.variadic, body := .unsupported "signature-only control" }
  ProgramCtx.ofTables
    (types := TypeEnv.reserved ++ #[(⟨"main.T"⟩, .struct #[])])
    (functions := #[target])
    (methods := #[{ id := req.id, funcId := ⟨"body"⟩, recv }])
    (methodSets := #[{ key := "main.T", coverage := .full }])
    (typeDisplays := #[(⟨"main.T"⟩, { name := "main.T", pkg := "main" })])

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
-- another package's declaration, or invent a target from its bare spelling.
-- G-P S2 (2026-09-28): the retired «not a synthesized wrapper» invariant is
-- «the resolution path is empty» — a PROMOTED entry (a record, no
-- declaration on the pointee) is outside the BUG-087 family.
private def nilTextState (members : Array MethodInfo) (promotions : Array Promotion := #[]) :
    ProgramCtx :=
  let target := fun (id : String) (recv : Ty) =>
    ({ id := ⟨id⟩, args := #[{ id := vid "$recv", typ := recv }], results := #[],
       body := .unsupported "validator-only control" } : Func)
  ProgramCtx.ofTables
    (types := TypeEnv.reserved ++ #[(⟨"main.T"⟩, .struct #[{ name := "e", typ := .defined 2, embedded := true }])])
    (functions := #[target "anchor" (.interface ⟨"main.I"⟩),
      target "plain" (.defined 2), target "other" (.defined 2)])
    (methods := #[{ id := privateP.id, funcId := ⟨"anchor"⟩, recv := .interface ⟨"main.I"⟩ }] ++ members)
    (promotions := promotions)

private def nilTextChecks (members : Array MethodInfo) (promotions : Array Promotion := #[]) :
    List Bool :=
  (ChoiceTrace.nilTextFacts (nilTextState members promotions) ⟨"anchor"⟩
    [.interface (.pointer (.defined 2)) .nil]).invariants.map Prod.snd

private def nilTarget (id : Declaration.MemberId) (body : String) : MethodInfo :=
  { id, funcId := ⟨body⟩, recv := .defined 2 }

/-- A PROMOTED `privateP` on `main.T` (one value hop, targeting `plain`). -/
private def promotedP : Promotion :=
  { type := ⟨"main.T"⟩, member := privateP.id, inPtrSetOnly := false,
    path := #[{ owner := ⟨"main.T"⟩, field := "e", ptr := false }], adjust := .asIs,
    target := .method ⟨"plain"⟩ }

theorem nil_text_ignores_foreign_declaration :
    nilTextChecks #[nilTarget privateQ.id "other", nilTarget privateP.id "plain"] =
      [true, true, true, true] := by decide +kernel

theorem nil_text_promoted_entry_outside_family :
    nilTextChecks #[nilTarget privateQ.id "plain"] #[promotedP] =
      [true, true, false, false] := by decide +kernel

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
    let withIface : ProgramCtx :=
      ⟨{ base.program with typeDefs := base.types ++ #[(⟨"main.I"⟩, .interfaceDef #[req])] }⟩
    match firstUnsatisfiedMethod? withIface (.defined 2) ⟨"main.I"⟩ with
    | .ok name => check (name == some req.name) "missing-method display contains package identity"
    | .error e => throw (IO.userError s!"full coverage refused: {repr e}")
    let unknown : ProgramCtx := ⟨{ withIface.program with methodSets := #[] }⟩
    match firstUnsatisfiedMethod? unknown (.defined 2) ⟨"main.I"⟩ with
    | .error e => check (e.status == "unsupported") "absent coverage did not refuse"
    | .ok _ => throw (IO.userError "absent coverage answered from no record")
    let exportedOnly : ProgramCtx :=
      ⟨{ withIface.program with methodSets := #[{ key := "main.T", coverage := .exported }] }⟩
    match firstUnsatisfiedMethod? exportedOnly (.defined 2) ⟨"main.I"⟩ with
    | .ok name => check (req.id.package.isEmpty && name == some req.name) "private exported-only query answered"
    | .error e =>
        check (!req.id.package.isEmpty && e.status == "unsupported") "public Unicode requirement refused"
        check (e.message == s!"interface satisfaction for main.T: requirement {req.name} is UNEXPORTED and the dynamic type's record covers exported methods only — this record cannot decide whether the private requirement is satisfied")
          "exported-only refusal does not describe the record's coverage limit"
  IO.println "Method satisfaction: PASS; 1620 identity/signature/receiver cells; full/exported/absent coverage and bare display"

-- Build-time: a failed cell throws, which fails this module's elaboration; the PASS line lands in
-- the build output for scripts/check-method-identity.
#eval satisfactionControls

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

#eval receiverControls

end GoLean.MethodIdentityTests
