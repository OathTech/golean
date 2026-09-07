import GoLean.GoCore.RecoveryPoolObservation
import GoLean.GoCore.RecoveryAdmission

/-! CLI-consumable observation of the actual program driver. The untyped
wrapper makes no admission claim; the checked wrapper runs the independent
profile checker. Both preserve the shipped result exactly. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine RecoveryTyping
open GoLean.Semantics

def runProgramPoolWithAbort (fuel : Nat) (p : Program) (name : String)
    (args : Array GoValue) (ch : Choices := []) : RunResult × Option AbortRecord :=
  match runProgramSetupM fuel p name args ch with
  | .error e => (.error (e, GoString.empty), none)
  | .ok (c, s, locs, initial) =>
    let observed := execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ {} initial GoString.empty
    match observed.1.2 with
    | .error e => (.error (e, observed.1.1), observed.2)
    | .ok (final, _) => match loadMany final locs with
      | .error e => (.error (e, observed.1.1), none)
      | .ok values => (.ok {values := values.toArray, output := observed.1.1}, none)

def runProgramPoolWithAbortInts (fuel : Nat) (p : Program) (name : String)
    (args : Array Int) (ch : Choices := []) : RunResult × Option AbortRecord :=
  runProgramPoolWithAbort fuel p name (args.map GoValue.int) ch

def checkedRunProgramPoolWithAbort (fuel : Nat) (p : Program) (name : String)
    (args : Array GoValue) (ch : Choices := []) :
    Except Error (RunResult × Option AbortRecord) := do
  checkRecovery p name args
  return runProgramPoolWithAbort fuel p name args ch

def checkedRunProgramPoolWithAbortInts (fuel : Nat) (p : Program) (name : String)
    (args : Array Int) (ch : Choices := []) : Except Error (RunResult × Option AbortRecord) :=
  checkedRunProgramPoolWithAbort fuel p name (args.map GoValue.int) ch

theorem runProgramPoolWithAbort_erasure (fuel : Nat) (p : Program) (name : String)
    (args : Array GoValue) (ch : Choices) :
    (runProgramPoolWithAbort fuel p name args ch).1 = runProgramPoolOutM fuel p name args ch := by
  unfold runProgramPoolWithAbort runProgramPoolOutM
  cases hs : runProgramSetupM fuel p name args ch with
  | error e => rfl
  | ok setup =>
    obtain ⟨c, s, locs, initial⟩ := setup
    dsimp only
    generalize hr : execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ {} initial GoString.empty = observed
    obtain ⟨⟨out, result⟩, metadata⟩ := observed
    have he := execPoolWithAbort_erasure fuel ⟨#[.running c none], s, 0⟩ {} initial GoString.empty
    rw [hr] at he
    rw [← he]
    cases result with
    | error e => rfl
    | ok final =>
      obtain ⟨s', ch'⟩ := final
      dsimp only
      cases loadMany s' locs <;> rfl

/-- Exactly the existing native-json integer-argument entry, with no implicit
integer-to-Boolean conversion or change to empty-argument behavior. -/
theorem runProgramPoolWithAbortInts_erasure (fuel : Nat) (p : Program) (name : String)
    (args : Array Int) (ch : Choices) :
    (runProgramPoolWithAbortInts fuel p name args ch).1 =
      runProgramPoolOutIntsM fuel p name args ch :=
  runProgramPoolWithAbort_erasure fuel p name (args.map GoValue.int) ch

theorem checkedRunProgramPoolWithAbort_admitted {fuel p name args ch}
    (admitted : RecoveryAdmission p name args) :
    checkedRunProgramPoolWithAbort fuel p name args ch =
      .ok (runProgramPoolWithAbort fuel p name args ch) := by
  simp [checkedRunProgramPoolWithAbort, checkRecovery_complete admitted, Bind.bind, Except.bind]

theorem checkedRunProgramPoolWithAbort_sound {fuel p name args ch observed}
    (h : checkedRunProgramPoolWithAbort fuel p name args ch = .ok observed) :
    RecoveryAdmission p name args ∧ observed.1 = runProgramPoolOutM fuel p name args ch := by
  unfold checkedRunProgramPoolWithAbort at h
  rw [bind_eq_ok] at h
  obtain ⟨u, admitted, h⟩ := h
  cases u
  cases h
  exact ⟨checkRecovery_sound admitted, runProgramPoolWithAbort_erasure fuel p name args ch⟩

/-- Computed metadata is tied to the actual setup and an actual pool-driver
abort witness at the same fuel, source arguments and initial choice stream.
The witness records detector checks and exact accumulated output. -/
theorem runProgramPoolWithAbort_witness {fuel p name args ch result record}
    (h : runProgramPoolWithAbort fuel p name args ch = (result, some record)) :
    ∃ (c : Config) (s : ExecState) (locs : List Loc) (initial : Choices)
      (out : GoString) (message : String),
      runProgramSetupM fuel p name args ch = .ok (c, s, locs, initial) ∧
      PoolAbortWitness fuel ⟨#[.running c none], s, 0⟩ {} initial GoString.empty
        (out, .error (.panic message)) record ∧ result = .error (.panic message, out) := by
  unfold runProgramPoolWithAbort at h
  cases hs : runProgramSetupM fuel p name args ch with
  | error e => simp [hs] at h
  | ok setup =>
    obtain ⟨c, s, locs, initial⟩ := setup
    simp only [hs] at h
    generalize hr : execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ {} initial GoString.empty = observed at h
    obtain ⟨⟨out, actual⟩, metadata⟩ := observed
    cases actual with
    | ok final =>
      obtain ⟨s', ch'⟩ := final
      cases hl : loadMany s' locs <;> simp [hl] at h
    | error e =>
      have he : (.error (e, out) : RunResult) = result ∧ metadata = some record := by simpa using h
      obtain ⟨rfl, rfl⟩ := he
      have witness := execPoolWithAbort_witness hr
      obtain ⟨finalOut, message, hresult⟩ := witness.panic_result
      obtain ⟨rfl, he⟩ := Prod.mk.inj hresult
      cases he
      exact ⟨c, s, locs, initial, out, message, rfl, witness, rfl⟩

end GoLean.GoCore.RecoveryRuntime
