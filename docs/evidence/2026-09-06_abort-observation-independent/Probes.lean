import Tests.AbortObservationAudit

namespace AbortObserverIndependent
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.GoCore.RecoveryRuntime
open GoLean.Semantics

set_option maxRecDepth 16384

theorem whole_record_is_nonempty (record : AbortRecord) : record.chain ≠ [] := by
  simp [AbortRecord.chain]

theorem record_needs_positive_budget {fuel m r ch out result record}
    (h : execPoolWithAbort fuel m r ch out = (result, some record)) : 0 < fuel := by
  obtain ⟨spent, remaining, _, _, _, _, _, _, _, _, _, _, _, budget, _⟩ :=
    (execPoolWithAbort_witness h).reached
  omega

theorem record_cannot_advertise_success {fuel m r ch out final values record}
    (h : execPoolWithAbort fuel m r ch out = ((final, .ok values), some record)) : False := by
  obtain ⟨_, _, impossible⟩ := (execPoolWithAbort_witness h).panic_result
  cases impossible

theorem detector_failure_discards_metadata {fuel m r ch out next after residual event refusal}
    (front : Pool.front m ch = .ok (.inr next))
    (step : stepMulti m next = .ok (after, residual, event))
    (race : raceUpdate m.shared m.threads event after r = .error refusal) :
    execPoolWithAbort (fuel + 1) m r ch out = ((out, .error refusal), none) := by
  simp [execPoolWithAbort, front, step, race]

def integerHead : PanicEntry := ⟨.interface (.int .int) (.int 5), false⟩
def integerPool : MultiConfig :=
  ⟨#[.running (.panicking [integerHead] .stop) none], {types := TypeEnv.reserved}, 0⟩

theorem same_rendering_does_not_prove_string_kind :
    execPoolWithAbort 1 integerPool {} [] GoString.empty =
      ((GoString.empty, .error (.panic "5")), none) := by
  with_unfolding_all rfl

def bytes : GoString := ⟨#[255, 0, 10, 65]⟩
def printed : Program := {funcs := #[{
  id := ⟨"run"⟩, args := #[], results := #[], body := .seqn #[
    .print false #[.stringLit bytes],
    .panicStmt (.toInterface (.interface ⟨"any"⟩) .string
      (.stringLit (GoString.fromLeanString "head"))) ] }]}

theorem actual_print_event_keeps_all_bytes :
    runProgramPoolWithAbort 24 printed "run" #[] [7,3,11] =
      (.error (.panic "head", bytes), some ⟨GoString.fromLeanString "head", false, []⟩) := by
  with_unfolding_all rfl

theorem actual_print_result_has_exact_driver_witness :
    ∃ c s locs initial,
      runProgramSetupM 24 printed "run" #[] [7,3,11] = .ok (c,s,locs,initial) ∧
      PoolAbortWitness 24 ⟨#[.running c none],s,0⟩ {} initial GoString.empty
        (bytes, .error (.panic "head")) ⟨GoString.fromLeanString "head",false,[]⟩ := by
  obtain ⟨c,s,locs,initial,out,message,setup,witness,result⟩ :=
    runProgramPoolWithAbort_witness actual_print_event_keeps_all_bytes
  cases result
  exact ⟨c,s,locs,initial,setup,witness⟩

def mixed : List PanicEntry :=
  [⟨.interface .string (.string (GoString.fromLeanString "5")), false⟩, integerHead]

theorem actual_nonstring_tail_remains_unrecorded :
    execPoolWithAbort 1
      ⟨#[.running (.panicking mixed .stop) none], {types := TypeEnv.reserved}, 0⟩ {} [] bytes =
      ((bytes, .error (.panic "5")), none) := by
  with_unfolding_all rfl

theorem sequential_normal_frontier_precedes_zero_fuel (s : ExecState) (ch : Choices) :
    runConfigWithAbort 0 s (.next .stop) ch = (.ok (s,ch),none) := rfl

theorem missing_main_is_refusal_without_metadata (s : ExecState) (ch : Choices) :
    execPoolWithAbort 0 ⟨#[],s,0⟩ {} ch bytes =
      ((bytes,.error (.internal "thread pool without a main goroutine")),none) := by
  simp [execPoolWithAbort, Pool.front]

end AbortObserverIndependent

#eval AbortObservationAudit.run
