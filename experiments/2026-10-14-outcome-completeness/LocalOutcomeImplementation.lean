import LocalOutcomeBridge
import OperationFailureSound

namespace GoLean.GoCore.Relational.C1
open Machine

/-- Ordinary operation failure, with records derived by the check structure
at the supplied control and store. It contains no driver or choice tape. -/
def ordinaryFailure : OperationFailure := fun ctx a records cause =>
  OperationCheck.Rejects (FailureChecks.atState ctx a) records cause.stop

namespace Correspondence
open ExecutionStatement OperationCheck.Correspondence FailureChecks.Correspondence

theorem ordinary_failure_coverage : OperationCoverage ordinaryFailure := by
  intro ctx a ch cause hz ha he
  have hb := blockedB_of_not_zeroCost (fun h => hz (Boundary.zero_cost_iff.mpr h))
  have hh : (run (FailureChecks.atState ctx a) ch).1 = some cause.stop := by
    rw [atState_errors ctx a.store a.control ch ha hb, he]
    rfl
  obtain ⟨hf, hr⟩ := run_coverage _ _ hh
  exact ⟨_, _, hf, hr⟩

theorem rejected_no_abort {ctx : ProgramCtx} {a : State} {records : List PickRecord}
    {cause : FailureCause} (h : ordinaryFailure ctx a records cause) : a.control.abort? = none := by
  cases ha : a.control.abort? with
  | none => rfl
  | some pair =>
    obtain ⟨first, rest⟩ := pair
    obtain ⟨hc, _⟩ := abort?_some ha
    unfold ordinaryFailure FailureChecks.atState at h
    rw [hc] at h
    cases h

theorem rejected_not_blocked {ctx : ProgramCtx} {a : State} {records : List PickRecord}
    {cause : FailureCause} (h : ordinaryFailure ctx a records cause) : a.control.blockedB = false := by
  obtain ⟨c, s⟩ := a
  cases c <;> first | rfl | cases h

theorem ordinary_failure_replay : OperationReplay ordinaryFailure := by
  intro ctx a records cause h ch tail hr
  have hx := OperationCheck.Correspondence.replay h hr
  rw [atState_errors ctx a.store a.control ch (rejected_no_abort h) (rejected_not_blocked h)] at hx
  cases he : stepFn ctx a.store a.control ch <;> simp_all [error?]

theorem ordinary_failure_selections : OperationSelections ordinaryFailure := by
  intro ctx a records cause h tail
  exact OperationCheck.Correspondence.selections h tail

theorem main_coverage : Coverage ordinaryFailure .main :=
  main_coverage_of_operation ordinaryFailure ordinary_failure_coverage

theorem main_realization : Realization ordinaryFailure .main :=
  main_realization_of_operation ordinaryFailure ordinary_failure_replay ordinary_failure_selections

theorem main_refusal_exclusion : RefusalExclusion ordinaryFailure .main :=
  refusal_exclusion_of_coverage ordinaryFailure .main main_coverage

theorem main_fatal_exclusion : FatalExclusion ordinaryFailure .main :=
  fatal_exclusion_of_coverage ordinaryFailure .main main_coverage

end Correspondence
end GoLean.GoCore.Relational.C1
