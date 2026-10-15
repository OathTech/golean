import LocalOutcomeConstraint
import OperationCheck

namespace GoLean.GoCore.Relational.C1.Correspondence
open Machine ExecutionStatement

theorem zero_cost_coverage {ctx : ProgramCtx} {a : State} (hz : C1.ZeroCost ctx a)
    (failure : OperationFailure) (mode : Mode) (budget : Nat) (ch : Choices) :
    ∃ o, C1.Execution failure mode ctx budget a [] a [] o 0 ∧
      driver mode ctx budget a ch = observe o a ch := by
  have hz := Boundary.zero_cost_iff.mp hz
  obtain ⟨c, s⟩ := a
  rcases hz with h | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
      ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> dsimp only at h <;> subst c
  · refine ⟨.boundary .normal, .finished (.boundary .normal (.inl rfl)) (Nat.zero_le _), ?_⟩
    cases mode <;> simp [driver, execStmtLoop_unfold, runInitConfig, observe, Outcome.stop?]
  · refine ⟨.boundary .deadlock, .finished (.boundary .send (.inl rfl)) (Nat.zero_le _), ?_⟩
    cases mode <;> simp [driver, execStmtLoop_unfold, runInitConfig, observe, Outcome.stop?] <;> rfl
  · refine ⟨.boundary .deadlock, .finished (.boundary .recv (.inl rfl)) (Nat.zero_le _), ?_⟩
    cases mode <;> simp [driver, execStmtLoop_unfold, runInitConfig, observe, Outcome.stop?] <;> rfl
  · refine ⟨.boundary .deadlock, .finished (.boundary .select (.inl rfl)) (Nat.zero_le _), ?_⟩
    cases mode <;> simp [driver, execStmtLoop_unfold, runInitConfig, observe, Outcome.stop?] <;> rfl
  · refine ⟨.boundary .deadlock, .finished (.boundary .sync (.inl rfl)) (Nat.zero_le _), ?_⟩
    cases mode <;> simp [driver, execStmtLoop_unfold, runInitConfig, observe, Outcome.stop?] <;> rfl

theorem error_finish (failure : OperationFailure) (coverage : OperationCoverage failure)
    {ctx : ProgramCtx} {a : State} {ch : Choices} {e : Stop}
    (hz : ¬ C1.ZeroCost ctx a) (he : stepFn ctx a.store a.control ch = .error e) :
    ∃ records o tail, C1.Finish failure .main ctx a records o 1 ∧
      replays records ch tail ∧ observe o a tail = .error e := by
  obtain ⟨c, s⟩ := a
  have hz' : ¬ ExecutionStatement.ZeroCost c := fun h => hz (Boundary.zero_cost_iff.mpr h)
  rcases stepFn_error_cases hz' he with
    ⟨hab, ⟨text, rfl⟩ | ⟨reason, rfl⟩⟩ | ⟨hab, ⟨reason, rfl⟩ | ⟨message, rfl⟩⟩
  · obtain ⟨⟨first, rest⟩, ha⟩ := Option.isSome_iff_exists.mp hab
    obtain ⟨records, tail, hf⟩ := finish_aborted_of_stepFn ha he
    cases hf with
    | aborted ha hc hm =>
      refine ⟨_, .boundary (.panic _ _ _), tail,
        .boundary (.panic ha (selection_of_consume hc) hm) (.inr trivial), ?_, rfl⟩
      exact OperationCheck.Correspondence.consume_replays hc
  · obtain ⟨⟨first, rest⟩, ha⟩ := Option.isSome_iff_exists.mp hab
    obtain ⟨records, tail, hf⟩ := (finish_refused_step ctx _ _ _ first rest reason ha).mpr he
    cases hf with
    | abortRefused ha hc hm =>
      refine ⟨_, .boundary (.renderingRefusal _ _ _), tail,
        .boundary (.renderingRefusal ha (selection_of_consume hc) hm) (.inr trivial), ?_, rfl⟩
      exact OperationCheck.Correspondence.consume_replays hc
  · obtain ⟨records, tail, hf, hr⟩ := coverage ctx ⟨c, s⟩ ch (.refusal reason) hz hab he
    exact ⟨records, .failed (.refusal reason), tail, .operation hz hab trivial hf, hr, rfl⟩
  · obtain ⟨records, tail, hf, hr⟩ := coverage ctx ⟨c, s⟩ ch (.fatal message) hz hab he
    exact ⟨records, .failed (.fatal message), tail, .operation hz hab trivial hf, hr, rfl⟩

theorem main_coverage_of_operation (failure : OperationFailure)
    (coverage : OperationCoverage failure) : Coverage failure .main := by
  intro ctx budget
  induction budget with
  | zero =>
    intro a ch
    by_cases hz : C1.ZeroCost ctx a
    · obtain ⟨o, hx, he⟩ := zero_cost_coverage hz failure .main 0 ch
      exact ⟨[], a, [], o, 0, ch, ch, hx, .done, rfl, he⟩
    · refine ⟨[], a, [], .exhausted, 0, ch, ch, .exhausted hz trivial, .done, rfl, ?_⟩
      exact execStmtLoop_nonZero (fun h => hz (Boundary.zero_cost_iff.mpr h))
  | succ budget ih =>
    intro a ch
    by_cases hz : C1.ZeroCost ctx a
    · obtain ⟨o, hx, he⟩ := zero_cost_coverage hz failure .main (budget + 1) ch
      exact ⟨[], a, [], o, 0, ch, ch, hx, .done, rfl, he⟩
    · have hu := execStmtLoop_nonZero (ctx := ctx) (fuel := budget + 1) (s := a.store)
        (ch := ch) (fun h => hz (Boundary.zero_cost_iff.mpr h))
      cases hs : stepFn ctx a.store a.control ch with
      | error e =>
        obtain ⟨records, o, tail, hf, hr, he⟩ := error_finish failure coverage hz hs
        refine ⟨[], a, records, o, 1, ch, tail,
          .finished hf (Nat.succ_le_succ (Nat.zero_le _)), .done, hr, ?_⟩
        simpa only [driver, hs, Except.bind, ← he] using hu
      | ok result =>
        obtain ⟨c, s, nextCh, label⟩ := result
        obtain ⟨ls, b, records, o, cost, middle, tail, hx, hp, hr, he⟩ := ih ⟨c, s⟩ nextCh
        refine ⟨label :: ls, b, records, o, cost + 1, middle, tail,
          .step trivial (stepFn_sound hs) hx, .step hs hp, hr, ?_⟩
        change execStmtLoop ctx _ _ _ _ = _
        rw [hu, hs]
        exact he

theorem boundary_main_realize {ctx : ProgramCtx} {a : State} {records : List PickRecord}
    {ending : Ending} {cost budget : Nat} (h : Boundary ctx a records ending cost)
    (enough : cost ≤ budget) (tail : Choices) :
    ∃ ch, replays records ch tail ∧
      driver .main ctx budget a ch = observe (.boundary ending) a tail := by
  cases h with
  | normal =>
    exact ⟨tail, rfl, by simp [driver, execStmtLoop_unfold, observe, Outcome.stop?]⟩
  | send =>
    exact ⟨tail, rfl, by simp [driver, execStmtLoop_unfold, observe, Outcome.stop?]; rfl⟩
  | recv =>
    exact ⟨tail, rfl, by simp [driver, execStmtLoop_unfold, observe, Outcome.stop?]; rfl⟩
  | select =>
    exact ⟨tail, rfl, by simp [driver, execStmtLoop_unfold, observe, Outcome.stop?]; rfl⟩
  | sync =>
    exact ⟨tail, rfl, by simp [driver, execStmtLoop_unfold, observe, Outcome.stop?]; rfl⟩
  | panic ha hp hm =>
    obtain ⟨ch, hc⟩ := hp.realize tail
    refine ⟨ch, OperationCheck.Correspondence.consume_replays hc, ?_⟩
    obtain ⟨ha, settled⟩ := abort?_some ha
    cases budget with
    | zero => omega
    | succ budget =>
      simp only [driver, ha]
      rw [execStmtLoop_nonZero (by simp [ExecutionStatement.ZeroCost, Blocked]), stepFn_abort settled, hc]
      simp only [hm, Except.bind]
      rfl
  | renderingRefusal ha hp hm =>
    obtain ⟨ch, hc⟩ := hp.realize tail
    refine ⟨ch, OperationCheck.Correspondence.consume_replays hc, ?_⟩
    obtain ⟨ha, settled⟩ := abort?_some ha
    cases budget with
    | zero => omega
    | succ budget =>
      simp only [driver, ha]
      rw [execStmtLoop_nonZero (by simp [ExecutionStatement.ZeroCost, Blocked]), stepFn_abort settled, hc]
      simp only [hm, Except.bind]
      rfl

theorem finish_main_realize (failure : OperationFailure)
    (replay : OperationReplay failure) (selections : OperationSelections failure)
    {ctx : ProgramCtx} {a : State} {records : List PickRecord} {o : Outcome} {cost budget : Nat}
    (h : C1.Finish failure .main ctx a records o cost) (enough : cost ≤ budget) (tail : Choices) :
    ∃ ch, replays records ch tail ∧ driver .main ctx budget a ch = observe o a tail := by
  cases h with
  | boundary hb _ => exact boundary_main_realize hb enough tail
  | initializationPrint hm _ => cases hm
  | operation hz _ _ hf =>
    obtain ⟨ch, hr⟩ := selections _ _ _ _ hf tail
    refine ⟨ch, hr, ?_⟩
    have hs := replay _ _ _ _ hf ch tail hr
    cases budget with
    | zero => omega
    | succ budget =>
      change execStmtLoop ctx _ _ _ _ = _
      rw [execStmtLoop_nonZero (fun h => hz (Boundary.zero_cost_iff.mpr h)), hs]
      rfl

theorem main_realization_of_operation (failure : OperationFailure)
    (replay : OperationReplay failure) (selections : OperationSelections failure) :
    Realization failure .main := by
  intro ctx budget a ls b records o cost h tail
  induction h with
  | finished hf enough =>
    obtain ⟨ch, hr, he⟩ := finish_main_realize failure replay selections hf enough tail
    exact ⟨ch, ch, .done, hr, he⟩
  | exhausted hz _ =>
    refine ⟨tail, tail, .done, rfl, ?_⟩
    exact execStmtLoop_nonZero (fun h => hz (Boundary.zero_cost_iff.mpr h))
  | step _ hs _ ih =>
    obtain ⟨ch, middle, hp, hr, he⟩ := ih
    obtain ⟨start, oldTail, hstep⟩ := step_complete hs
    obtain ⟨start, hstep⟩ := stepFn_any_residual hstep ch
    refine ⟨start, middle, .step hstep hp, hr, ?_⟩
    change execStmtLoop ctx _ _ _ _ = _
    rw [execStmtLoop_nonZero (stepFn_zeroCost_not_ok hstep), hstep]
    exact he

end GoLean.GoCore.Relational.C1.Correspondence
