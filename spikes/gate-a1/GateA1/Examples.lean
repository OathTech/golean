import GateA1.ProgramTrace
import GateA1.Language

namespace GoLean.GateA1
open GoCore GoCore.Machine Semantics

namespace Customer
open Iris Iris.ProgramLogic Iris.ProgramLogic.Language

theorem recover_check_result :
    recoverResult (recoverCompare panicFrame) =
      ((panicEntry "audit").value, recoverCompare recoveredFrame) := by
  unfold recoverResult
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [recoverCompare, Cont.tail]
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [recoverBranch, Cont.tail]
  rw [Cont.rebuild_act (by rfl)]
  dsimp only [panicFrame]
  unfold recoverThroughWrappers
  rw [Cont.rebuild_act (by rfl)]
  rfl

theorem recover_check_step (s : ExecState) (ch : Choices) :
    stepFn s recoverCheck ch =
      .ok (.retV (panicEntry "audit").value (recoverCompare recoveredFrame), s, ch) := by
  rw [recoverCheck, recover_stepFn, recover_check_result]

theorem compare_recovered_step (s : ExecState) (ch : Choices) :
    stepFn s (.retV (panicEntry "audit").value (recoverCompare recoveredFrame)) ch =
      .ok (.retV (.bool true) (recoverBranch recoveredFrame), s, ch) := by
  have he : valueEq s (.interface ⟨"empty_interface"⟩) .nil (panicEntry "audit").value =
      .ok false := by
    rw [valueEq.eq_def]
    simp [TypeEnv.resolve, panicEntry, runtimeErrorValue, Pure.pure, Except.pure]
  simp [stepFn, recoverCompare, applyStrictOp, he,
    toResult, deliverS, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem recover_check_trace (s : ExecState) (ch : Choices) :
    Trace 7 s recoverCheck ch s (.next .stop) ch := by
  apply Trace.step (recover_check_step s ch)
  apply Trace.step (compare_recovered_step s ch)
  apply Trace.step (show stepFn s (.retV (.bool true) (recoverBranch recoveredFrame)) ch =
    .ok (.exec (.seqn #[]) [] recoveredFrame, s, ch) from rfl)
  apply Trace.step (show stepFn s (.exec (.seqn #[]) [] recoveredFrame) ch =
    .ok (.next (.seq [] [] recoveredFrame), s, ch) from rfl)
  apply Trace.step (show stepFn s (.next (.seq [] [] recoveredFrame)) ch =
    .ok (.next recoveredFrame, s, ch) from rfl)
  apply Trace.step (show stepFn s (.next recoveredFrame) ch =
    .ok (.next (.panicResumeK [{ panicEntry "audit" with recovered := true }] .stop), s, ch) from rfl)
  apply Trace.step (show stepFn s
    (.next (.panicResumeK [{ panicEntry "audit" with recovered := true }] .stop)) ch =
    .ok (.next .stop, s, ch) from rfl)
  exact .done

/-- Non-vacuity on the actual sequential driver, for every heap and stream. -/
theorem recover_check_runs (s : ExecState) (ch : Choices) :
    execStmtLoop 7 s recoverCheck ch = .ok (s, ch) :=
  run_ok_iff.mpr ⟨7, Nat.le_refl _, recover_check_trace s ch⟩

/-- A complete, non-stuck recovery execution, uniform in heap and stream.
The value is checked against nil, the deferred frame exits, and the marked
panic resumes normally. The failed check would explicitly refuse. -/
instance recover_check_exec : PureExec True 7 recoverCheck (Config.next .stop) where
  pureExec _ := by
    apply Relation.Iterate.head (pure_of_stepFn recover_check_step)
    apply Relation.Iterate.head (pure_of_stepFn compare_recovered_step)
    apply Relation.Iterate.head (pure_of_stepFn
      (c' := .exec (.seqn #[]) [] recoveredFrame) (fun _ _ => rfl))
    apply Relation.Iterate.head (pure_of_stepFn
      (c' := .next (.seq [] [] recoveredFrame)) (fun _ _ => rfl))
    apply Relation.Iterate.head (pure_of_stepFn
      (c' := .next recoveredFrame) (fun _ _ => rfl))
    apply Relation.Iterate.head (pure_of_stepFn
      (c' := .next (.panicResumeK [{ panicEntry "audit" with recovered := true }] .stop))
      (fun _ _ => rfl))
    exact Relation.Iterate.once (pure_of_stepFn (c' := .next .stop) (fun _ _ => rfl))

/-- The consumer derives a terminating recovery fact through Iris's
public pure-step rule; its final obligation is only the postcondition. -/
theorem wp_recover_check {GF : BundledGFunctors} {hlc : HasLC}
    [IrisGS_gen hlc Config GF] {E : CoPset} {Φ : Unit → IProp GF} :
    (▷^[7] (£ 7 -∗ Φ ())) ⊢
      WP recoverCheck @ Stuckness.NotStuck; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step_later (e₁ := recoverCheck) (n := 7) trivial)
  apply BI.laterN_mono
  apply BI.wand_mono
  · exact .rfl
  · exact wp_value' (v := ())

end Customer
end GoLean.GateA1
