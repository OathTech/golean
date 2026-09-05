import GateA1.ProgramTrace
import GateA1.Language

namespace GoLean.GateA1
open GoCore GoCore.Machine

def exampleState : ExecState := { types := TypeEnv.reserved }
def choicePool : MultiConfig := ⟨#[Thread.running forkPoint none], exampleState, 0⟩

/-- Hand-authored GoCore; no claim of a certified Go frontend translation. -/
def printPanicProgram : Program := { funcs := #[{
  id := ⟨"main.audit"⟩, args := #[], results := #[],
  body := .seqn #[.print true #[.stringLit (GoString.fromLeanString "before")],
    .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) .string
      (.stringLit (GoString.fromLeanString "boom")))] }] }

def recoverBranch (k : Cont) : Cont :=
  .ifK (.seqn #[]) (.unsupported "recovery did not happen") [] k
def recoverCompare (k : Cont) : Cont :=
  .strictK (.neqCmp (.interface ⟨"empty_interface"⟩)) [.nil] [] [] (recoverBranch k)
def recoverCheck : Config := .evalE .recoverCall [] (recoverCompare panicFrame)

/-- An injective readout for panic results, to make kernel computation
avoid equality instances for unrelated successful result values. -/
def panicObservation : RunResult → Option (String × Array UInt8)
  | .error (.terminal (.panic msg), out) => some (msg, out.bytes)
  | _ => none

theorem panicObservation_sound {r : RunResult} {msg : String} {bytes : Array UInt8}
    (h : panicObservation r = some (msg, bytes)) :
    r = .error (.panic msg, ⟨bytes⟩) := by
  cases r with
  | ok v => cases h
  | error e =>
    obtain ⟨stop, ⟨out⟩⟩ := e
    cases stop with
    | refusal e => cases h
    | fuelOut => cases h
    | terminal t => cases t with
      | panic m =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rfl
      | fatal m => cases h
      | deadlock => cases h
      | raceDetected => cases h

set_option maxRecDepth 4096 in
/-- Full entry, actual print event, abort, and the retained byte prefix. -/
theorem print_before_panic :
    runProgramPoolOutM 20 printPanicProgram "main.audit" #[] [] =
      .error (.panic "boom", GoString.fromLeanString "before\n") := by
  apply panicObservation_sound
  decide +kernel

theorem print_before_panic_trace :
    Pool.ProgramRun 20 printPanicProgram "main.audit" #[] []
      (.error (.panic "boom", GoString.fromLeanString "before\n")) :=
  Pool.program_run_iff.mp print_before_panic

/-- Terminal checking precedes exhaustion. One step suffices for DEFER. -/
theorem defer_completes (s : ExecState) (tail : Choices) :
    execStmtLoop 1 s forkPoint (0 :: tail) = .ok (s, tail) :=
  run_ok_iff.mpr ⟨1, Nat.le_refl _, defer_trace s tail⟩

theorem raise_needs_abort_fuel (s : ExecState) (tail : Choices) :
    execStmtLoop 1 s forkPoint (1 :: tail) = .error .fuelOut := by
  rw [execStmtLoop_step (choose_raise s tail)]
  rfl

theorem raise_aborts :
    execStmtLoop 2 exampleState forkPoint [1] = .error (.panic "audit") := by
  rw [execStmtLoop_step (choose_raise exampleState [])]
  with_unfolding_all rfl

/-- Both directions of the corrected bridge at the actual choice site. -/
theorem defer_run_iff :
    execStmtLoop 1 exampleState forkPoint [0] = .ok (exampleState, []) ↔
      ∃ n, n ≤ 1 ∧ Trace n exampleState forkPoint [0] exampleState (.next .stop) [] :=
  run_ok_iff

theorem pool_defer (acc : GoString) :
    execProgLoopOut 2 choicePool {} [0] acc = (acc, .ok (exampleState, [])) := by
  with_unfolding_all rfl

theorem pool_raise (acc : GoString) :
    execProgLoopOut 2 choicePool {} [1] acc = (acc, .error (.panic "audit")) := by
  with_unfolding_all rfl

theorem both_pool_traces (acc : GoString) :
    Pool.Run 2 choicePool {} [0] acc (acc, .ok (exampleState, [])) ∧
    Pool.Run 2 choicePool {} [1] acc (acc, .error (.panic "audit")) :=
  ⟨Pool.run_iff.mp (pool_defer acc), Pool.run_iff.mp (pool_raise acc)⟩

theorem two_choice_pool_bridge (acc : GoString) :
    (∃ ch, execProgLoopOut 2 choicePool {} ch acc = (acc, .error (.panic "audit"))) ∧
    execProgLoopOut 2 choicePool {} [0] acc ≠ (acc, .error (.panic "audit")) := by
  refine ⟨⟨[1], pool_raise acc⟩, ?_⟩
  rw [pool_defer]
  intro h
  cases (Prod.mk.inj h).2

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
