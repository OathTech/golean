import GoLean.GoCore.RecoverySingleton

/-! Same-fuel correspondence for the actual singleton pool, including its
abort tombstone transition. This theorem preserves renderer refusals as
well as successes, so it does not depend on a renderer totality claim. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine

theorem stepFn_success_no_abort {s c ch next t residual}
    (step : stepFn s c ch = .ok (next, t, residual)) : c.abort? = none := by
  fun_cases Config.abort? c
  · rename_i first rest
    have h : stepFn s (.panicking (first :: rest) .stop) ch =
        (abortMsg s first rest (abortConsult first rest ch).1).bind
          (fun msg => .error (.panic msg)) := rfl
    rw [h] at step
    cases hm : abortMsg s first rest (abortConsult first rest ch).1 <;>
      simp [hm, Except.bind] at step
  · rfl

theorem singleton_abort_driver (fuel : Nat) (s : ExecState)
    (first : PanicEntry) (rest : List PanicEntry) (ch : Choices)
    (rs : RaceState) (out : GoString) :
    execProgLoopOut (fuel + 1)
      ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ rs ch out =
      (out, runConfig (fuel + 1) s (.panicking (first :: rest) .stop) ch) := by
  have hrun : threadRunnable s (.running (.panicking (first :: rest) .stop) none) = true := rfl
  unfold execProgLoopOut
  simp only [show (#[Thread.running (.panicking (first :: rest) .stop) none] : Array Thread).isEmpty = false from rfl,
    Bool.false_eq_true, reduceIte, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
    runnableIdxs_singleton hrun, singleton_abort_step]
  -- Both drivers draw the same `repanicCollapse` pick (`consumeAtE`
  -- projects onto `consumeAt`, which `abortConsult` is).
  have hpick : (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
      = (abortConsult first rest ch).1 := by
    unfold abortConsult
    rw [← Choices.consumeAtE_fst_snd]
  rw [hpick]
  cases hm : abortMsg s first rest (abortConsult first rest ch).1 with
  | error e =>
    simp [hm, runConfig, stepFn, Bind.bind, Except.bind, Except.map,
      throw, throwThe, MonadExceptOf.throw]
  | ok message =>
    simp [hm, raceUpdate_single, runConfig, stepFn,
      Bind.bind, Except.bind, Except.map,
      throw, throwThe, MonadExceptOf.throw]
    rw [GoLean.Semantics.Pool.unfold_driver]
    rfl

/-- No output or choice is added by the singleton pool. The statement
uses the same fuel and exact actual sequential result, on every input
stream and initial race state/output prefix in the typed runtime domain. -/
theorem Inv.pool_eq_runConfig {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) (rs : RaceState) (out : GoString) :
    execProgLoopOut fuel ⟨#[.running c none], s, 0⟩ rs ch out =
      (out, runConfig fuel s c ch) := by
  induction fuel generalizing s c ch with
  | zero =>
      obtain ⟨world, heap, control, pins⟩ := inv.typed
      by_cases ht : c = .next .stop
      · subst c; rfl
      · have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
          (fun hterm => ht (control.terminal_iff.mp hterm))
        have hrun : threadRunnable s (.running c none) = true := by
          simp [threadRunnable, hd, control.not_blocked]
        rw [control.runConfig_zero ht]
        unfold execProgLoopOut
        simp [control.main_outcome ht, runnableIdxs_singleton hrun, MultiConfig.panicMsg?,
          throw, throwThe, MonadExceptOf.throw]
  | succ fuel ih =>
      obtain ⟨world, heap, control, pins⟩ := inv.typed
      rcases control_progress inv.program inv.sameContext heap control with rfl | abort | advance
      · rfl
      · obtain ⟨first, rest, rfl⟩ := abort
        exact singleton_abort_driver fuel s first rest ch rs out
      · obtain ⟨d, u, nextWorld, hu, _⟩ := advance ch
        have hn : c ≠ .next .stop := by intro he; subst c; simp [stepFn] at hu
        have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
          (fun ht => hn (control.terminal_iff.mp ht))
        have hrun : threadRunnable s (.running c none) = true := by
          simp [threadRunnable, hd, control.not_blocked]
        have hm := control.singleton_step hn (stepFn_success_no_abort hu) s ch
        rw [hu] at hm
        simp only [Except.map] at hm
        rw [BooleanRuntime.runConfig_eq_loop, execStmtLoop_step hu, ← BooleanRuntime.runConfig_eq_loop]
        unfold execProgLoopOut
        simp [control.main_outcome hn, runnableIdxs_singleton hrun, MultiConfig.panicMsg?,
          hm, raceUpdate_single, ih (inv.step (stepFn_sound hu))]

/-- Actual entry admission supplies the invariant internally. Empty output
holds on normal, panic, renderer-refusal and exhaustion paths alike. -/
theorem runProgramPool_eq_sequential {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryTyping.RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    runProgramPoolOutM fuel p name args ch =
      (runProgramM fuel p name args ch).mapError (fun e => (e, GoString.empty)) := by
  obtain ⟨f, zeros, _, _, setup, inv⟩ := setup_inv admitted fuel ch
  simp only [runProgramPoolOutM, setup, inv.pool_eq_runConfig, runProgramM,
    Bind.bind, Except.bind]
  cases hr : runConfig fuel (initialState p f args.toList zeros)
      (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop)) ch with
  | error e => rfl
  | ok v =>
      obtain ⟨final, residual⟩ := v
      dsimp only
      cases loadMany final (BooleanRuntime.initialResults f) <;> rfl

/-- An actual successful setup result receives the invariant supplied by
admission. This is an equality bridge, not a caller-proposed initial state. -/
theorem setup_result_inv {p : Program} {name : String} {args : Array GoValue}
    {fuel ch c s roots initial}
    (admitted : RecoveryTyping.RecoveryAdmission p name args)
    (setup : runProgramSetupM fuel p name args ch = .ok (c, s, roots, initial)) :
    initial = ch ∧ ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      Inv p f.results.toList roots s c := by
  obtain ⟨f, zeros, find, _, actual, inv⟩ := setup_inv admitted fuel ch
  rw [actual] at setup
  cases setup
  exact ⟨rfl, f, find, inv⟩

end GoLean.GoCore.RecoveryRuntime
