import GoLean.GoCore.BooleanProgram
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.Trace

/-! The shipped output-folding singleton driver for admitted Boolean programs.
Same fuel, original and residual choices, event output, actual result pins
and readout remain explicit. This supplies no multi-thread pool converse. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

theorem Control.not_blocked {root roots c} (h : Control root roots c) :
    isBlockedConfig c = false := by cases h <;> rfl

theorem Control.no_abort {root roots c} (h : Control root roots c) :
    c.abort? = none := by cases h <;> rfl

theorem Control.no_spawn {root roots c} (h : Control root roots c) :
    spawnPlan c = none := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Control.no_select {root roots c} (h : Control root roots c) :
    selectApplyPlan c = none := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Control.no_registry {root roots c} (h : Control root roots c) (s : ExecState) :
    c.registryCommits s = false := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Control.no_flag {root roots c} (h : Control root roots c)
    (s : ExecState) (c' : Config) : c.afterStepFlag s c' = none := by
  simp [Config.afterStepFlag, h.no_spawn, h.no_registry]

theorem Control.terminal_iff {root roots c} (_h : Control root roots c) :
    c.isTerminal = true ↔ c = .next .stop := by
  cases c <;> try simp [Config.isTerminal]
  case next k => cases k <;> simp only [reduceCtorEq]

theorem Control.main_outcome {root roots c} (h : Control root roots c)
    (hn : c ≠ .next .stop) (s : ExecState) :
    (MultiConfig.mk #[Thread.running c none] s 0).mainOutcome? = none := by
  cases h <;> try rfl
  · contradiction
  · rename_i k hk
    cases hk <;> rfl

theorem Control.singleton_thread {root roots c} (h : Control root roots c)
    (s : ExecState) (ch : Choices) :
    stepThread s #[.running c none] 0 ch = (stepFn s c ch).map
      (fun r => (#[.running r.1 none], r.2.1, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
  unfold stepThread
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  rw [h0]
  simp only [h.not_blocked, Bool.false_eq_true, reduceIte, h.no_abort, h.no_spawn]
  rw [arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind, h.no_select, h.silent]
  cases hstep : stepFn s c ch with
  | error e => rfl
  | ok r =>
      obtain ⟨c', s', ch'⟩ := r
      simp [Except.map, Thread.afterStep, h.no_flag]

theorem Control.singleton_step {root roots c} (h : Control root roots c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    stepMulti ⟨#[.running c none], s, 0⟩ ch = (stepFn s c ch).map
      (fun r => (⟨#[.running r.1 none], r.2.1, 0⟩, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
  have hd : c.isTerminal = false := Bool.eq_false_iff.mpr (fun ht => hn (h.terminal_iff.mp ht))
  have hrun : threadRunnable s (.running c none) = true := by
    simp [threadRunnable, hd, h.not_blocked]
  have hinto : stepThreadInto ⟨#[.running c none], s, 0⟩ 0 ch =
      (stepFn s c ch).map (fun r =>
        (⟨#[.running r.1 none], r.2.1, 0⟩, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
    unfold stepThreadInto
    show (stepThread s #[.running c none] 0 ch).bind _ = _
    rw [h.singleton_thread]
    cases stepFn s c ch <;> simp [Except.bind, Except.map]
  unfold stepMulti
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  simp only [h0]
  by_cases hb : Thread.atBoundary (.running c none) = true
  · simp only [hb, reduceIte]
    rw [schedSlots_singleton hrun]
    dsimp only
    rw [show Choices.consumeAtE (Thread.boundarySite (.running c none)) [0].length ch =
        (0, ch, []) from Choices.consumeAtE_le_one (by simp)]
    simp only [List.getElem?_cons_zero, Bind.bind, Except.bind]
    rw [hinto]
    cases stepFn s c ch <;> simp [Except.map]
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, reduceIte]
    exact hinto

theorem Control.runConfig_zero {root roots c} (h : Control root roots c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    runConfig 0 s c ch = .error .fuelOut := by
  cases h <;> try rfl
  · contradiction
  · rename_i k hk
    cases hk <;> rfl

/-- The shipped output-folding singleton driver agrees at the SAME fuel,
store and choice stream with the actual sequential driver. No event output
or choice consumption occurs, including on the exhaustion path. -/
theorem Inv.pool_eq_runConfig {context results s c} (h : Inv context results s c)
    (fuel : Nat) (ch : Choices) (rs : RaceState) (out : GoString) :
    execProgLoopOut fuel ⟨#[.running c none], s, 0⟩ rs ch out =
      (out, runConfig fuel s c ch) := by
  induction fuel generalizing s c ch with
  | zero =>
      by_cases ht : c = .next .stop
      · subst c; rfl
      · have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
          (fun hterm => ht (h.control.terminal_iff.mp hterm))
        have hrun : threadRunnable s (.running c none) = true := by
          simp [threadRunnable, hd, h.control.not_blocked]
        rw [h.control.runConfig_zero ht]
        unfold execProgLoopOut
        simp [h.control.main_outcome ht, runnableIdxs_singleton hrun, MultiConfig.panicMsg?,
          throw, throwThe, MonadExceptOf.throw]
  | succ fuel ih =>
      rcases control_advances h.heap h.control with rfl | ha
      · rfl
      · obtain ⟨d, u, hu, _, _⟩ := ha ch
        have hn : c ≠ .next .stop := by intro he; subst c; simp [stepFn] at hu
        have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
          (fun ht => hn (h.control.terminal_iff.mp ht))
        have hrun : threadRunnable s (.running c none) = true := by
          simp [threadRunnable, hd, h.control.not_blocked]
        have hm := h.control.singleton_step hn s ch
        rw [hu] at hm
        simp only [Except.map] at hm
        rw [runConfig_eq_loop, execStmtLoop_step hu, ← runConfig_eq_loop]
        unfold execProgLoopOut
        simp [h.control.main_outcome hn, runnableIdxs_singleton hrun, MultiConfig.panicMsg?,
          hm, raceUpdate_single, ih (h.step (stepFn_sound hu))]

/-- Actual whole-program driver correspondence in the admitted Boolean
domain. The output-folding driver preserves empty output even on fuel-out. -/
theorem runProgramPool_eq_sequential {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    runProgramPoolOutM fuel p name args ch =
      (runProgramM fuel p name args ch).mapError (fun e => (e, GoString.empty)) := by
  obtain ⟨f, env, s, locs, _, _, hs, hi, _⟩ := setup_typed h fuel ch
  simp only [runProgramPoolOutM, hs, hi.pool_eq_runConfig, runProgramM,
    Bind.bind, Except.bind]
  cases hr : runConfig fuel s (.exec f.body env (.frame [] [] [] [] .stop)) ch with
  | error e => rfl
  | ok v =>
      obtain ⟨sf, chf⟩ := v
      dsimp only
      cases loadMany sf locs <;> rfl

/-- Typed readout or explicit fuel exhaustion for the SHIPPED driver,
uniformly over every supplied choice stream. No panic or model refusal is
hidden in the success alternative; both paths have proved empty output. -/
theorem runProgramPool_typed {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ bs : List Bool, bs.length = f.results.size ∧
        runProgramPoolOutM fuel p name args ch =
          .ok { values := (bs.map GoValue.bool).toArray, output := GoString.empty }) ∨
       runProgramPoolOutM fuel p name args ch = .error (.fuelOut, GoString.empty)) := by
  obtain ⟨f, hf, hr⟩ := runProgram_typed h fuel ch
  refine ⟨f, hf, ?_⟩
  rw [runProgramPool_eq_sequential h]
  rcases hr with ⟨bs, hb, hr⟩ | hr
  · exact .inl ⟨bs, hb, by rw [hr]; rfl⟩
  · exact .inr (by rw [hr]; rfl)

theorem runProgramPool_no_refusal {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) :
    runProgramPoolOutM fuel p name args ch ≠ .error (.refusal reason, out) := by
  obtain ⟨_, _, hr⟩ := runProgramPool_typed h fuel ch
  rcases hr with ⟨_, _, hr⟩ | hr <;> rw [hr] <;> simp

theorem Control.no_seq_consumption {root roots c} (h : Control root roots c)
    (s : ExecState) : seqConsumption s c = none := by
  cases h <;> try rfl
  case next hk => cases hk <;> rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl
  case exec hc he hs hk => cases hs <;> rfl
  case execSeq hc he hs ht hk => cases hs <;> rfl
  case returning hk => cases hk <;> rfl

/-- A successful sequential run supplies an exact bounded trace on the
original stream, a typed final invariant, actual readout and the shipped
pool execution. All conclusions use that SAME stream, not existentially
reselected choices. Functional clients may supply a separate termination
witness; generic safety is already available without this success premise. -/
theorem Inv.success_contract {context results s c fuel ch sf chf}
    (h : Inv context results s c) (hr : runConfig fuel s c ch = .ok (sf, chf)) :
    chf = ch ∧ ∃ n : Nat, n ≤ fuel ∧
      GoLean.Semantics.Trace n s c ch sf (.next .stop) ch ∧
      Inv context results sf (.next .stop) ∧
      (∃ bs : List Bool, loadMany sf results = .ok (bs.map GoValue.bool) ∧
        bs.length = results.length) ∧
      GoLean.Semantics.Pool.Run fuel ⟨#[.running c none], s, 0⟩ {} ch GoString.empty
        (GoString.empty, .ok (sf, ch)) := by
  have hc := h.run_choices hr
  subst chf
  obtain ⟨n, hn, ht⟩ := GoLean.Semantics.run_ok_iff.mp
    (by simpa only [runConfig_eq_loop] using hr)
  exact ⟨rfl, n, hn, ht, h.steps ht.erase, h.run_readout hr,
    GoLean.Semantics.Pool.run_iff.mp (by rw [h.pool_eq_runConfig, hr])⟩

end GoLean.GoCore.BooleanRuntime
