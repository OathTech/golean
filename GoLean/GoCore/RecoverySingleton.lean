import GoLean.GoCore.RecoverySuccessfulRuns
import GoLean.GoCore.ProgramTrace

/-! Structural exclusion of scheduling operations in the recovery profile.
These are properties of actual typed configurations, including saved call
and unwind continuations, rather than observations of one fixture. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine

theorem Control.not_blocked {world fs c} (h : Control world fs c) :
    isBlockedConfig c = false := by cases h <;> rfl

theorem ValueCont.no_spawn {world fs kind k} (h : ValueCont world fs kind k) (v : GoValue) :
    spawnPlan (.retV v k) = none := by induction h <;> first | assumption | rfl

theorem ValueCont.no_select {world fs kind k} (h : ValueCont world fs kind k) (v : GoValue) :
    selectApplyPlan (.retV v k) = none := by induction h <;> first | assumption | rfl

theorem ValueCont.no_registry {world fs kind k} (h : ValueCont world fs kind k)
    (v : GoValue) (s : ExecState) : (Config.retV v k).registryCommits s = false := by
  induction h <;> (first | assumption | rfl | skip)
  case strict =>
    rename_i Γ env op ds kind ps out done pending k he hp hd hes hk ih
    cases pending <;> rfl
  case rhs =>
    rename_i Γ env p before after refs done pending k he hr hd ha hk
    cases pending <;> rfl

theorem Control.no_spawn {world fs c} (h : Control world fs c) : spawnPlan c = none := by
  cases h <;> try rfl
  case ret hv hk => exact hk.no_spawn _

theorem Control.no_select {world fs c} (h : Control world fs c) : selectApplyPlan c = none := by
  cases h <;> try rfl
  case ret hv hk => exact hk.no_select _

theorem Control.no_registry {world fs c} (h : Control world fs c) (s : ExecState) :
    c.registryCommits s = false := by
  cases h <;> try rfl
  case ret hv hk => exact hk.no_registry _ _

theorem Control.no_flag {world fs c} (h : Control world fs c)
    (s : ExecState) (c' : Config) : c.afterStepFlag s c' = none := by
  simp [Config.afterStepFlag, h.no_spawn, h.no_registry]

theorem Control.terminal_iff {world fs c} (_h : Control world fs c) :
    c.isTerminal = true ↔ c = .next .stop := by
  cases c <;> try simp [Config.isTerminal]
  case next k => cases k <;> simp only [reduceCtorEq]

theorem Control.main_outcome {world fs c} (h : Control world fs c)
    (hn : c ≠ .next .stop) (s : ExecState) :
    (MultiConfig.mk #[Thread.running c none] s 0).mainOutcome? = none := by
  cases h <;> try rfl
  case next hk =>
    cases hk with
    | stop => contradiction
    | stmt hk => cases hk <;> rfl
    | resume => rfl

theorem Control.runConfig_zero {world fs c} (h : Control world fs c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    runConfig 0 s c ch = .error .fuelOut := by
  cases h <;> try rfl
  case next hk =>
    cases hk with
    | stop => contradiction
    | stmt hk => cases hk <;> rfl
    | resume => rfl

theorem Control.singleton_thread {world fs c} (h : Control world fs c)
    (hn : c.abort? = none) (s : ExecState) (ch : Choices) :
    stepThread s #[.running c none] 0 ch = (stepFn s c ch).map
      (fun r => (#[.running r.1 none], r.2.1, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
  unfold stepThread
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  rw [h0]
  simp only [h.not_blocked, Bool.false_eq_true, reduceIte, hn, h.no_spawn]
  rw [arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind, h.no_select, h.silent]
  cases hstep : stepFn s c ch with
  | error e => rfl
  | ok r =>
      obtain ⟨c', s', ch'⟩ := r
      simp [Except.map, Thread.afterStep, h.no_flag]

theorem Control.singleton_step {world fs c} (h : Control world fs c)
    (hn : c ≠ .next .stop) (ha : c.abort? = none) (s : ExecState) (ch : Choices) :
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
    rw [h.singleton_thread ha]
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

theorem singleton_abort_step (s : ExecState) (first : PanicEntry) (rest : List PanicEntry)
    (ch : Choices) :
    stepMulti ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ ch =
      (abortMsg s first rest).map (fun msg =>
        (⟨#[.aborted msg], s, 0⟩, ch, ⟨0, .aborted, [], []⟩)) := by
  simp only [stepMulti, Thread.atBoundary, Config.atBoundary, stepThreadInto, stepThread,
    Config.abort?, isBlockedConfig, Bool.false_eq_true, reduceIte,
    Array.getElem?_singleton, Except.map, Bind.bind, Except.bind]
  cases abortMsg s first rest <;> rfl

end GoLean.GoCore.RecoveryRuntime
