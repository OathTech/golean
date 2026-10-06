import GoLean.GoCore.PoolStatement

/-! Full singleton labels. [AGENT Codex, pool grind] 2026-10-06. -/
namespace GoLean.GoCore.PoolSingletonFacts
open GoLean GoLean.GoCore GoLean.GoCore.Machine
variable {ctx : ProgramCtx}

theorem thread_label {σ : Store} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsp : spawnPlan c = none) (hab : c.abort? = none)
    {c' : Config} {σ' : Store} {ch' : Choices} {l : StepLabel}
    (hstep : stepFn ctx σ c ch = .ok (c', σ', ch', l)) :
    ∃ ev, stepThread ctx σ #[.running c none] 0 ch = .ok (#[Thread.afterStep σ c c'], σ', ch', ev)
      ∧ ev.who = 0 ∧ ev.label = l := by
  unfold stepThread
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  rw [h0]
  simp only [hbl, Bool.false_eq_true, reduceIte, hab, hsp]
  rw [show arrivalPlan ctx σ #[Thread.running c none] 0 c ch = .ok (none, ch, [])
    from arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind]
  cases hselp : selectApplyPlan c with
  | none =>
      rw [hstep]
      exact ⟨⟨0, .privateStep, { l with picks := [] ++ l.picks }⟩, rfl, rfl, rfl⟩
  | some p =>
      obtain ⟨v, clauses, default?, done, env, k'⟩ := p
      obtain rfl := selectApplyPlan_shape hselp
      dsimp only
      cases happly : applySelect ctx σ clauses default? ((v :: done).reverse) env k' ch with
      | ok r =>
          obtain ⟨c₂, s₂, ch₂, ps, cl?, tr⟩ := r
          have hfn : stepFn ctx σ (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = .ok (c₂, s₂, ch₂, ⟨tr, ps, []⟩) := by
            unfold stepFn
            dsimp only
            rw [happly]
            rfl
          rw [hfn] at hstep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hstep
          refine ⟨⟨0, match cl? with
            | some cl => .selectCommit cl
            | none => .selectPass, ⟨tr, [] ++ ps, []⟩⟩, ?_, rfl, rfl⟩
          cases cl? <;> rfl
      | error e =>
          have hfn : stepFn ctx σ (.retV v (.selectOpsK clauses default? done [] env k')) ch
              = (match e with
                 | .panic msg => .ok (.panicking [panicEntry msg] k', σ, ch, ⟨[], [], []⟩)
                 | e => .error e) := by
            unfold stepFn
            dsimp only
            simp only [happly]
            cases_stop e <;> rfl
          rw [hfn] at hstep
          cases_stop e <;> simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hstep
          case panic msg =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hstep
            exact ⟨⟨0, .selectPass, ⟨[], [], []⟩⟩, rfl, rfl, rfl⟩

/-- The singleton pool preserves the entire sequential label and attributes its event to 0. -/
theorem multi_label {σ : Store} {c : Config} {ch : Choices}
    (hbl : isBlockedConfig c = false) (hsp : spawnPlan c = none) (hab : c.abort? = none)
    (hdone : c.isTerminal = false)
    {c' : Config} {σ' : Store} {ch' : Choices} {l : StepLabel}
    (hstep : stepFn ctx σ c ch = .ok (c', σ', ch', l)) :
    ∃ ev, stepMulti ctx ⟨#[.running c none], σ, 0⟩ ch = .ok (⟨#[Thread.afterStep σ c c'], σ', 0⟩, ch', ev)
      ∧ ev.who = 0 ∧ ev.label = l := by
  have hrun : threadRunnable ctx σ (.running c none) = true := by
    simp [threadRunnable, hdone, hbl]
  obtain ⟨ev, hst, hev⟩ := thread_label hbl hsp hab hstep
  have hinto : stepThreadInto ctx ⟨#[.running c none], σ, 0⟩ 0 ch
      = .ok (⟨#[Thread.afterStep σ c c'], σ', 0⟩, ch', ev) := by
    unfold stepThreadInto
    show (stepThread ctx σ #[.running c none] 0 ch).bind _ = _
    rw [hst]
    rfl
  unfold stepMulti
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  simp only [h0]
  by_cases hb : Thread.atBoundary (.running c none) = true
  · simp only [hb, reduceIte]
    rw [show schedSlots ctx σ #[Thread.running c none] 0 (Thread.boundarySite (.running c none)) = [0]
      from schedSlots_singleton hrun]
    dsimp only
    rw [show Choices.consumeAtE (Thread.boundarySite (.running c none)) [0].length ch = (0, ch, [])
      from Choices.consumeAtE_le_one (by simp)]
    simp only [List.getElem?_cons_zero]
    simp only [Bind.bind, Except.bind]
    rw [hinto]
    exact ⟨_, rfl, hev⟩
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, reduceIte]
    exact ⟨ev, hinto, hev⟩

theorem step_label {σ : Store} {c : Config} {ch : Choices}
    {c' : Config} {σ' : Store} {ch' : Choices} {l : StepLabel}
    (h : stepFn ctx σ c ch = .ok (c', σ', ch', l)) :
    ∃ ev, stepMulti ctx ⟨#[.running c none], σ, 0⟩ ch =
      .ok (⟨#[Thread.afterStep σ c c'], σ', 0⟩, ch', ev) ∧ ev.who = 0 ∧ ev.label = l := by
  have hs := stepFn_sound h
  have hsp : spawnPlan c = none := by
    cases he : spawnPlan c with
    | none => rfl
    | some p => exact False.elim (step_spawnPos_elim he hs)
  exact multi_label (isBlockedConfig_false_of_stepFn_ok h) hsp
    (abort?_none_of_stepE (n := 0) (.lift hs)) (isTerminal_false_of_stepFn_ok h) h

end GoLean.GoCore.PoolSingletonFacts
