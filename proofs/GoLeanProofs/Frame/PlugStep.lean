import GoLeanProofs.Frame.PlugApply

/-!
# THE PLUG RULE, part 4: the per-step commutation walk (design note §7)

`stepFn_plug`: on a barrier-carrying configuration, every successful
machine step commutes with the below-barrier replacement `plugC`, and
the step's result either still carries the barrier, is the exit
(`.next .stop`), or is the panic-crossed shape
(`.panicking chain .stop` — refuted from span success at the
iteration level). The walk is `fun_cases stepFn` over every arm
(the rename walk's skeleton, `Frame/StepSim.lean`, state-trivially:
both sides share σ and the choice stream verbatim).

Premises (§7, the non-locality census): `mapIterFree k'` (the
delete-prune walks cross call frames), `recoverThroughWrappers k' =
none` (a barrier-level `recover()` inspects below a non-wrapper
barrier). The barrier itself is the well-shaped `hasBarrierC`
invariant (resultless, non-wrapper — §7 premise 3 is folded into the
shape).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option autoImplicit false

variable {env' : LocalEnv} {k' : Cont}

/-- The per-step plug correspondence: IF the canonical step succeeds,
the plugged step produces the `plugC`-image at the same state/stream,
and the result classifies (barrier kept / exit / crossed). -/
def PS (env' : LocalEnv) (k' : Cont)
    (x y : Except GoError (Config × ExecState × Choices)) : Prop :=
  ∀ ⦃d : Config⦄ ⦃σ₁ : ExecState⦄ ⦃ch₁ : Choices⦄,
    x = .ok (d, σ₁, ch₁) →
    y = .ok (plugC env' k' d, σ₁, ch₁)
    ∧ (hasBarrierC d = true ∨ d = .next .stop
        ∨ ∃ chain, d = .panicking chain .stop)

theorem PS.err {e : GoError}
    {y : Except GoError (Config × ExecState × Choices)} :
    PS env' k' (.error e) y := fun _ _ _ h => nomatch h

theorem PS.throw {e : GoError}
    {y : Except GoError (Config × ExecState × Choices)} :
    PS env' k' (throw e) y := PS.err

/-- Close an `.ok` arm: supply the plugged step's reduction and the
classification. -/
theorem PS.ok {d : Config} {σ₁ : ExecState} {ch₁ : Choices}
    {y : Except GoError (Config × ExecState × Choices)}
    (h₁ : y = .ok (plugC env' k' d, σ₁, ch₁))
    (h₂ : hasBarrierC d = true ∨ d = .next .stop
        ∨ ∃ chain, d = .panicking chain .stop) :
    PS env' k' (.ok (d, σ₁, ch₁)) y := by
  intro d₂ σ₂ ch₂ h
  cases h
  exact ⟨h₁, h₂⟩

theorem PS.pure {d : Config} {σ₁ : ExecState} {ch₁ : Choices}
    {y : Except GoError (Config × ExecState × Choices)}
    (h₁ : y = .ok (plugC env' k' d, σ₁, ch₁))
    (h₂ : hasBarrierC d = true ∨ d = .next .stop
        ∨ ∃ chain, d = .panicking chain .stop) :
    PS env' k' (pure (d, σ₁, ch₁)) y := PS.ok h₁ h₂

/-- Frame entry commutes (the nested-call arms): the entry is
state-only; the built configuration and the entry-panic continuation
carry the plug through the `mk`/`k` premises. -/
theorem PS.enterFrameStep {s : ExecState} {fid : FuncId}
    {args : List GoValue} {mk mk' : Func → LocalEnv → List Loc → Config}
    {k : Cont} {ch : Choices}
    (hmk : ∀ f e ls, mk' f e ls = plugC env' k' (mk f e ls))
    (hmkbar : ∀ f e ls, hasBarrierC (mk f e ls) = true)
    (hb : hasBarrierK k = true) :
    PS env' k' (enterFrameStep s fid args mk k ch)
      (enterFrameStep s fid args mk' (plugK env' k' k) ch) := by
  intro d σ₁ ch₁ h
  unfold GoLean.GoCore.Machine.enterFrameStep at h ⊢
  cases henter : enterFrame s fid args with
  | ok r =>
      obtain ⟨f, e, ls, s'⟩ := r
      rw [henter] at h
      cases h
      refine ⟨?_, Or.inl (hmkbar f e ls)⟩
      simp [hmk]
  | error err =>
      rw [henter] at h
      cases err <;> simp_all
      · -- the entry panic joins at the caller continuation
        obtain ⟨h1, h2, h3⟩ := h
        subst h1; subst h2; subst h3
        exact ⟨by simp [plugC], Or.inl (by simp [hasBarrierC, hb])⟩

/-- Panic-path deferred-call frame entry commutes (the drain arm). -/
theorem PS.enterFrameDeferPanicking {s : ExecState} {fid : FuncId}
    {args : List GoValue} {mk mk' : Func → LocalEnv → Config}
    {chain : List PanicEntry} {krest : Cont} {ch : Choices}
    (hmk : ∀ f e, mk' f e = plugC env' k' (mk f e))
    (hmkbar : ∀ f e, hasBarrierC (mk f e) = true)
    (hb : hasBarrierK krest = true) :
    PS env' k' (enterFrameDeferPanicking s fid args mk chain krest ch)
      (enterFrameDeferPanicking s fid args mk' chain
        (plugK env' k' krest) ch) := by
  intro d σ₁ ch₁ h
  unfold GoLean.GoCore.Machine.enterFrameDeferPanicking at h ⊢
  cases henter : enterFrame s fid args with
  | ok r =>
      obtain ⟨f, e, ls, s'⟩ := r
      rw [henter] at h
      cases h
      refine ⟨?_, Or.inl (hmkbar f e)⟩
      simp [hmk]
  | error err =>
      rw [henter] at h
      cases err <;> simp_all
      · obtain ⟨h1, h2, h3⟩ := h
        subst h1; subst h2; subst h3
        exact ⟨by simp [plugC], Or.inl (by simp [hasBarrierC, hb])⟩


/-! ## Catch-all entry lemmas (the wide/strict/chan/sync entry arms sit
under catch-all match scrutinees — StepSim's pattern, reproduced since
those helpers are private there) -/

private def wideEntryP (σ₀ : ExecState) (op : StmtOp) (nt : Nat)
    (es : List Expr) (env : LocalEnv) (k : Cont) (ch : Choices) :
    Except GoError (Config × ExecState × Choices) :=
  match es with
  | e :: rest => pure (.evalE e env (.stmtOpK op nt [] rest env k), σ₀, ch)
  | [] => do
      let (s', choices') ← applyStmtOp σ₀ ch op nt []
      pure (.next k, s', choices')

private theorem stepFn_exec_wideP {σ₀ : ExecState} {s : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} {op : StmtOp} {nt : Nat}
    {es : List Expr} (hplan : stmtPlan s = some (op, nt, es)) :
    stepFn σ₀ (.exec s env k) ch = wideEntryP σ₀ op nt es env k ch := by
  cases s <;>
    first
      | (simp [stmtPlan] at hplan; done)
      | (simp only [stepFn.eq_def]
         rw [hplan]
         cases es <;> rfl)

private def strictEntryP (σ₀ : ExecState) (op : StrictOp) (es : List Expr)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    Except GoError (Config × ExecState × Choices) :=
  match es with
  | e₁ :: rest => pure (.evalE e₁ env (.strictK op [] rest env k), σ₀, ch)
  | [] =>
      match applyStrictOp σ₀ op [] with
      | .ok (v, s') => pure (.retV v k, s', ch)
      | .error (.panic msg) =>
          pure (.panicking [⟨runtimeErrorValue msg, false⟩] k, σ₀, ch)
      | .error err => throw err

private theorem stepFn_evalE_strictP {σ₀ : ExecState} {e : Expr}
    {env : LocalEnv} {k : Cont} {ch : Choices} {op : StrictOp}
    {es : List Expr} (hplan : strictPlan e = some (op, es)) :
    stepFn σ₀ (.evalE e env k) ch = strictEntryP σ₀ op es env k ch := by
  cases e <;>
    first
      | (simp [strictPlan] at hplan; done)
      | (simp only [stepFn.eq_def]
         rw [hplan]
         cases es <;> rfl)

private theorem stepFn_exec_chanRecvP {σ₀ : ExecState}
    {targets : Array Assignee} {chE : Expr} {elem : Ty} {env : LocalEnv}
    {k : Cont} {ch : Choices} {op : ChanStOp} {e : Expr} {rest : List Expr}
    (hplan : chanPlan (.chanRecv targets chE elem) = some (op, e :: rest)) :
    stepFn σ₀ (.exec (.chanRecv targets chE elem) env k) ch
      = pure (.evalE e env (.chanStK op [] rest env k), σ₀, ch) := by
  simp only [stepFn.eq_def]
  split
  · rename_i op' e' rest' heq
    rw [hplan] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨hop, he, hrest⟩ := heq
    subst hop; subst he; subst hrest
    rfl
  · rename_i heq
    rw [hplan] at heq
    simp at heq
  · rename_i heq
    rw [hplan] at heq
    simp at heq

private theorem stepFn_exec_syncP {σ₀ : ExecState} {sop : SyncStmtOp}
    {args : Array Expr} {targets : Array Assignee} {env : LocalEnv}
    {k : Cont} {ch : Choices} {op : SyncOp} {e : Expr} {rest : List Expr}
    (hplan : syncPlan (.syncStmt sop args targets) = some (op, e :: rest)) :
    stepFn σ₀ (.exec (.syncStmt sop args targets) env k) ch
      = pure (.evalE e env (.syncStK op [] rest env k), σ₀, ch) := by
  simp only [stepFn.eq_def]
  split
  · rename_i op' e' rest' heq
    rw [hplan] at heq
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨hop, he, hrest⟩ := heq
    subst hop; subst he; subst hrest
    rfl
  · rename_i heq
    rw [hplan] at heq
    simp at heq
  · rename_i heq
    rw [hplan] at heq
    simp at heq


/-! ## Local preservation helpers for the walk's classification -/

private theorem hasBarrierK_frame_ds {t : List (TargetShape × List Expr)}
    {te te₂ : LocalEnv} {r r₂ : List Loc}
    {ds ds₂ : List (GoValue × List GoValue)} {k : Cont} {w : Bool} :
    hasBarrierK (.frame t te r ds k w) = hasBarrierK (.frame t te₂ r₂ ds₂ k w) := by
  cases t <;> cases w <;> cases k <;> rfl

private theorem hasBarrierK_seqCont (ss : List Stmt) (env : LocalEnv)
    (k : Cont) : hasBarrierK (seqCont ss env k) = hasBarrierK k := by
  cases k
  case seq rest env₂ k₂ =>
      by_cases henv : env₂ = env <;> simp [seqCont, henv, hasBarrierK]
  all_goals rfl

private theorem hasBarrierK_pushDefer {d : GoValue × List GoValue} :
    ∀ {k k₂ : Cont}, pushDefer d k = some k₂ →
      hasBarrierK k₂ = hasBarrierK k := by
  intro k
  induction k <;> intro k₂ hp
  all_goals
    first
    | (simp only [pushDefer, Option.some.injEq] at hp
       rw [← hp]
       exact hasBarrierK_frame_ds)
    | (rename_i k₃ ih
       simp only [pushDefer] at hp
       revert hp
       cases hpd : pushDefer d k₃ <;> intro hp
       · simp at hp
       · simp only [Option.map_some, Option.some.injEq] at hp
         rw [← hp]
         simp only [hasBarrierK]
         exact ih hpd)
    | (simp [pushDefer] at hp)

private theorem rtw_bar :
    ∀ {k : Cont} {v : GoValue} {k₃ : Cont}, hasBarrierK k = true →
      recoverThroughWrappers k = some (v, k₃) → hasBarrierK k₃ = true := by
  intro k
  induction k <;> intro v k₃ hb hpr
  case stop => simp [recoverThroughWrappers] at hpr
  case panicResumeK chain k₂ _ =>
      simp only [recoverThroughWrappers] at hpr
      cases hm : markNewestRecovered chain <;> rw [hm] at hpr
      · simp at hpr
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpr
        rw [← hpr.2]
        simpa [hasBarrierK] using hb
  case frame t te r ds k₂ w ih =>
      cases w with
      | false => simp [recoverThroughWrappers] at hpr
      | true =>
          have hb₂ : hasBarrierK k₂ = true := by
            rwa [hasBarrierK_frame_of_ne (by simp)] at hb
          simp only [recoverThroughWrappers] at hpr
          cases hm : recoverThroughWrappers k₂ <;> rw [hm] at hpr
          · simp at hpr
          · rename_i p; obtain ⟨v₂, k₄⟩ := p
            simp only [Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hpr
            rw [← hpr.2]
            exact hasBarrierK_frame_of_tail (ih hb₂ hm)
  all_goals
    rename_i k₂ ih
    simp only [hasBarrierK] at hb
    simp only [recoverThroughWrappers] at hpr
    cases hm : recoverThroughWrappers k₂ <;> rw [hm] at hpr
    · simp at hpr
    · rename_i p; obtain ⟨v₂, k₄⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpr
      rw [← hpr.2]
      simp only [hasBarrierK]
      exact ih hb hm

private theorem recoverResult_bar :
    ∀ {k : Cont}, hasBarrierK k = true →
      hasBarrierK (recoverResult k).2 = true := by
  intro k
  induction k <;> intro hb
  case stop => simp [hasBarrierK] at hb
  case panicResumeK chain k₂ _ => simpa [recoverResult, hasBarrierK] using hb
  case frame t te r ds k₂ w ih =>
      cases w with
      | false =>
          simp only [recoverResult]
          cases hm : recoverThroughWrappers k₂
          · simpa using hb
          · rename_i p; obtain ⟨v, k₃⟩ := p
            by_cases hb2 : t = [] ∧ k₂ = .stop
            · obtain ⟨h1, h2⟩ := hb2; subst h1; subst h2
              simp [recoverThroughWrappers] at hm
            · have hne : ¬ (t = [] ∧ k₂ = .stop ∧ (false : Bool) = false) :=
                fun h => hb2 ⟨h.1, h.2.1⟩
              have hb₂ : hasBarrierK k₂ = true := by
                rwa [hasBarrierK_frame_of_ne hne] at hb
              simp only []
              exact hasBarrierK_frame_of_tail (rtw_bar hb₂ hm)
      | true =>
          have hb₂ : hasBarrierK k₂ = true := by
            rwa [hasBarrierK_frame_of_ne (by simp)] at hb
          simp only [recoverResult]
          exact hasBarrierK_frame_of_tail (ih hb₂)
  all_goals
    rename_i k₂ ih
    simp only [hasBarrierK] at hb
    simp only [recoverResult, hasBarrierK]
    exact ih hb

/-! ## The walk -/

set_option maxHeartbeats 6400000 in
/-- **THE PER-STEP PLUG COMMUTATION** (design note §7): on a
barrier-carrying configuration, under the two context premises, the
machine step commutes with `plugC`, and the result keeps the barrier,
exits, or is the crossed panic shape. -/
theorem stepFn_plug
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    {σ : ExecState} {c : Config} {ch : Choices}
    (hbar : hasBarrierC c = true) :
    PS env' k' (stepFn σ c ch) (stepFn σ (plugC env' k' c) ch) := by
  fun_cases stepFn σ c ch
  all_goals first
    | exact PS.err
    | exact PS.throw
    | (simp only [hasBarrierC, hasBarrierK] at hbar; done)
    | ((refine PS.pure ?_ (Or.inl ?_) <;>
        simp_all [stepFn, plugC, plugK, hasBarrierC, hasBarrierK,
          seqCont_plug, contHeadLabel_plug, pushDefer_plug,
          panicPassthrough_plug, recoverResult_plug,
          contAfterStmtOp_plug, contAfterStmtOp_bar,
          applyChanOp_plug, applyChanOp_bar,
          applySyncOp_plug, applySyncOp_bar,
          applySelect_plug, applySelect_bar,
          enterRecvTargets_plug, enterRecvTargets_bar,
          commitClause_plug,
          plugK_frame_of_bar, hasBarrierK_frame_of_tail,
          Except.map, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none]); done)
    | skip
  -- ROUND 2: value-bind arms
  case case66 =>
    rename_i env k id loc hlook
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hload : loadLoc σ loc <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · simp only [bind, Except.bind, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2
      subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩ <;>
        simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none, Except.map,
          contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
          applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
          seqCont_plug, pushDefer_plug,
          hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
          applyChanOp_bar, applySyncOp_bar, applySelect_bar,
          enterRecvTargets_bar, hasBarrierK_pushDefer,
          hasBarrierK_seqCont, recoverResult_bar]
  case case13 =>
    rename_i env k decls ss
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases halloc : allocDecls env.pushScope σ decls.toList <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i pr
      obtain ⟨env2, σ2⟩ := pr
      simp only [bind, Except.bind, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2
      subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩ <;>
        simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none, Except.map,
          contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
          applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
          seqCont_plug, pushDefer_plug,
          hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
          applyChanOp_bar, applySyncOp_bar, applySelect_bar,
          enterRecvTargets_bar, hasBarrierK_pushDefer,
          hasBarrierK_seqCont, recoverResult_bar]
  case case14 =>
    rename_i p rest kenv k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hdv : defaultValue σ p.typ <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · simp only [bind, Except.bind, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2
      subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩ <;>
        simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none, Except.map,
          contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
          applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
          seqCont_plug, pushDefer_plug,
          hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
          applyChanOp_bar, applySyncOp_bar, applySelect_bar,
          enterRecvTargets_bar, hasBarrierK_pushDefer,
          hasBarrierK_seqCont, recoverResult_bar]
  case case87 =>
    rename_i v r env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hvb : valueAsBool v <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i b
      cases b
      all_goals
        simp [bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2.1, ← h.2.2]
        refine ⟨?_, Or.inl ?_⟩ <;>
          simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
            Option.map_some, Option.map_none, Except.map,
            contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
            applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
            seqCont_plug, pushDefer_plug,
            hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
            applyChanOp_bar, applySyncOp_bar, applySelect_bar,
            enterRecvTargets_bar, hasBarrierK_pushDefer,
            hasBarrierK_seqCont, recoverResult_bar]
  case case88 =>
    rename_i v r env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hvb : valueAsBool v <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i b
      cases b
      all_goals
        simp [bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2.1, ← h.2.2]
        refine ⟨?_, Or.inl ?_⟩ <;>
          simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
            Option.map_some, Option.map_none, Except.map,
            contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
            applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
            seqCont_plug, pushDefer_plug,
            hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
            applyChanOp_bar, applySyncOp_bar, applySelect_bar,
            enterRecvTargets_bar, hasBarrierK_pushDefer,
            hasBarrierK_seqCont, recoverResult_bar]
  case case89 =>
    rename_i v k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hvb : valueAsBool v <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · simp only [bind, Except.bind, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2
      subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩ <;>
        simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none, Except.map,
          contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
          applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
          seqCont_plug, pushDefer_plug,
          hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
          applyChanOp_bar, applySyncOp_bar, applySelect_bar,
          enterRecvTargets_bar, hasBarrierK_pushDefer,
          hasBarrierK_seqCont, recoverResult_bar]
  case case90 =>
    rename_i v t e env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hvb : valueAsBool v <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i b
      cases b
      all_goals
        simp [bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2.1, ← h.2.2]
        refine ⟨?_, Or.inl ?_⟩ <;>
          simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
            Option.map_some, Option.map_none, Except.map,
            contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
            applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
            seqCont_plug, pushDefer_plug,
            hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
            applyChanOp_bar, applySyncOp_bar, applySelect_bar,
            enterRecvTargets_bar, hasBarrierK_pushDefer,
            hasBarrierK_seqCont, recoverResult_bar]
  case case91 =>
    rename_i v c2 b2 env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hvb : valueAsBool v <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i b
      cases b
      all_goals
        simp [bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2.1, ← h.2.2]
        refine ⟨?_, Or.inl ?_⟩ <;>
          simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
            Option.map_some, Option.map_none, Except.map,
            contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
            applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
            seqCont_plug, pushDefer_plug,
            hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
            applyChanOp_bar, applySyncOp_bar, applySelect_bar,
            enterRecvTargets_bar, hasBarrierK_pushDefer,
            hasBarrierK_seqCont, recoverResult_bar]
  case case98 =>
    rename_i v op nt done env k2 s2 choices2 happ
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hca : contAfterStmtOp s2 op ((v :: done).reverse) k2 <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i k3
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.1, ← h.2.1, ← h.2.2]
      refine ⟨?_, Or.inl ?_⟩
      · simp_all [plugC, plugK, stepFn, contAfterStmtOp_plug, hca, happ,
          Except.map, bind, Except.bind, pure, Except.pure]
      · rw [hasBarrierC, contAfterStmtOp_bar hca]
        exact hb
  case case111 =>
    rename_i v env k2 hdef k3 hpush
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    refine PS.pure ?_ (Or.inl ?_)
    · simp [plugC, plugK, stepFn, pushDefer_plug hb, hpush, hdef]
    · rw [hasBarrierC, hasBarrierK_pushDefer hpush]
      exact hb
  case case115 =>
    rename_i v cv vals env k2 k3 hpush
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    refine PS.pure ?_ (Or.inl ?_)
    · simp [plugC, plugK, stepFn, pushDefer_plug hb, hpush]
    · rw [hasBarrierC, hasBarrierK_pushDefer hpush]
      exact hb
  case case117 =>
    rename_i v keyVar valVar keyTy valTy body env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hbs : mapRangeStartSets σ v <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i bs
      obtain ⟨b1, b2⟩ := bs
      simp only [bind, Except.bind, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2
      subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩ <;>
        simp_all [plugC, plugK, stepFn, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none, Except.map,
          contAfterStmtOp_plug, applyChanOp_plug, applySyncOp_plug,
          applySelect_plug, enterRecvTargets_plug, recoverResult_plug,
          seqCont_plug, pushDefer_plug,
          hasBarrierC, hasBarrierK, contAfterStmtOp_bar,
          applyChanOp_bar, applySyncOp_bar, applySelect_bar,
          enterRecvTargets_bar, hasBarrierK_pushDefer,
          hasBarrierK_seqCont, recoverResult_bar]
  case case120 =>
    rename_i v op done env k2 c2 s2 happ
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    rw [List.reverse_cons] at happ
    refine PS.pure ?_ (Or.inl (applyChanOp_bar happ hb))
    simp [plugC, plugK, stepFn, applyChanOp_plug, happ, Except.map]
  case case143 =>
    rename_i v op done env k2 c2 s2 happ
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    rw [List.reverse_cons] at happ
    refine PS.pure ?_ (Or.inl (applySyncOp_bar happ hb))
    simp [plugC, plugK, stepFn, applySyncOp_plug, happ, Except.map]
  case case124 =>
    rename_i v clauses default? done env k2 c2 s2 choices2 cl2 happ
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    rw [List.reverse_cons] at happ
    refine PS.pure ?_ (Or.inl (applySelect_bar happ hb))
    simp [plugC, plugK, stepFn, applySelect_plug, happ, Except.map]
  -- ROUND 3: frame entries, catch-alls, recover, mapIter pick
  case case3 =>
    rename_i chain t te r args ds k2 w fid captured
    have hb : hasBarrierK (.frame t te r ds k2 w) = true := by
      simp only [hasBarrierC] at hbar
      rwa [show hasBarrierK
          (.frame t te r ((GoValue.funcVal fid captured, args) :: ds) k2 w)
          = hasBarrierK (.frame t te r ds k2 w) from hasBarrierK_frame_ds]
        at hbar
    have hred : stepFn σ (plugC env' k' (.panicking chain
        (.frame t te r ((.funcVal fid captured, args) :: ds) k2 w))) ch
        = enterFrameDeferPanicking σ fid (captured ++ args)
            (fun func frameEnv => .exec func.body frameEnv
              (.frame [] [] [] [] (.panicResumeK chain
                (plugK env' k' (.frame t te r ds k2 w))) func.wrapper))
            chain (plugK env' k' (.frame t te r ds k2 w)) ch := by
      by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        rfl
      · simp [plugC, plugK_frame_of_ne hb2, stepFn]
    rw [hred]
    refine PS.enterFrameDeferPanicking (fun f e => ?_) (fun f e => ?_) hb
    · simp [plugC, plugK]
    · simp only [hasBarrierC]
      exact hasBarrierK_frame_of_tail (by simpa [hasBarrierK] using hb)
  case case156 =>
    rename_i t te r args ds k2 w fid captured
    have hb : hasBarrierK (.frame t te r ds k2 w) = true := by
      simp only [hasBarrierC] at hbar
      rwa [show hasBarrierK
          (.frame t te r ((GoValue.funcVal fid captured, args) :: ds) k2 w)
          = hasBarrierK (.frame t te r ds k2 w) from hasBarrierK_frame_ds]
        at hbar
    have hred : stepFn σ (plugC env' k' (.next
        (.frame t te r ((.funcVal fid captured, args) :: ds) k2 w))) ch
        = enterFrameStep σ fid (captured ++ args)
            (fun func frameEnv _ => .exec func.body frameEnv
              (.frame [] [] [] []
                (plugK env' k' (.frame t te r ds k2 w)) func.wrapper))
            (plugK env' k' (.frame t te r ds k2 w)) ch := by
      by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        simp [plugC, plugK, stepFn]
      · simp [plugC, plugK_frame_of_ne hb2, stepFn]
    rw [hred]
    refine PS.enterFrameStep (fun f e ls => ?_) (fun f e ls => ?_) hb
    · simp [plugC, plugK]
    · simp only [hasBarrierC]
      exact hasBarrierK_frame_of_tail hb
  case case195 =>
    rename_i t te r args ds k2 w fid captured
    have hb : hasBarrierK (.frame t te r ds k2 w) = true := by
      simp only [hasBarrierC] at hbar
      rwa [show hasBarrierK
          (.frame t te r ((GoValue.funcVal fid captured, args) :: ds) k2 w)
          = hasBarrierK (.frame t te r ds k2 w) from hasBarrierK_frame_ds]
        at hbar
    have hred : stepFn σ (plugC env' k' (.returning
        (.frame t te r ((.funcVal fid captured, args) :: ds) k2 w))) ch
        = enterFrameStep σ fid (captured ++ args)
            (fun func frameEnv _ => .exec func.body frameEnv
              (.frame [] [] [] []
                (plugK env' k' (.frame t te r ds k2 w)) func.wrapper))
            (plugK env' k' (.frame t te r ds k2 w)) ch := by
      by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        simp [plugC, plugK, stepFn]
      · simp [plugC, plugK_frame_of_ne hb2, stepFn]
    rw [hred]
    refine PS.enterFrameStep (fun f e ls => ?_) (fun f e ls => ?_) hb
    · simp [plugC, plugK]
    · simp only [hasBarrierC]
      exact hasBarrierK_frame_of_tail hb
  case case10 =>
    rename_i chain k h4 h3 h2 h1 k2 hpass
    cases k
    case stop => exact absurd rfl h1
    case panicResumeK a b => exact absurd rfl (h2 _ _)
    case frame t te r ds k3 w =>
        cases ds with
        | nil => exact absurd rfl (h4 _ _ _ _ _)
        | cons dd ds2 =>
            obtain ⟨cv, av⟩ := dd
            exact absurd rfl (h3 _ _ _ _ _ _ _ _)
    all_goals
      simp only [panicPassthrough, Option.some.injEq] at hpass
      subst hpass
      refine PS.pure ?_ (Or.inl ?_) <;>
        simp_all [stepFn, plugC, plugK, hasBarrierC, hasBarrierK,
          panicPassthrough]
  case case36 =>
    rename_i env k targets fid args plans hplan hargs
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    have hred : stepFn σ (plugC env' k'
        (.exec (.call targets fid args) env k)) ch
        = enterFrameStep σ fid []
            (fun func fe rls => .exec func.body fe
              (.frame plans env rls [] (plugK env' k' k) func.wrapper))
            (plugK env' k' k) ch := by
      simp only [plugC]
      simp only [stepFn.eq_def]
      rw [hplan, hargs]
    rw [hred]
    refine PS.enterFrameStep (fun f e ls => ?_) (fun f e ls => ?_) hb
    · simp [plugC, plugK_frame_of_bar hb]
    · simp [hasBarrierC, hasBarrierK_frame_of_tail hb]
  case case93 =>
    rename_i v fid plans vals env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    have hred : stepFn σ (plugC env' k'
        (.retV v (.callArgsK fid plans vals [] env k2))) ch
        = enterFrameStep σ fid (vals ++ [v])
            (fun func fe rls => .exec func.body fe
              (.frame plans env rls [] (plugK env' k' k2) func.wrapper))
            (plugK env' k' k2) ch := rfl
    rw [hred]
    refine PS.enterFrameStep (fun f e ls => ?_) (fun f e ls => ?_) hb
    · simp [plugC, plugK_frame_of_bar hb]
    · simp [hasBarrierC, hasBarrierK_frame_of_tail hb]
  case case101 =>
    rename_i plans env k2 fid captured
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    have hred : stepFn σ (plugC env' k'
        (.retV (.funcVal fid captured) (.callValCalleeK plans [] env k2))) ch
        = enterFrameStep σ fid captured
            (fun func fe rls => .exec func.body fe
              (.frame plans env rls [] (plugK env' k' k2) func.wrapper))
            (plugK env' k' k2) ch := rfl
    rw [hred]
    refine PS.enterFrameStep (fun f e ls => ?_) (fun f e ls => ?_) hb
    · simp [plugC, plugK_frame_of_bar hb]
    · simp [hasBarrierC, hasBarrierK_frame_of_tail hb]
  case case107 =>
    rename_i v plans vals env k2 fid captured
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    have hred : stepFn σ (plugC env' k'
        (.retV v (.callValArgsK (.funcVal fid captured) plans vals []
          env k2))) ch
        = enterFrameStep σ fid (captured ++ vals ++ [v])
            (fun func fe rls => .exec func.body fe
              (.frame plans env rls [] (plugK env' k' k2) func.wrapper))
            (plugK env' k' k2) ch := rfl
    rw [hred]
    refine PS.enterFrameStep (fun f e ls => ?_) (fun f e ls => ?_) hb
    · simp [plugC, plugK_frame_of_bar hb]
    · simp [hasBarrierC, hasBarrierK_frame_of_tail hb]
  case case41 =>
    rename_i env k targets chE elem op e rest hplan
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hasBarrierK, hb]))
    show stepFn σ (.exec (.chanRecv targets chE elem) env
        (plugK env' k' k)) ch = _
    rw [stepFn_exec_chanRecvP hplan]
    simp [plugC, plugK]
  case case60 =>
    rename_i env k op args targets sop e rest hplan
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hasBarrierK, hb]))
    show stepFn σ (.exec (.syncStmt op args targets) env
        (plugK env' k' k)) ch = _
    rw [stepFn_exec_syncP hplan]
    simp [plugC, plugK]
  case case64 =>
    rename_i op nt hplan
    intro d σ₁ ch₁ h
    revert h
    cases happ : applyStmtOp σ ch op nt [] <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i pr
      obtain ⟨s2, ch2⟩ := pr
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.1, ← h.2.1, ← h.2.2]
      refine ⟨?_, Or.inl ?_⟩
      · simp only [plugC]
        rw [stepFn_exec_wideP hplan]
        simp [wideEntryP, happ, bind, Except.bind, pure, Except.pure,
          plugC, plugK]
      · simp_all [hasBarrierC, hasBarrierK]
  case case76 =>
    rename_i env k v k2 hrec
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    have hplugrec := recoverResult_plug (env' := env') (k' := k') hb hrc
    refine PS.pure ?_ (Or.inl ?_)
    · simp [plugC, plugK, stepFn, hplugrec, hrec]
    · have hpres := recoverResult_bar (k := k) hb
      rw [hrec] at hpres
      simpa [hasBarrierC, hasBarrierK] using hpres
  case case97 =>
    rename_i v op nt done env k2 a rest hlt
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hasBarrierK, hb]))
    simp [plugC, plugK, stepFn, if_neg hlt]
  case case163 =>
    rename_i keyVar valVar keyTy valTy body base produced start env k2
    have hb : hasBarrierK k2 = true := by
      simpa [hasBarrierC, hasBarrierK] using hbar
    intro d σ₁ ch₁ h
    revert h
    cases hcands : mapIterCandidates σ keyTy valTy base produced <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i cands
      simp only [bind, Except.bind] at h
      split at h
      · rename_i hemp
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2.1, ← h.2.2]
        refine ⟨?_, Or.inl (by simp [hasBarrierC, hasBarrierK, hb])⟩
        simp [plugC, plugK, stepFn, hcands, hemp, bind, Except.bind,
          pure, Except.pure]
      · rename_i hemp
        revert h
        cases hmand : mapIterMandatoryRemains σ keyTy cands start <;> intro h
        · exact absurd h (by simp [bind, Except.bind])
        · rename_i mand
          simp only [bind, Except.bind] at h
          cases hpair : Choices.consumeAt .mapIter
              (cands.size + if mand = true then 0 else 1) ch with
          | mk idx ch2 =>
            rw [hpair] at h
            revert h
            cases hidx : cands[idx]? <;> intro h
            · simp only [pure, Except.pure, Except.ok.injEq,
                Prod.mk.injEq] at h
              rw [← h.1, ← h.2.1, ← h.2.2]
              refine ⟨?_, Or.inl (by simp [hasBarrierC, hasBarrierK, hb])⟩
              simp [plugC, plugK, stepFn, hcands, hemp, hmand, hpair, hidx,
                bind, Except.bind, pure, Except.pure]
            · rename_i kv2
              obtain ⟨key, value⟩ := kv2
              revert h
              cases hbind : bindIterVars env.pushScope σ keyVar valVar
                  keyTy valTy key value <;> intro h
              · exact absurd h (by simp [hbind, bind, Except.bind])
              · rename_i pr2
                obtain ⟨env2, s2⟩ := pr2
                simp only [hbind, bind, Except.bind, pure, Except.pure,
                  Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.1, ← h.2.1, ← h.2.2]
                refine ⟨?_, Or.inl (by simp [hasBarrierC, hasBarrierK, hb])⟩
                simp [plugC, plugK, stepFn, hcands, hemp, hmand, hpair,
                  hidx, hbind, bind, Except.bind, pure, Except.pure]
  -- ROUND 1: the frame-headed arms (barrier splits)
  case case2 =>
    rename_i chain t te r k2 w
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      refine PS.pure ?_ (Or.inr (Or.inr ⟨chain, rfl⟩))
      simp [plugC, plugK, stepFn]
    · have hb : hasBarrierK k2 = true := by
        simp only [hasBarrierC] at hbar
        rwa [hasBarrierK_frame_of_ne hb2] at hbar
      refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hb]))
      simp [plugC, plugK_frame_of_ne hb2, stepFn]
  case case4 =>
    rename_i chain t te r args ds k2 w
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hasBarrierK]))
      simp [plugC, plugK, stepFn]
    · have hb : hasBarrierK k2 = true := by
        simp only [hasBarrierC] at hbar
        rwa [hasBarrierK_frame_of_ne hb2] at hbar
      refine PS.pure ?_
        (Or.inl (by simp [hasBarrierC, hasBarrierK_frame_of_ne hb2, hb]))
      simp [plugC, plugK_frame_of_ne hb2, stepFn]
  case case157 =>
    rename_i t te r args ds k2 w
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hasBarrierK]))
      simp [plugC, plugK, stepFn]
    · have hb : hasBarrierK k2 = true := by
        simp only [hasBarrierC] at hbar
        rwa [hasBarrierK_frame_of_ne hb2] at hbar
      refine PS.pure ?_
        (Or.inl (by simp [hasBarrierC, hasBarrierK_frame_of_ne hb2, hb]))
      simp [plugC, plugK_frame_of_ne hb2, stepFn]
  case case196 =>
    rename_i t te r args ds k2 w
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hasBarrierK]))
      simp [plugC, plugK, stepFn]
    · have hb : hasBarrierK k2 = true := by
        simp only [hasBarrierC] at hbar
        rwa [hasBarrierK_frame_of_ne hb2] at hbar
      refine PS.pure ?_
        (Or.inl (by simp [hasBarrierC, hasBarrierK_frame_of_ne hb2, hb]))
      simp [plugC, plugK_frame_of_ne hb2, stepFn]
  case case152 =>
    rename_i te k2 w
    by_cases hb2 : k2 = .stop ∧ w = false
    · obtain ⟨h1, h2⟩ := hb2; subst h1; subst h2
      refine PS.pure ?_ (Or.inr (Or.inl rfl))
      simp [plugC, plugK, stepFn]
    · have hne : ¬ (([] : List (TargetShape × List Expr)) = []
          ∧ k2 = .stop ∧ w = false) := fun h => hb2 ⟨h.2.1, h.2.2⟩
      have hb : hasBarrierK k2 = true := by
        simp only [hasBarrierC] at hbar
        rwa [hasBarrierK_frame_of_ne hne] at hbar
      refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hb]))
      simp [plugC, plugK_frame_of_ne hne, stepFn]
  case case191 =>
    rename_i te k2 w
    by_cases hb2 : k2 = .stop ∧ w = false
    · obtain ⟨h1, h2⟩ := hb2; subst h1; subst h2
      refine PS.pure ?_ (Or.inr (Or.inl rfl))
      simp [plugC, plugK, stepFn]
    · have hne : ¬ (([] : List (TargetShape × List Expr)) = []
          ∧ k2 = .stop ∧ w = false) := fun h => hb2 ⟨h.2.1, h.2.2⟩
      have hb : hasBarrierK k2 = true := by
        simp only [hasBarrierC] at hbar
        rwa [hasBarrierK_frame_of_ne hne] at hbar
      refine PS.pure ?_ (Or.inl (by simp [hasBarrierC, hb]))
      simp [plugC, plugK_frame_of_ne hne, stepFn]
  case case153 =>
    rename_i te rl rls k2 w
    intro d σ₁ ch₁ h
    revert h
    cases hlm : loadMany σ (rl :: rls) <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · exact absurd h (by simp [bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw])
  case case192 =>
    rename_i te rl rls k2 w
    intro d σ₁ ch₁ h
    revert h
    cases hlm : loadMany σ (rl :: rls) <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · exact absurd h (by simp [bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw])
  case case154 =>
    rename_i sh e ops rest te results k2 w
    have hne : ¬ (((sh, e :: ops) :: rest) = []
        ∧ k2 = .stop ∧ w = false) := by simp
    have hb : hasBarrierK k2 = true := by
      simp only [hasBarrierC] at hbar
      rwa [hasBarrierK_frame_of_ne hne] at hbar
    intro d σ₁ ch₁ h
    revert h
    cases hlm : loadMany σ results <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i vs
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2; subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩
      · simp [plugC, plugK_frame_of_ne hne, stepFn, hlm, bind, Except.bind,
          plugK, pure, Except.pure]
      · simp [hasBarrierC, hasBarrierK, hb]
  case case193 =>
    rename_i sh e ops rest te results k2 w
    have hne : ¬ (((sh, e :: ops) :: rest) = []
        ∧ k2 = .stop ∧ w = false) := by simp
    have hb : hasBarrierK k2 = true := by
      simp only [hasBarrierC] at hbar
      rwa [hasBarrierK_frame_of_ne hne] at hbar
    intro d σ₁ ch₁ h
    revert h
    cases hlm : loadMany σ results <;> intro h
    · exact absurd h (by simp [bind, Except.bind])
    · rename_i vs
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2; subst h3
      rw [← h1]
      refine ⟨?_, Or.inl ?_⟩
      · simp [plugC, plugK_frame_of_ne hne, stepFn, hlm, bind, Except.bind,
          plugK, pure, Except.pure]
      · simp [hasBarrierC, hasBarrierK, hb]
  case case12 =>
    rename_i env k ss
    have hb : hasBarrierK k = true := by simpa [hasBarrierC] using hbar
    refine PS.pure ?_ (Or.inl ?_)
    · simp [plugC, plugK, stepFn, seqCont_plug hb]
    · simp [hasBarrierC, hasBarrierK_seqCont, hb]
end GoLean.Frame
