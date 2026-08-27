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

end GoLean.Frame
