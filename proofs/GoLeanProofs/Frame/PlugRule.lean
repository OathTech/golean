import GoLeanProofs.Frame.PlugStep

/-!
# THE PLUG RULE (design note §7-§8): the iterated commutation and the
call-span corollary

`stepFnIter_plug` iterates the per-step walk: a successful
barrier-anchored run commutes with the below-barrier replacement at
the SAME fuel/state/stream, landing at `.next k'`. The crossed panic
shape is refuted from span success (the terminal discipline: once a
panic passes the barrier the canonical run can only abort), and the
exit pins the fuel exactly.

`callSpan_plug` is THE PLUG RULE proper: a successful resultless
call-span at the CANONICAL anchor (caller env `[]`, below-barrier
tail `.stop` — the shape `FrameSim` transport delivers) yields, at
the same fuel/state/stream, the span at ANY caller context
`(env', k')` satisfying the §7 premises (`mapIterFree k'`,
`recoverThroughWrappers k' = none`, non-wrapper callee).

LINEAGE (§7): wp_bind / evaluation-context composition, realized as
certificate-replay-style per-step commutation on the executable
machine.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

variable {env' : LocalEnv} {k' : Cont}

/-- A run from the terminal abort never succeeds. -/
private theorem iter_panicked_no_success :
    ∀ {m : Nat} {σ : ExecState} {msg : String} {ch : Choices}
      {σ' : ExecState} {ch' : Choices},
      stepFnIter m σ (.panicked msg) ch ≠ .ok (.next .stop, σ', ch') := by
  intro m σ msg ch σ' ch'
  cases m with
  | zero => simp [stepFnIter]
  | succ m2 =>
      simp [stepFnIter, stepFn, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw]

/-- A run from the CROSSED panic shape (`.panicking chain .stop`)
never succeeds: it aborts (or is stuck on a malformed chain) — the
terminal discipline behind the walk's third disjunct. -/
private theorem iter_panicking_stop_no_success :
    ∀ {m : Nat} {σ : ExecState} {chain : List PanicEntry} {ch : Choices}
      {σ' : ExecState} {ch' : Choices},
      stepFnIter m σ (.panicking chain .stop) ch
        ≠ .ok (.next .stop, σ', ch') := by
  intro m σ chain ch σ' ch'
  cases m with
  | zero => simp [stepFnIter]
  | succ m2 =>
      simp only [stepFnIter]
      cases chain with
      | nil =>
          simp [stepFn, bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw]
      | cons first rest =>
          cases hrend : renderPanicHead σ first rest with
          | none =>
              simp [stepFn, hrend, bind, Except.bind, throw, throwThe,
                MonadExceptOf.throw]
          | some msg =>
              simp only [stepFn, hrend, bind, Except.bind, pure, Except.pure]
              exact iter_panicked_no_success

/-- A successful run from the exit configuration has zero fuel left
(the iterator throws on terminals — StepFn's discipline). -/
private theorem iter_next_stop_zero :
    ∀ {m : Nat} {σ : ExecState} {ch : Choices} {σ' : ExecState}
      {ch' : Choices},
      stepFnIter m σ (.next .stop) ch = .ok (.next .stop, σ', ch') →
      σ' = σ ∧ ch' = ch := by
  intro m σ ch σ' ch' h
  cases m with
  | zero =>
      simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.2.1.symm, h.2.2.symm⟩
  | succ m2 =>
      simp [stepFnIter, stepFn, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at h

/-- **The iterated plug commutation**: a successful barrier-anchored
run commutes with the below-barrier replacement at the same fuel,
state, and stream. -/
theorem stepFnIter_plug
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none) :
    ∀ {n : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {σ' : ExecState} {ch' : Choices},
      hasBarrierC c = true →
      stepFnIter n σ c ch = .ok (.next .stop, σ', ch') →
      stepFnIter n σ (plugC env' k' c) ch = .ok (.next k', σ', ch') := by
  intro n
  induction n with
  | zero =>
      intro σ c ch σ' ch' hbar hrun
      simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq] at hrun
      rw [hrun.1] at hbar
      simp [hasBarrierC, hasBarrierK] at hbar
  | succ m ih =>
      intro σ c ch σ' ch' hbar hrun
      simp only [stepFnIter] at hrun ⊢
      cases hstep : stepFn σ c ch with
      | error e =>
          rw [hstep] at hrun
          exact absurd hrun (by simp [bind, Except.bind])
      | ok trip =>
          obtain ⟨d, σ₁, ch₁⟩ := trip
          rw [hstep] at hrun
          simp only [bind, Except.bind] at hrun ⊢
          obtain ⟨hplug, hcls⟩ := stepFn_plug hmf hrc hbar hstep
          rw [hplug]
          rcases hcls with hcls | hcls | ⟨chain, hcls⟩
          · exact ih hcls hrun
          · subst hcls
            obtain ⟨hσ, hch⟩ := iter_next_stop_zero hrun
            subst hσ; subst hch
            have hm : m = 0 := by
              cases m with
              | zero => rfl
              | succ m2 =>
                  exfalso
                  revert hrun
                  simp [stepFnIter, stepFn, bind, Except.bind, throw,
                    throwThe, MonadExceptOf.throw]
            subst hm
            simp [stepFnIter, plugC, plugK]
          · subst hcls
            exact absurd hrun iter_panicking_stop_no_success

/-- **THE PLUG RULE** (the frame's control half, §7-§8): a successful
resultless call-span at the canonical anchor — caller env `[]`,
below-barrier tail `.stop`, exactly the shape `FrameSim` transport
delivers — holds at ANY caller context `(env', k')` under the §7
premises, at the same fuel, terminal state, and stream. The
non-wrapper premise is on the ENTERED callee (its frame is the
barrier; a wrapper barrier is transparent to Go's recover walk and is
refused — the sealed posture, §7 premise 3). -/
theorem callSpan_plug
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    {σ σ' : ExecState} {fid : FuncId} {vals : List GoValue} {v : GoValue}
    {n : Nat} {ch ch' : Choices}
    (hnw : ∀ func fenv rls σe,
      enterFrame σ fid (vals ++ [v]) = .ok (func, fenv, rls, σe) →
      func.wrapper = false)
    (hrun : stepFnIter n σ (.retV v (.callArgsK fid [] vals [] [] .stop)) ch
      = .ok (.next .stop, σ', ch')) :
    stepFnIter n σ (.retV v (.callArgsK fid [] vals [] env' k')) ch
      = .ok (.next k', σ', ch') := by
  cases n with
  | zero => simp [stepFnIter] at hrun
  | succ m =>
      simp only [stepFnIter] at hrun ⊢
      cases henter : enterFrame σ fid (vals ++ [v]) with
      | ok r =>
          obtain ⟨func, fenv, rls, σe⟩ := r
          have hwf : func.wrapper = false := hnw _ _ _ _ henter
          have hstep1 : stepFn σ
              (.retV v (.callArgsK fid [] vals [] [] .stop)) ch
              = .ok (.exec func.body fenv
                  (.frame [] [] rls [] .stop func.wrapper), σe, ch) := by
            simp [stepFn, GoLean.GoCore.Machine.enterFrameStep, henter]
          have hstep1' : stepFn σ
              (.retV v (.callArgsK fid [] vals [] env' k')) ch
              = .ok (.exec func.body fenv
                  (.frame [] env' rls [] k' func.wrapper), σe, ch) := by
            simp [stepFn, GoLean.GoCore.Machine.enterFrameStep, henter]
          rw [hstep1] at hrun
          rw [hstep1']
          simp only [bind, Except.bind] at hrun ⊢
          have hbar : hasBarrierC (.exec func.body fenv
              (.frame [] [] rls [] .stop func.wrapper)) = true := by
            simp [hasBarrierC, hwf, hasBarrierK]
          have hres := stepFnIter_plug (env' := env') (k' := k')
            hmf hrc hbar hrun
          simpa [plugC, plugK, hwf] using hres
      | error err =>
          cases err
          case panic msg =>
              have hstep1 : stepFn σ
                  (.retV v (.callArgsK fid [] vals [] [] .stop)) ch
                  = .ok (.panicking [⟨runtimeErrorValue msg, false⟩] .stop,
                      σ, ch) := by
                simp [stepFn, GoLean.GoCore.Machine.enterFrameStep, henter]
              rw [hstep1] at hrun
              simp only [bind, Except.bind] at hrun
              exact absurd hrun iter_panicking_stop_no_success
          all_goals
            revert hrun
            simp [stepFn, GoLean.GoCore.Machine.enterFrameStep, henter,
              bind, Except.bind]

end GoLean.Frame
