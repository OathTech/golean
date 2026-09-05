import GoLean.GoCore.MachineSound

/-! Exact, choice-threaded prefixes of the CURRENT executable step.
This is a proof carrier, not another executable interpreter. Erasing the
stream yields `Steps`; the reverse erasure needs a composition theorem.
-/
namespace GoLean.GateA1
open GoCore GoCore.Machine

inductive Trace : Nat → ExecState → Config → Choices →
    ExecState → Config → Choices → Prop where
  | done : Trace 0 s c ch s c ch
  | step : stepFn s c ch = .ok (c₁, s₁, ch₁) →
      Trace n s₁ c₁ ch₁ sf cf chf → Trace (n + 1) s c ch sf cf chf

theorem iter_iff_trace {n s c ch sf cf chf} :
    stepFnIter n s c ch = .ok (cf, sf, chf) ↔ Trace n s c ch sf cf chf := by
  induction n generalizing s c ch with
  | zero =>
    simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact .done
    · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    constructor
    · intro h
      cases hs : stepFn s c ch with
      | error e => simp [stepFnIter, hs, Bind.bind, Except.bind] at h
      | ok v =>
        obtain ⟨c₁, s₁, ch₁⟩ := v
        exact .step hs (ih.mp (by simpa [stepFnIter, hs, Bind.bind, Except.bind] using h))
    · intro h
      cases h with
      | step hs ht => simpa [stepFnIter, hs, Bind.bind, Except.bind] using ih.mpr ht

theorem Trace.erase (h : Trace n s c ch sf cf chf) : Steps c s cf sf := by
  induction h with
  | done => exact .refl _ _
  | step hs _ ih => exact (Steps.single (stepFn_sound hs)).trans ih

theorem exists_iter_iff {n s c sf cf} :
    (∃ ch chf, stepFnIter n s c ch = .ok (cf, sf, chf)) ↔
    ∃ ch chf, Trace n s c ch sf cf chf := by
  simp only [iter_iff_trace]

theorem Trace.run (ht : Trace n s c ch sf cf chf) (hdone : cf = .next .stop) :
    execStmtLoop n s c ch = .ok (sf, chf) := by
  induction ht with
  | done => subst hdone; rfl
  | step hs _ ih => rw [execStmtLoop_step hs]; exact ih hdone

/-- Exact successful-run bridge: one FIXED initial stream, its residual,
and a counted trace whose length is bounded by the supplied fuel. -/
theorem run_ok_iff {fuel s c ch sf chf} :
    execStmtLoop fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ Trace n s c ch sf (.next .stop) chf := by
  constructor
  · intro h
    fun_induction execStmtLoop fuel s c ch with
    | case1 =>
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, Nat.zero_le _, .done⟩
    | case2 => simp [throw, throwThe, MonadExceptOf.throw] at h
    | case3 => simp [throw, throwThe, MonadExceptOf.throw] at h
    | case4 => simp [throw, throwThe, MonadExceptOf.throw] at h
    | case5 => simp [throw, throwThe, MonadExceptOf.throw] at h
    | case6 => simp [throw, throwThe, MonadExceptOf.throw] at h
    | case7 =>
      rename_i ih
      rw [bind_eq_ok] at h
      obtain ⟨⟨c₁, s₁, ch₁⟩, hs, hr⟩ := h
      obtain ⟨n, hn, ht⟩ := ih _ _ _ hr
      exact ⟨n + 1, Nat.succ_le_succ hn, .step hs ht⟩
  · rintro ⟨n, hn, ht⟩
    exact execStmtLoop_mono _ _ _ _ _ _ hn (ht.run rfl)

theorem exists_run_ok_iff {s c sf} :
    (∃ fuel ch chf, execStmtLoop fuel s c ch = .ok (sf, chf)) ↔
      ∃ n ch chf, Trace n s c ch sf (.next .stop) chf := by
  constructor
  · rintro ⟨fuel, ch, chf, h⟩
    obtain ⟨n, _, ht⟩ := run_ok_iff.mp h
    exact ⟨n, ch, chf, ht⟩
  · rintro ⟨n, ch, chf, ht⟩
    exact ⟨n, ch, chf, run_ok_iff.mpr ⟨n, Nat.le_refl _, ht⟩⟩

end GoLean.GateA1
