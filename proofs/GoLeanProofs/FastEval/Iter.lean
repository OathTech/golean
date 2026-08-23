import GoLeanProofs.FastEval.Ops

/-!
# FastEval — the fast iterator and its transport (campaign Arc 2, U4)

Generic over the per-step function so it lands before `stepFast` does:
`iterF f` is the fuel iterator; `iterF_ok` transports a completed fast
iteration to `stepFnIter` given the per-step one-directional sim;
`iterF_add` is the segment-chaining arithmetic (the fast-space
analogue of the kit's `stepFnIter_chain`). UNTRUSTED METHOD — never in
any statement closure.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- Fuel iteration of a fast step function (mirrors `stepFnIter`). -/
def iterF (f : ExecStateF → Config → Choices →
    Except GoError (Config × ExecStateF × Choices)) :
    Nat → ExecStateF → Config → Choices →
    Except GoError (Config × ExecStateF × Choices)
  | 0, σF, c, ch => .ok (c, σF, ch)
  | n + 1, σF, c, ch => do
      let (c', σF', ch') ← f σF c ch
      iterF f n σF' c' ch'

/-- The transport: a completed fast iteration is a completed
`stepFnIter` at the γ-image, given the per-step sim. -/
theorem iterF_ok {f : ExecStateF → Config → Choices →
      Except GoError (Config × ExecStateF × Choices)}
    (hf : ∀ σF c ch c' σF' ch', f σF c ch = .ok (c', σF', ch') →
      stepFn (γF σF) c ch = .ok (c', γF σF', ch')) :
    ∀ {n : Nat} {σF : ExecStateF} {c : Config} {ch : Choices}
      {c' : Config} {σF' : ExecStateF} {ch' : Choices},
    iterF f n σF c ch = .ok (c', σF', ch') →
    stepFnIter n (γF σF) c ch = .ok (c', γF σF', ch') := by
  intro n
  induction n with
  | zero =>
      intro σF c ch c' σF' ch' h
      simp only [iterF, Except.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | succ n ih =>
      intro σF c ch c' σF' ch' h
      unfold iterF at h
      cases hstep : f σF c ch with
      | error e => rw [hstep] at h; simp [Bind.bind, Except.bind] at h
      | ok r =>
          obtain ⟨c₁, σF₁, ch₁⟩ := r
          rw [hstep] at h
          simp only [Bind.bind, Except.bind] at h
          unfold stepFnIter
          rw [hf _ _ _ _ _ _ hstep]
          simp only [Bind.bind, Except.bind]
          exact ih h

/-- Segment chaining: fast-space fuel arithmetic (the assembly's
composition spine). -/
theorem iterF_add {f : ExecStateF → Config → Choices →
      Except GoError (Config × ExecStateF × Choices)}
    {a b : Nat} {σF : ExecStateF} {c : Config} {ch : Choices}
    {c₁ : Config} {σF₁ : ExecStateF} {ch₁ : Choices}
    {c₂ : Config} {σF₂ : ExecStateF} {ch₂ : Choices}
    (h₁ : iterF f a σF c ch = .ok (c₁, σF₁, ch₁))
    (h₂ : iterF f b σF₁ c₁ ch₁ = .ok (c₂, σF₂, ch₂)) :
    iterF f (a + b) σF c ch = .ok (c₂, σF₂, ch₂) := by
  induction a generalizing σF c ch with
  | zero =>
      simp only [iterF, Except.ok.injEq] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := h₁
      simpa using h₂
  | succ a ih =>
      unfold iterF at h₁
      cases hstep : f σF c ch with
      | error e => rw [hstep] at h₁; simp [Bind.bind, Except.bind] at h₁
      | ok r =>
          obtain ⟨c', σF', ch'⟩ := r
          rw [hstep] at h₁
          simp only [Bind.bind, Except.bind] at h₁
          show iterF f (a + 1 + b) σF c ch = .ok (c₂, σF₂, ch₂)
          have : a + 1 + b = (a + b) + 1 := by omega
          rw [this]
          unfold iterF
          rw [hstep]
          simp only [Bind.bind, Except.bind]
          exact ih h₁

end GoLean.FastEval
