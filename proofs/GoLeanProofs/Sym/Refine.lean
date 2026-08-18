import GoLeanProofs.Sym.Walk

/-!
# THE REFINEMENT THEOREM (WP arc slice 4, phase 2; design §6.1/§6.2
layer 4)

The window driver's induction over the master walk at the symbolic
interpretation: a `symEvalWindow` run of `n` completed steps transports
to an `n`-step `stepFnIter` fact — for EVERY valuation `ρ` (the
value-domain frame rule: full precision on every scalar the window
never inspects), EVERY table-carrier `σ` (program-genericity), and
EVERY choice stream `ch`, unchanged (choice-freedom of the fragment —
the mirror consumes no choices; Q3 quits enforce it).

Quit = shorter window (ruled OQ2): the driver has no error channel and
the theorem no side conditions — a quit at step `n+1` simply yields the
`n`-step fact. Nothing here claims quit-minimality (design §6.4: an
over-eager quit costs automation, never soundness).
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- **THE REFINEMENT THEOREM** (charter `:89`, design §6.1): the
transported window, ∀ρ ∀σ ∀ch with `ch` unchanged. -/
theorem symEvalWindow_refines :
    ∀ {budget : Nat} {S : SymState} {C : SymConfig} {n : Nat}
      {S' : SymState} {C' : SymConfig},
      symEvalWindow budget S C = (n, S', C') →
      ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
        stepFnIter n (γS ρ σ S) (γC ρ C) ch
          = .ok (γC ρ C', γS ρ σ S', ch) := by
  intro budget
  induction budget with
  | zero =>
      intro S C n S' C' h ρ σ ch
      simp only [symEvalWindow, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | succ budget ih =>
      intro S C n S' C' h ρ σ ch
      simp only [symEvalWindow] at h
      rcases hstep : stepFnS S C with q | ⟨C₁, S₁⟩ <;> rw [hstep] at h
      · -- quit ends the window: the 0-step fact
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      · -- one transported step, then the induction hypothesis
        simp only [] at h
        rcases hrec : symEvalWindow budget S₁ C₁ with ⟨m, S₂, C₂⟩
        rw [hrec] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h1 := stepFnS_sound ρ σ ch hstep
        simp only [stepFnIter, h1, Bind.bind, Except.bind]
        exact ih hrec ρ σ ch

/-- The PROJECTION-form corollary of the refinement theorem — the
emission-seam spelling (WP arc slice 4, phase 3: the matmul transported
segments are its first consumers, `Examples/MatMul.lean`). A window
discharge writes only the INPUT fixture: the transported RHS is the
run's own output (`(symEvalWindow …).2.1/2.2`), so no hand-transcribed
output fixture exists to get wrong — the campaign's near-miss class.
The one obligation is the step-count projection (`hn`), a closed
evaluator run; the caller lands on the statement's own spelling by a
defeq `exact`. Zero new content: `Prod` eta + `symEvalWindow_refines`. -/
theorem symEvalWindow_refines' {budget n : Nat} {S : SymState} {C : SymConfig}
    (hn : (symEvalWindow budget S C).1 = n)
    (ρ : Valuation) (σ : ExecState) (ch : Choices) :
    stepFnIter n (γS ρ σ S) (γC ρ C) ch
      = .ok (γC ρ (symEvalWindow budget S C).2.2,
          γS ρ σ (symEvalWindow budget S C).2.1, ch) :=
  symEvalWindow_refines (by rw [← hn]) ρ σ ch

end GoLean.Sym
