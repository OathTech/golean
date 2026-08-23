import GoLeanProofs.Specs.Raft.BcSteps

/-!
# A4-U4 wave 1: THE `becomeCandidate` HANDLER EQUATION

The third full handler equation, U3's exact form at the reset-family's
TERM-CHANGE branch: from the drained `becomeCandidate()` call at any
state γ-extending the populated fixture (`bcS0`, state CONCRETE 0 —
the panic-guard precondition) with projection `some n`, over EVERY
consumed choice prefix `c₁ c₂ c₃ c₄` (the D-11 jitter pick + Visit's
three range picks), the run reaches the function's return in exactly
**3,282 machine steps** with the four choices consumed and the
projection equal to `specBecomeCandidate n 1` — the spec handler at
the abstract state, `r.id = 1` from the fixture.

NO range side conditions: every pre-symbolic scalar (Vote/lead/
leadTransferee) is OVERWRITTEN by the handler (reset's term-change
branch clears the vote before `r.Vote = r.id`), so the post
projection is fully concrete (probe: post scalars are norm-wraps over
LITERALS, reducing closed).

Composition: 7 transported windows (`BcFixture`, at the `BcLit`
literals) ⧺ 4 pick transports ⧺ the whole-step STOP ⧺ the whole-step
sortSlice COLLAPSE (`BcSteps`) — the reset-span spine, instantiated
the second time.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-- The composed 3,282-step span at the prefix-derived valuation. -/
theorem bc_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices) :
    stepFnIter 3282 (γS (uρ' ρ c₁ c₂ c₃) σ bcS0) (γC (uρ' ρ c₁ c₂ c₃) bcC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: ch)
      = .ok (.next .stop, γS (uρ' ρ c₁ c₂ c₃) σ bcS13, ch) := by
  have w1 := fun chx => bcWin1 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w2 := fun chx => bcWin2 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w3 := fun chx => bcWin3 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w4 := fun chx => bcWin4 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w5 := fun chx => bcWin5 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w6 := fun chx => bcWin6 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w7 := fun chx => bcWin7 (uρ' ρ c₁ c₂ c₃) σ chx hag
  have p1 := bcPick1_step ρ σ hag (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)
    c₁ (c₂ :: c₃ :: c₄ :: ch)
  have p2 := bcPick2_step ρ σ ((c₁ % 10 : Nat) : Int) (uKey2 c₂ c₃)
    (uKey3 c₂ c₃) c₂ (c₃ :: c₄ :: ch)
  have p3 := bcPick3_step ρ σ ((c₁ % 10 : Nat) : Int) (uKey3 c₂ c₃)
    c₂ c₃ (c₄ :: ch)
  have p4 := bcPick4_step ρ σ ((c₁ % 10 : Nat) : Int) c₂ c₃ c₄ ch
  have pstop := bcStop_step ρ σ ((c₁ % 10 : Nat) : Int) c₂ c₃ ch
  have psort := bcSort_step ρ σ ((c₁ % 10 : Nat) : Int) c₂ c₃ ch
  have h := GoLean.Surface.stepFnIter_chain
    (GoLean.Surface.stepFnIter_chain
      (GoLean.Surface.stepFnIter_chain
        (GoLean.Surface.stepFnIter_chain
          (GoLean.Surface.stepFnIter_chain
            (GoLean.Surface.stepFnIter_chain
              (GoLean.Surface.stepFnIter_chain
                (GoLean.Surface.stepFnIter_chain
                  (GoLean.Surface.stepFnIter_chain
                    (GoLean.Surface.stepFnIter_chain
                      (GoLean.Surface.stepFnIter_chain
                        (GoLean.Surface.stepFnIter_chain
                          (w1 (c₁ :: c₂ :: c₃ :: c₄ :: ch))
                          (GoLean.Surface.stepFnIter_one p1))
                        (w2 (c₂ :: c₃ :: c₄ :: ch)))
                      (GoLean.Surface.stepFnIter_one p2))
                    (w3 (c₃ :: c₄ :: ch)))
                  (GoLean.Surface.stepFnIter_one p3))
                (w4 (c₄ :: ch)))
              (GoLean.Surface.stepFnIter_one p4))
            (w5 ch))
          (GoLean.Surface.stepFnIter_one pstop))
        (w6 ch))
      (GoLean.Surface.stepFnIter_one psort))
    (w7 ch)
  have hstop : γC (uρ' ρ c₁ c₂ c₃) bcC13 = .next .stop := by
    rw [bcC13_stop]
    rfl
  rw [← hstop]
  exact h

/-- **THE HANDLER EQUATION**: from the drained `becomeCandidate()`
call at any γ-extension of the fixture (state 0) with projection
`some n`, over every consumed choice prefix, the run returns with
projection `specBecomeCandidate n 1` — no side conditions. -/
theorem becomeCandidate_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 3282 (γS ρ σ bcS0) (γC ρ bcC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ bcS0) ⟨0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeCandidate
              ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ 1) := by
  have hpre : γS ρ σ bcS0 = γS (uρ' ρ c₁ c₂ c₃) σ bcS0 := by
    kernel_rfl
  have hpreC : γC ρ bcC0 = γC (uρ' ρ c₁ c₂ c₃) bcC0 := by
    kernel_rfl
  refine ⟨γS (uρ' ρ c₁ c₂ c₃) σ bcS13, ?_, ?_, ?_⟩
  · rw [hpre, hpreC]
    exact bc_full_span ρ σ hag c₁ c₂ c₃ c₄ ch
  · kernel_rfl
  · kernel_rfl

/-! ## Discharge witness (constitution §3.3): every premise at
concrete values — `wBase` tables, Vote 7 / lead 2 / leadTransferee 5,
the probe's stream `[3, 1, 0, 0]`. -/

def bcρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem becomeCandidate_handler_eq_witness :
    ∃ σfin,
      stepFnIter 3282 (γS bcρw wBase bcS0) (γC bcρw bcC0) [3, 1, 0, 0]
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode (γS bcρw wBase bcS0) ⟨0⟩ = some ⟨0, 7, 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeCandidate ⟨0, 7, 2, 0, 1, 1⟩ 1) :=
  becomeCandidate_handler_eq bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ 3 1 0 0 []

end GoLean.RaftSeam
