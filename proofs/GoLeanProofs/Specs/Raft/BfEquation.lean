import GoLeanProofs.Specs.Raft.BfSortStep

/-!
# A4-U3: THE FIRST FULL HANDLER EQUATION — `becomeFollower`

The charter statement (A4-U3 dispatch), realized: from the drained
call configuration of `becomeFollower(0, x₉)` at any state γ-extending
the POPULATED fixture (`uS0`, probe2's recipe) whose abstract
projection is `some n`, over EVERY consumed choice prefix
`c₁ c₂ c₃ c₄` (the D-11 jitter pick + Visit's three range picks), the
run reaches the function's return in exactly 3,234 machine steps with
the four choices consumed and the projection equal to
`specBecomeFollower n 0 lead` — the spec handler applied at the
abstract state (`AbsState.lean`, the pilot's validated
correspondence form).

Composition: the 7 transported windows (`BfFixture`) chained through
the 6 hand crossings (`BfSteps`/`BfSteps2`) — the spine's shape at
scale: window ⧺ pick ⧺ … ⧺ stop ⧺ window ⧺ sort-collapse ⧺ window.
The conclusion is CHOICE-INDEPENDENT (design §4(ii)): the picked keys
land only in latitude-bearing spots (`randomizedElectionTimeout`, the
dead iteration key cells) that `absRaftNode` never reads; the final
state itself is prefix-dependent, hence the existential.

Fine print, recorded:
- `Term = 0 = term` in the fixture: reset's term-EQUAL branch (vote
  preserved). The term-change branch (vote cleared) is a recorded U3
  residual — a second fixture family, same machinery.
- `hlead`: the lead argument is a `uint64` value (its normalize is
  the identity) — the genuinely-external side condition, discharged
  concretely in the witness.
- Address-concrete per design §5: the fixture's layout is part of the
  statement; `γ-extending` = any tables-agreeing σ and any valuation.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-- Iterated `uint64` normalize — the shape store-time
re-normalization leaves on the raft cell's symbolic scalars (every
whole-struct write re-wraps them; probe `ProjProbe`: Vote 13 deep,
lead 3 deep). -/
def unrm : Nat → Int → Int
  | 0, v => v
  | n + 1, v => IntKind.normalize .uint64 (unrm n v)

theorem unrm_id {v : Int} (h : IntKind.normalize .uint64 v = v) :
    ∀ n, unrm n v = v
  | 0 => rfl
  | n + 1 => by rw [unrm, unrm_id h n, h]

/-- The composed 3,234-step span at the prefix-derived valuation. -/
theorem bf_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices) :
    stepFnIter 3234 (γS (uρ' ρ c₁ c₂ c₃) σ uS0) (γC (uρ' ρ c₁ c₂ c₃) uC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: ch)
      = .ok (.next .stop, γS (uρ' ρ c₁ c₂ c₃) σ uS13, ch) := by
  have w1 := fun chx => symEvalWindowTB_refines' uW1_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w2 := fun chx => symEvalWindowTB_refines' uW2_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w3 := fun chx => symEvalWindowTB_refines' uW3_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w4 := fun chx => symEvalWindowTB_refines' uW4_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w5 := fun chx => symEvalWindowTB_refines' uW5_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w6 := fun chx => symEvalWindowTB_refines' uW6_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have w7 := fun chx => symEvalWindowTB_refines' uW7_n (uρ' ρ c₁ c₂ c₃) σ chx hag
  have p1 := uPick1_step ρ σ hag (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)
    c₁ (c₂ :: c₃ :: c₄ :: ch)
  have p2 := uPick2_step ρ σ ((c₁ % 10 : Nat) : Int) (uKey2 c₂ c₃)
    (uKey3 c₂ c₃) c₂ (c₃ :: c₄ :: ch)
  have p3 := uPick3_step ρ σ ((c₁ % 10 : Nat) : Int) (uKey3 c₂ c₃)
    c₂ c₃ (c₄ :: ch)
  have p4 := uPick4_step ρ σ ((c₁ % 10 : Nat) : Int) c₂ c₃ c₄ ch
  have pstop := uStop_step ρ σ ((c₁ % 10 : Nat) : Int) c₂ c₃ ch
  have psort := uSort_step ρ σ ((c₁ % 10 : Nat) : Int) c₂ c₃ ch
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
  have hstop : γC (uρ' ρ c₁ c₂ c₃) uC13 = .next .stop := by
    rw [uC13_stop]
    rfl
  rw [← hstop]
  exact h

/-- **THE HANDLER EQUATION** (A4-U3's deliverable; seam design
layer (B), the pilot's validated correspondence form at full-handler
scale): from the drained `becomeFollower(0, lead)` call at any
γ-extension of the populated fixture with projection `some n`, over
every consumed choice prefix, the run returns with projection
`specBecomeFollower n 0 lead`. -/
theorem becomeFollower_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 9) = ρ.ints 9)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 3234 (γS ρ σ uS0) (γC ρ uC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ uS0) ⟨0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeFollower
              ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩ 0 (ρ.ints 9)) := by
  have hpre : γS ρ σ uS0 = γS (uρ' ρ c₁ c₂ c₃) σ uS0 := by
    with_unfolding_all rfl
  have hpreC : γC ρ uC0 = γC (uρ' ρ c₁ c₂ c₃) uC0 := by
    with_unfolding_all rfl
  refine ⟨γS (uρ' ρ c₁ c₂ c₃) σ uS13, ?_, ?_, ?_⟩
  · rw [hpre, hpreC]
    exact bf_full_span ρ σ hag c₁ c₂ c₃ c₄ ch
  · with_unfolding_all rfl
  · have hproj : absRaftNode (γS (uρ' ρ c₁ c₂ c₃) σ uS13) ⟨0⟩
        = some ⟨0, unrm 13 (ρ.ints 1), unrm 3 (ρ.ints 9), 0, 1, 1⟩ := by
      with_unfolding_all rfl
    rw [hproj, unrm_id hvote 13, unrm_id hlead 3]
    with_unfolding_all rfl

/-! ## Discharge witness (constitution §3.3): every premise at
concrete values — the tables state `wBase`, a live valuation
(Vote 7, lead 2, state 1, leadTransferee 5, lead ARG 4), and the
concrete prefix `[3, 1, 0, 0]` (the probe's stream). -/

def uρw : Valuation :=
  { ints := fun i => [0, 7, 2, 1, 5, 0, 0, 0, 0, 4].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem becomeFollower_handler_eq_witness :
    ∃ σfin,
      stepFnIter 3234 (γS uρw wBase uS0) (γC uρw uC0) [3, 1, 0, 0]
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode (γS uρw wBase uS0) ⟨0⟩ = some ⟨0, 7, 2, 1, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeFollower ⟨0, 7, 2, 1, 1, 1⟩ 0 4) :=
  becomeFollower_handler_eq uρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 1 0 0 []

end GoLean.RaftSeam
