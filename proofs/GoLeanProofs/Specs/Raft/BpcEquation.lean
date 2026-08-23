import GoLeanProofs.Specs.Raft.BfEquation

/-!
# A4-U4 wave 1: the `becomePreCandidate` handler equation

The reset-family's choice-free member (`raftsubject/raft/raft.go:936-951`
— NO `reset` call, so no jitter pick, no `Visit`, no sort): from the
drained `becomePreCandidate()` call at any state γ-extending the
populated fixture WITH `state` CONCRETE 0 (the `state == StateLeader`
panic guard branches on it, so it cannot ride symbolic — the fixture
family's precondition, exactly the U3 fine-print pattern), the run is
**ONE transported window of 152 machine steps, zero choices consumed**
(`ch` rides through unchanged — the equation form's degenerate,
strongest case), landing at the function's return with projection
`specBecomePreCandidate` of the pre-projection.

Probe provenance (`artifacts/probe/BpcProbe.lean`, the
#eval-before-rfl rule): phase 1 (machine, concrete) completes in 152
steps, projection post == spec; phase 2 (mirror) is one 152-step
window whose γ-image heap EQUALS the machine's final heap (nextAddr
30 both); wrap depths probed: Vote survives symbolic at norm-depth 5
(hence the one `hvote` side condition), lead/state land concrete.

Slice-0 pattern note: a single-window handler needs NO generated
literals — with `kernel_rfl`, the kernel evaluates the 152-step
window per fact (~seconds); literalization pays off from the second
window on (BC's chain will use it).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface

set_option maxRecDepth 8000000

/-- The symbolic fixture: the U3 populated heap with the raft cell's
`Vote`/`lead`/`leadTransferee` symbolic (x₁/x₂/x₄) and `state`
CONCRETE 0 (follower — the panic-guard precondition). -/
def bpcSymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (uRaftVal 0 0 0 0))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def bpcSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy bpcSymRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def bpcS0 : SymState := { heap := bpcSymHeap, nextAddr := 21 }

/-- The drained call configuration of `becomePreCandidate()`
(receiver-only). -/
def bpcC0 : SymConfig :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)

def bpcS1 : SymState := (symEvalWindowTB bfTB 152 bpcS0 bpcC0).2.1

/-- The window count (#eval-checked first: 152, then a terminal
q11Internal — the run's whole span in one window). -/
theorem bpcW_n : (symEvalWindowTB bfTB 152 bpcS0 bpcC0).1 = 152 := by
  kernel_rfl

/-- The window lands at the function's return. -/
theorem bpcC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 152 bpcS0 bpcC0).2.2 = .next .stop := by
  kernel_rfl

/-- The full span: one transported window, `ch` unchanged. -/
theorem bpc_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 152 (γS ρ σ bpcS0) (γC ρ bpcC0) ch
      = .ok (.next .stop, γS ρ σ bpcS1, ch) := by
  have h := symEvalWindowTB_refines' bpcW_n ρ σ ch hag
  rw [bpcC1_stop ρ] at h
  exact h

/-- **THE HANDLER EQUATION**: from the drained `becomePreCandidate()`
call at any γ-extension of the fixture (state 0) with projection
`some n`, over ANY choice stream (none is consumed), the run returns
in 152 steps with projection `specBecomePreCandidate n`. The one side
condition is the surviving symbolic scalar's range fact (`hvote` —
store-time re-normalization wraps Vote 5 deep; U3's `unrm` pattern). -/
theorem becomePreCandidate_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (ch : Choices) :
    ∃ σfin,
      stepFnIter 152 (γS ρ σ bpcS0) (γC ρ bpcC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ bpcS0) ⟨0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  refine ⟨γS ρ σ bpcS1, bpc_span ρ σ ch hag, ?_, ?_⟩
  · kernel_rfl
  · have hproj : absRaftNode (γS ρ σ bpcS1) ⟨0⟩
        = some ⟨0, unrm 5 (ρ.ints 1), 0, 3, 1, 1⟩ := by
      kernel_rfl
    rw [hproj, unrm_id hvote 5]
    with_unfolding_all rfl

/-! ## Discharge witness (constitution §3.3): every premise at
concrete values — `wBase` tables, Vote 7 / lead 2 / leadTransferee 5,
the empty choice stream. -/

def bpcρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem becomePreCandidate_handler_eq_witness :
    ∃ σfin,
      stepFnIter 152 (γS bpcρw wBase bpcS0) (γC bpcρw bpcC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode (γS bpcρw wBase bpcS0) ⟨0⟩ = some ⟨0, 7, 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomePreCandidate ⟨0, 7, 2, 0, 1, 1⟩) :=
  becomePreCandidate_handler_eq bpcρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) []

end GoLean.RaftSeam
