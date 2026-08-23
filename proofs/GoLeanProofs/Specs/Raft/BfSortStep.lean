import GoLeanProofs.Specs.Raft.BfSteps2
import GoLeanProofs.Sym.KernelRfl

/-! A4-U3: the sortSlice COLLAPSE dispatcher — the §4(ii) collapse at
the choice-prefix level: every pick order lands in one of the six
leaves, and every leaf's post state is `uS12` (ids = [1,2,3]; the dead
key cells keep their per-leaf values, which `absRaftNode` never
reads).

A4-U4 slice 0: the six leaves live IN THIS MODULE again — the
one-module-per-leaf split (U3's 24G-cap workaround) is retired. Two
levers landed: the leaves reduce against the `BfLit` literals instead
of re-evaluating the window chain, and the conversion is checked by
`kernel_rfl` (kernel-delegated; the elaborator's slow machine-side
whnf was 100% of the measured leaf cost — 352 s elaborator vs ≈0 s
kernel on the identical goal). Measured after both levers: the whole
six-leaf family + dispatcher elaborates in seconds. -/

namespace GoLean.RaftSeam
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

set_option maxRecDepth 8000000

/-! ## The six leaves (picked-key orders; post state `uS12` in every
one — the collapse). Each is `#eval`-validated by the BfU3Probe
phase-2 walk; `kernel_rfl` fails loudly at `addDecl` on any drift. -/

theorem uSort_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ uS11) (γC (uρ ρ a 1 2 3) uC11) ch
      = .ok (γC (uρ ρ a 1 2 3) uC12, γS (uρ ρ a 1 2 3) σ uS12, ch) := by
  kernel_rfl

theorem uSort_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ uS11) (γC (uρ ρ a 1 3 2) uC11) ch
      = .ok (γC (uρ ρ a 1 3 2) uC12, γS (uρ ρ a 1 3 2) σ uS12, ch) := by
  kernel_rfl

theorem uSort_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ uS11) (γC (uρ ρ a 2 1 3) uC11) ch
      = .ok (γC (uρ ρ a 2 1 3) uC12, γS (uρ ρ a 2 1 3) σ uS12, ch) := by
  kernel_rfl

theorem uSort_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ uS11) (γC (uρ ρ a 2 3 1) uC11) ch
      = .ok (γC (uρ ρ a 2 3 1) uC12, γS (uρ ρ a 2 3 1) σ uS12, ch) := by
  kernel_rfl

theorem uSort_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ uS11) (γC (uρ ρ a 3 1 2) uC11) ch
      = .ok (γC (uρ ρ a 3 1 2) uC12, γS (uρ ρ a 3 1 2) σ uS12, ch) := by
  kernel_rfl

theorem uSort_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ uS11) (γC (uρ ρ a 3 2 1) uC11) ch
      = .ok (γC (uρ ρ a 3 2 1) uC12, γS (uρ ρ a 3 2 1) σ uS12, ch) := by
  kernel_rfl

theorem uSort_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ uS11)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) uC11) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) uC12,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ uS12,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact uSort_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact uSort_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact uSort_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact uSort_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact uSort_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact uSort_leaf_21 ρ σ a ch

end GoLean.RaftSeam
