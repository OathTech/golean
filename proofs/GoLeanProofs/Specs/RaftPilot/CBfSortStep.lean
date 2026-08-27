import GoLeanProofs.Specs.RaftPilot.CBfSteps2
import GoLeanProofs.Sym.KernelRfl

/-!
# W2 unit 4: the compliant-chain sort collapse (the address-shifted
mirror of `BfSortStep`). PRIVATE scaffolding per the W1 convention.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The six leaves (picked-key orders; post state `cS12` in every
one — the collapse). Each is `#eval`-validated by the BfU3Probe
phase-2 walk; `kernel_rfl` fails loudly at `addDecl` on any drift. -/

theorem cSort_leaf_00 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ cS11) (γC (uρ ρ a 1 2 3) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a 1 2 3) (cC12 tenv k), γS (uρ ρ a 1 2 3) σ cS12, ch) := by
  kernel_rfl

theorem cSort_leaf_01 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ cS11) (γC (uρ ρ a 1 3 2) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a 1 3 2) (cC12 tenv k), γS (uρ ρ a 1 3 2) σ cS12, ch) := by
  kernel_rfl

theorem cSort_leaf_10 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ cS11) (γC (uρ ρ a 2 1 3) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a 2 1 3) (cC12 tenv k), γS (uρ ρ a 2 1 3) σ cS12, ch) := by
  kernel_rfl

theorem cSort_leaf_11 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ cS11) (γC (uρ ρ a 2 3 1) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a 2 3 1) (cC12 tenv k), γS (uρ ρ a 2 3 1) σ cS12, ch) := by
  kernel_rfl

theorem cSort_leaf_20 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ cS11) (γC (uρ ρ a 3 1 2) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a 3 1 2) (cC12 tenv k), γS (uρ ρ a 3 1 2) σ cS12, ch) := by
  kernel_rfl

theorem cSort_leaf_21 (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ cS11) (γC (uρ ρ a 3 2 1) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a 3 2 1) (cC12 tenv k), γS (uρ ρ a 3 2 1) σ cS12, ch) := by
  kernel_rfl

theorem cSort_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState) (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ cS11)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (cC11 tenv k)) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (cC12 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ cS12,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact cSort_leaf_00 tenv k ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact cSort_leaf_01 tenv k ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact cSort_leaf_10 tenv k ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact cSort_leaf_11 tenv k ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact cSort_leaf_20 tenv k ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact cSort_leaf_21 tenv k ρ σ a ch


end GoLean.RaftSeam
