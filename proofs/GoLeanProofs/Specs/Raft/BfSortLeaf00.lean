import GoLeanProofs.Specs.Raft.BfSteps

/-! A4-U3 sort-collapse leaf (0,0): picked keys (1,2,3);
post-sort ids = [1,2,3] — the §4(ii) collapse instance. One module per
leaf: the whole-step kernel reduction costs ~8–9 min and multiple GB,
so leaves build in separate lean processes (measured: six in one
process breached the 24G cap). -/

namespace GoLean.RaftSeam
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

set_option maxRecDepth 8000000
set_option maxHeartbeats 256000000
set_option smartUnfolding false

theorem uSort_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int)
    (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ uS11) (γC (uρ ρ a 1 2 3) uC11) ch
      = .ok (γC (uρ ρ a 1 2 3) uC12, γS (uρ ρ a 1 2 3) σ uS12, ch) := by
  with_unfolding_all rfl

end GoLean.RaftSeam
