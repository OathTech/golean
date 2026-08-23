/- U5 emitter gate-check (before any wave): batch-emit [350000, 350100]
via `twin_ckpt_groupF%` (ONE incremental compiled pass), then kernel-check
(1) the incremental literal at 350k EQUALS the from-0 single-index
    reflection `ckptF350k` (drift check on the batch lever's logic);
(2) the exact unit-5 segment shape — equality-to-next-literal over
    100 fast steps. -/
import GoLeanProofs.Specs.TwinCheckpointsF
import GoLeanProofs.FastEval.Step
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option smartUnfolding false

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open GoLean.FastEval GoLean.StateWire

namespace GoLean.Examples.RaftTwin

twin_ckpt_groupF% tk [350000, 350100]

/-- The uniform segment-state spelling (program-generic: tables once). -/
def stOf (p : HeapT × Nat × Config × Choices) : ExecStateF :=
  { twinBaseF with heapT := p.1, nextAddr := p.2.1 }

-- (1) incremental == from-0
example : tk_350000 = ckptF350k := by with_unfolding_all rfl

-- (2) the unit-5 segment shape, 100 steps
example : iterF stepFast 100 (stOf tk_350000) tk_350000.2.2.1 tk_350000.2.2.2
    = .ok (tk_350100.2.2.1, stOf tk_350100, tk_350100.2.2.2) := by
  with_unfolding_all rfl

end GoLean.Examples.RaftTwin
