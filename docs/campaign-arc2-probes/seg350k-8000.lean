/- Campaign Arc 2, U2 go/no-go probe: ONE mid-run segment of 8000 steps
from the 350k checkpoint (heap 19,093 cells), kernel-checked.
Expected shape confirmed compiled first (seg350k-expected.lean: .ok).
The existential form makes the elaborator's whnf supply the endpoint —
no hand-transcribed output state; the kernel still checks the full
equation. Run capped + timed + RSS-polled; a kill point is a datum. -/
import GoLeanProofs.Specs.TwinCheckpoints
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option smartUnfolding false

open GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin

example : ∃ x, stepFnIter 8000 ckpt350kState ckpt350kCfg ckpt350kCh = .ok x := by
  with_unfolding_all exact ⟨_, rfl⟩
