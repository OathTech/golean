/- U4 mid-build gate kernel point: 20000 fast steps from the 350k trie
checkpoint. Expected .ok confirmed compiled first (fastseg-expected).
Existential form; capped + timed + RSS-polled; kill point is a datum. -/
import GoLeanProofs.Specs.TwinCheckpointsF
import GoLeanProofs.FastEval.Step
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option smartUnfolding false

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open GoLean.FastEval

example : ∃ x, iterF stepFast 20000 ckptF350kState ckptF350k.2.2.1 ckptF350k.2.2.2 = .ok x := by
  with_unfolding_all exact ⟨_, rfl⟩
