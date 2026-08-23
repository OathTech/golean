/- U5 lever re-projection point: 1000 fast steps from the 350k trie
checkpoint (decomposes fixed vs marginal after the k2000@48G OOM
refuted the 14.5 MB/step retention extrapolation). Existential form,
matching fastseg-k500's shape exactly. -/
import GoLeanProofs.Specs.TwinCheckpointsF
import GoLeanProofs.FastEval.Step
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option smartUnfolding false

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open GoLean.FastEval

example : ∃ x, iterF stepFast 1000 ckptF350kState ckptF350k.2.2.1 ckptF350k.2.2.2 = .ok x := by
  with_unfolding_all exact ⟨_, rfl⟩
