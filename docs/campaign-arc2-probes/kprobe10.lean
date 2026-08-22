/- Campaign Arc 2, kernel probe K=10: the small-K kernel cost point.
Expected value confirmed compiled first (probeB0-expected.lean, all
small K are .error .fuelOut). smartUnfolding false is the kit's L5
rule (kit-guide §5/§22) — measured mandatory here: without it K=0 OOMs
past 48G in the elaborator's whnf. Run under scripts/capped + timeout;
wall/RSS recorded in the route memo. -/
import GoLeanProofs.Specs.RaftAgreement
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option smartUnfolding false

open GoLean.Examples.RaftTwin

example : twinRun 10 [] = .error .fuelOut := by with_unfolding_all rfl
