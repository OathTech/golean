import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.RoundVoteEqB
import GoLeanProofs.Specs.Raft.RoundVoteEqC

/-! # RoundVoteEquation — THE CANONICAL RUN of the MsgVote
real-vote-family round (A4-U23): anchor to anchor, 19,291 steps, 9
draws, composed from the three segment spans. The stream prefix is
the round's censused draw list: position 0 is THE SEMANTIC DELIVERY
PICK (which live message is delivered — the draw the
choice-invariance factoring keeps explicit); positions 1–4 are the
becomeFollower Visit mapIters (latitude: map-iteration order);
positions 5–8 are latitude appendSpills (capacity only — the family
the ∀-stream envelope will absorb via the arc4c ~ when it lands;
until then the canonical zero draws with the RE-SPILL residual
recorded, the C2c convention). The Visit loop's exhaustion-exit
crossing (arm segment) consumes NOTHING and holds for every stream —
it does not appear in the prefix. -/

namespace GoLean.RaftSeam.RoundVote

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The round's censused draw prefix: the delivery pick, four Visit
mapIters, four spills — all at the canonical zero. -/
def πVote : Choices := [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **THE CANONICAL ROUND RUN** (∀ρ ∀σ-tables ∀stream-tail): from the
γ-image of the anchor literal, the full vote round completes in
19,291 steps consuming exactly the nine-draw prefix, ending at the
γ-image of the end-anchor literal (self-returning at the γ level —
`roundVote_selfReturn_conc`, `RoundVoteLemma.lean`). -/
theorem roundVote_run (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 19291 (γS ρ σ mvSB0) (γC ρ mvCB0) (πVote ++ rest)
      = .ok (γC ρ mvCB26, γS ρ σ mvSB26, rest) := by
  have h1 := roundVote_armSpan ρ σ hag (0 :: 0 :: 0 :: 0 :: rest)
  have h2 := roundVote_midSpan ρ σ hag (0 :: 0 :: 0 :: rest)
  have h3 := roundVote_suffixSpan ρ σ hag rest
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain h1 h2) h3

end GoLean.RaftSeam.RoundVote
