import GoLeanProofs.Specs.Raft.RoundVrEqA
import GoLeanProofs.Specs.Raft.RoundVrEqB
import GoLeanProofs.Specs.Raft.RoundVrEqC
import GoLeanProofs.Specs.Raft.RoundVrEqD
import GoLeanProofs.Specs.Raft.RoundVrEqE

/-! # RoundVrEquation — THE CANONICAL RUN of the MsgVoteResp
ELECTION-COMPLETION round (A4-U25): anchor 2 to anchor 3, 33,274
steps, 25 draws, composed from the five segment spans. Position 0
is THE SEMANTIC DELIVERY PICK (deliver the quorum-completing
VoteResp to the candidate); the remaining draws are 16 tracker/map
Visit mapIters (poll bookkeeping, becomeLeader's progress resets,
bcastAppend's peer walk — latitude: map-iteration order,
table-pinned per the U23 finding) and 8 latitude appendSpills (the
noop-append storage ring + the two MsgApp send assemblies + the
harness net/live sends). FIVE choice-free Visit exhaustion-exits
consume NOTHING and hold ∀-stream — the fourth round kind confirming
the U23 auto-discovery lesson (the choice census cannot place them;
the mirror's own quit sites can). -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The round's censused draw prefix: the pick, sixteen Visit
mapIters, eight spills — all at the canonical zero. -/
def πVr : Choices :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **THE CANONICAL ROUND RUN** (∀ρ ∀σ-tables ∀stream-tail). -/
theorem roundVr_run (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 33274 (γS ρ σ vrSB0) (γC ρ vrCB0) (πVr ++ rest)
      = .ok (γC ρ vrCB69, γS ρ σ vrSB69, rest) := by
  have h1 := roundVr_spanA ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 ::
    0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h2 := roundVr_spanB ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 ::
    0 :: rest)
  have h3 := roundVr_spanC ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 ::
    0 :: rest)
  have h4 := roundVr_spanD ρ σ hag rest
  have h5 := roundVr_spanE ρ σ hag rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain (Surface.stepFnIter_chain h1 h2) h3) h4) h5

end GoLean.RaftSeam.RoundVr
