import GoLeanProofs.Specs.Raft.RoundMarEqA
import GoLeanProofs.Specs.Raft.RoundMarEqB
import GoLeanProofs.Specs.Raft.RoundMarEqC
import GoLeanProofs.Specs.Raft.RoundMarEqD

/-! # RoundMarEquation — THE CANONICAL RUN of the MsgAppResp
maybeCommit round (A4-U24): anchor 3 to anchor 4, 26,224 steps, 10
draws, composed from the four segment spans. Position 0 is THE
SEMANTIC DELIVERY PICK; positions 1–6 are the two tracker-Visit
mapIter triplets (maybeCommit's quorum walk, bcastAppend's peer walk
— latitude: map-iteration order); positions 7–9 are latitude
appendSpills (the send assembly + the harness net/live sends). The
two Visit exhaustion-exits consume NOTHING and hold ∀-stream. The
crossing-free 12,816-step stretch (B22–B27) is the commit ring's
core — apply + SetHardState + the nested MsgStorageApplyResp Step —
draw-free, SC1's storage-resp classification at the COMMIT ring. -/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The round's censused draw prefix: the pick, six Visit mapIters,
three spills — all at the canonical zero. -/
def πMar : Choices := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **THE CANONICAL ROUND RUN** (∀ρ ∀σ-tables ∀stream-tail). -/
theorem roundMar_run (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 26224 (γS ρ σ mrSB0) (γC ρ mrCB0) (πMar ++ rest)
      = .ok (γC ρ mrCB33, γS ρ σ mrSB33, rest) := by
  have h1 := roundMar_spanA ρ σ hag (0 :: 0 :: 0 :: rest)
  have h2 := roundMar_spanB ρ σ hag (0 :: 0 :: rest)
  have h3 := roundMar_spanC ρ σ hag (0 :: 0 :: rest)
  have h4 := roundMar_spanD ρ σ hag rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain (Surface.stepFnIter_chain h1 h2) h3) h4

end GoLean.RaftSeam.RoundMar
