import GoLeanProofs.Specs.Raft.RoundMaEqA
import GoLeanProofs.Specs.Raft.RoundMaEqB
import GoLeanProofs.Specs.Raft.RoundMaEqC

/-! # RoundMaEquation — THE CANONICAL RUN of the MsgApp append-family
round (A4-U22 C2d): anchor to anchor, 23,488 steps, 8 draws, composed
from the three segment spans. The stream prefix is the round's
censused draw list: position 0 is THE SEMANTIC DELIVERY PICK (which
live message is delivered — the draw the choice-invariance factoring
keeps explicit); positions 1–7 are latitude appendSpills (capacity
only — the family the ∀-stream envelope will absorb via the arc4c ~
when it lands; until then the canonical zero draws with the RE-SPILL
residual recorded, exactly the C2c convention). -/

namespace GoLean.RaftSeam.RoundMa

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The round's censused draw prefix: the delivery pick, then seven
latitude spills — all at the canonical zero. -/
def πMa : Choices := [0, 0, 0, 0, 0, 0, 0, 0]

/-- **THE CANONICAL ROUND RUN** (∀ρ ∀σ-tables ∀stream-tail): from the
γ-image of the anchor literal, the full round completes in 23,488
steps consuming exactly the eight-draw prefix, ending at the γ-image
of the end-anchor literal — with the SAME loop-head configuration
(self-returning; `maCR4 = maCR0` is checked by `roundMa_selfReturn`
below). -/
theorem roundMa_run (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 23488 (γS ρ σ maSR0) (γC ρ maCR0) (πMa ++ rest)
      = .ok (γC ρ maCR4, γS ρ σ maSR4, rest) := by
  have h1 := roundMa_armSpan ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h2 := roundMa_ringHeadSpan ρ σ hag (0 :: 0 :: rest)
  have h3 := roundMa_suffixSpan ρ σ hag rest
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain h1 h2) h3

/-! Self-return note: the MACHINE configs at the two anchors are
identical (fixture-probe-verified by repr); the SYM literals `maCR0`
(reflected) and `maCR4` (mirror-propagated) may differ
representationally, so the self-return equality is stated at the γ
level, closed, in `RoundMaLemma.lean` (`roundMa_selfReturn_conc`) —
the level the R-form's `renameConfig r C0` return shape consumes. -/

end GoLean.RaftSeam.RoundMa
