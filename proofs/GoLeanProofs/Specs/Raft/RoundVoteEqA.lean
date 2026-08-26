import GoLeanProofs.Specs.Raft.RoundVoteLit1
import GoLeanProofs.Specs.Raft.RoundVoteLit2
import GoLeanProofs.Specs.Raft.RoundVoteLit3
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVoteEqA — the ARM segment of the MsgVote round's canonical
run (A4-U23): anchor → past becomeFollower's Visit loop. Windows +
crossings in the tree-propagation template with the U23
AUTO-DISCOVERED boundary schedule (the mirror's own quit sites; the
choice census alone MISSES choice-free quit sites — this segment ends
at the first one found, the Visit loop's mapIterK exhaustion-exit at
round step 3793, `roundVote_visitExit`: a crossing that consumes NO
choice). The round's SEMANTIC draw is the delivery pick (round step
207, `roundVote_pick`); the four Visit mapIter draws
(`roundVote_reset1–4`, becomeFollower's tracker reset — SC1's bucket
row at instance level) are latitude. Split across three RoundVoteEq*
modules so the kernel work parallelizes (the C2c lesson). Design
record: `RoundVoteLemma.lean`'s docstring.

SECOND TEMPLATE FINDING (this unit, measured by kernel bisect —
probes `Reset1Bisect*.lean`/`Reset1Fix.lean`): a mapIter crossing
over a map whose VALUE type is a defined type consults the TYPE
TABLE (`snapshotEntriesSelfNormalized s.types …` inside
`mapIterCandidates`), so its ∀σ statement is NOT kernel-reducible at
a free table carrier — the four Visit-reset crossings (tracker
`map[uint64]*tracker.Progress`) carry the windows' own
`bfTB.Agrees σ` premise and rewrite to the pinned carrier first
(`γS_pin`). The delivery pick (`map[int]bool` — primitive value
type) and the exhaustion-exit (empty candidate list) never touch the
table and stay premise-free. -/

namespace GoLean.RaftSeam.RoundVote

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- Table pin at the twin pack — now a thin wrapper over the
PROMOTED generic `SymTables.Agrees.concS_eq` (TableExt; promotion
executed A4-U24 when `RoundMarEqA` became the second consumer, per
the U23 ledger row). Statement unchanged. -/
theorem γS_pin {σ : ExecState} (hag : bfTB.Agrees σ)
    (ρ : Valuation) (S : SymState) :
    γS ρ σ S = γS ρ bfTB.toState S :=
  hag.concS_eq S

/-- Window: anchor → the delivery pick (207 steps). -/
theorem mvWA1_out : symEvalWindowTB bfTB 207 mvSB0 mvCB0
    = (207, mvSB1, mvCB1) := by
  kernel_rfl

/-- **THE SEMANTIC CROSSING** — the delivery pick (mapIter draw at
head 0: deliver net[0], the doctored MsgVote). -/
theorem roundVote_pick (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB1) (γC ρ mvCB1) (0 :: rest)
      = .ok (γC ρ mvCB2, γS ρ σ mvSB2, rest) := by
  kernel_rfl

theorem mvWA2_out : symEvalWindowTB bfTB 2500 mvSB2 mvCB2
    = (2500, mvSB3, mvCB3) := by
  kernel_rfl

theorem mvWA3_out : symEvalWindowTB bfTB 814 mvSB3 mvCB3
    = (814, mvSB4, mvCB4) := by
  kernel_rfl

/-- becomeFollower's tracker `Visit` mapIter draw 1 (latitude:
map-iteration order). -/
theorem roundVote_reset1 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mvSB4) (γC ρ mvCB4) (0 :: rest)
      = .ok (γC ρ mvCB5, γS ρ σ mvSB5, rest) := by
  simp only [γS_pin hag]
  kernel_rfl

theorem mvWA4_out : symEvalWindowTB bfTB 183 mvSB5 mvCB5
    = (183, mvSB6, mvCB6) := by
  kernel_rfl

/-- Visit mapIter draw 2 (latitude). -/
theorem roundVote_reset2 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mvSB6) (γC ρ mvCB6) (0 :: rest)
      = .ok (γC ρ mvCB7, γS ρ σ mvSB7, rest) := by
  simp only [γS_pin hag]
  kernel_rfl

theorem mvWA5_out : symEvalWindowTB bfTB 28 mvSB7 mvCB7
    = (28, mvSB8, mvCB8) := by
  kernel_rfl

/-- Visit mapIter draw 3 (latitude). -/
theorem roundVote_reset3 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mvSB8) (γC ρ mvCB8) (0 :: rest)
      = .ok (γC ρ mvCB9, γS ρ σ mvSB9, rest) := by
  simp only [γS_pin hag]
  kernel_rfl

theorem mvWA6_out : symEvalWindowTB bfTB 28 mvSB9 mvCB9
    = (28, mvSB10, mvCB10) := by
  kernel_rfl

/-- Visit mapIter draw 4 (latitude). -/
theorem roundVote_reset4 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mvSB10) (γC ρ mvCB10) (0 :: rest)
      = .ok (γC ρ mvCB11, γS ρ σ mvSB11, rest) := by
  simp only [γS_pin hag]
  kernel_rfl

theorem mvWA7_out : symEvalWindowTB bfTB 28 mvSB11 mvCB11
    = (28, mvSB12, mvCB12) := by
  kernel_rfl

/-- **THE CHOICE-FREE CROSSING** — the Visit loop's mapIterK
exhaustion-exit (round step 3793): the mirror quits here (its
conservative mapIter quit-site) but the MACHINE consumes no choice —
the step is deterministic, so the crossing holds for EVERY stream.
The U23 template lesson: crossings are the mirror's quit sites, not
the choice census's draw sites. -/
theorem roundVote_visitExit (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB12) (γC ρ mvCB12) rest
      = .ok (γC ρ mvCB13, γS ρ σ mvSB13, rest) := by
  kernel_rfl

/-- **The ARM segment span**: anchor → past the Visit exit (3,794
steps, 5 draws: the pick + four latitude Visit mapIters; the
exhaustion-exit crossing consumes nothing). -/
theorem roundVote_armSpan (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 3794 (γS ρ σ mvSB0) (γC ρ mvCB0) (0 :: 0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ mvCB13, γS ρ σ mvSB13, rest) := by
  have h1 := symEvalWindowTB_refines mvWA1_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have hp := roundVote_pick ρ σ (0 :: 0 :: 0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines mvWA2_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have h3 := symEvalWindowTB_refines mvWA3_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have hr1 := roundVote_reset1 ρ σ hag (0 :: 0 :: 0 :: rest)
  have h4 := symEvalWindowTB_refines mvWA4_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have hr2 := roundVote_reset2 ρ σ hag (0 :: 0 :: rest)
  have h5 := symEvalWindowTB_refines mvWA5_out ρ σ (0 :: 0 :: rest) hag
  have hr3 := roundVote_reset3 ρ σ hag (0 :: rest)
  have h6 := symEvalWindowTB_refines mvWA6_out ρ σ (0 :: rest) hag
  have hr4 := roundVote_reset4 ρ σ hag rest
  have h7 := symEvalWindowTB_refines mvWA7_out ρ σ rest hag
  have hx := roundVote_visitExit ρ σ rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain
          (Surface.stepFnIter_chain
            (Surface.stepFnIter_chain
              (Surface.stepFnIter_chain
                (Surface.stepFnIter_chain
                  (Surface.stepFnIter_chain
                    (Surface.stepFnIter_chain
                      (Surface.stepFnIter_chain
                        (Surface.stepFnIter_chain h1 (Surface.stepFnIter_one hp))
                        h2)
                      h3)
                    (Surface.stepFnIter_one hr1))
                  h4)
                (Surface.stepFnIter_one hr2))
              h5)
            (Surface.stepFnIter_one hr3))
          h6)
        (Surface.stepFnIter_one hr4))
      h7)
    (Surface.stepFnIter_one hx)

end GoLean.RaftSeam.RoundVote
