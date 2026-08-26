import GoLeanProofs.Specs.Raft.RoundVoteLit4
import GoLeanProofs.Specs.Raft.RoundVoteLit5
import GoLeanProofs.Specs.Raft.RoundVoteLit6
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVoteEqC — the RING+SUFFIX segment of the MsgVote round's
canonical run (A4-U23): the harvest ring (hardstate-only — SetHardState
persists Term/Vote, NO storage-resp arms: the U21 census's round-kind
matrix row) and the driver suffix. Three latitude draws
(Ready-assembly and the two accept-side spills). See
`RoundVoteEqA.lean`'s split note. -/

namespace GoLean.RaftSeam.RoundVote

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem mvWC1_out : symEvalWindowTB bfTB 2500 mvSB17 mvCB17
    = (2500, mvSB18, mvCB18) := by
  kernel_rfl

theorem mvWC2_out : symEvalWindowTB bfTB 143 mvSB18 mvCB18
    = (143, mvSB19, mvCB19) := by
  kernel_rfl

/-- The Ready-assembly appendSpill (latitude). -/
theorem roundVote_spill2 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB19) (γC ρ mvCB19) (0 :: rest)
      = .ok (γC ρ mvCB20, γS ρ σ mvSB20, rest) := by
  kernel_rfl

theorem mvWC3_out : symEvalWindowTB bfTB 1784 mvSB20 mvCB20
    = (1784, mvSB21, mvCB21) := by
  kernel_rfl

/-- Accept-side appendSpill 1 (latitude; the harness net send). -/
theorem roundVote_spill3 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB21) (γC ρ mvCB21) (0 :: rest)
      = .ok (γC ρ mvCB22, γS ρ σ mvSB22, rest) := by
  kernel_rfl

theorem mvWC4_out : symEvalWindowTB bfTB 49 mvSB22 mvCB22
    = (49, mvSB23, mvCB23) := by
  kernel_rfl

/-- Accept-side appendSpill 2 (latitude; the harness live send). -/
theorem roundVote_spill4 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB23) (γC ρ mvCB23) (0 :: rest)
      = .ok (γC ρ mvCB24, γS ρ σ mvSB24, rest) := by
  kernel_rfl

theorem mvWC5_out : symEvalWindowTB bfTB 2500 mvSB24 mvCB24
    = (2500, mvSB25, mvCB25) := by
  kernel_rfl

theorem mvWC6_out : symEvalWindowTB bfTB 1547 mvSB25 mvCB25
    = (1547, mvSB26, mvCB26) := by
  kernel_rfl

/-- **The RING+SUFFIX segment span** (8,526 steps, 3 latitude
draws). -/
theorem roundVote_suffixSpan (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 8526 (γS ρ σ mvSB17) (γC ρ mvCB17) (0 :: 0 :: 0 :: rest)
      = .ok (γC ρ mvCB26, γS ρ σ mvSB26, rest) := by
  have h1 := symEvalWindowTB_refines mvWC1_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have h2 := symEvalWindowTB_refines mvWC2_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have hs2 := roundVote_spill2 ρ σ (0 :: 0 :: rest)
  have h3 := symEvalWindowTB_refines mvWC3_out ρ σ (0 :: 0 :: rest) hag
  have hs3 := roundVote_spill3 ρ σ (0 :: rest)
  have h4 := symEvalWindowTB_refines mvWC4_out ρ σ (0 :: rest) hag
  have hs4 := roundVote_spill4 ρ σ rest
  have h5 := symEvalWindowTB_refines mvWC5_out ρ σ rest hag
  have h6 := symEvalWindowTB_refines mvWC6_out ρ σ rest hag
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain
          (Surface.stepFnIter_chain
            (Surface.stepFnIter_chain
              (Surface.stepFnIter_chain
                (Surface.stepFnIter_chain h1 h2)
                (Surface.stepFnIter_one hs2))
              h3)
            (Surface.stepFnIter_one hs3))
          h4)
        (Surface.stepFnIter_one hs4))
      h5)
    h6

end GoLean.RaftSeam.RoundVote
