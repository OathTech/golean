import GoLeanProofs.Specs.Raft.RoundVoteLit3
import GoLeanProofs.Specs.Raft.RoundVoteLit4
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVoteEqB — the MID segment of the MsgVote round's canonical
run (A4-U23): the rest of the vote-grant arm (r.send assembly)
through the send-assembly spill. One latitude draw. See
`RoundVoteEqA.lean`'s split note. -/

namespace GoLean.RaftSeam.RoundVote

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem mvWB1_out : symEvalWindowTB bfTB 2500 mvSB13 mvCB13
    = (2500, mvSB14, mvCB14) := by
  kernel_rfl

theorem mvWB2_out : symEvalWindowTB bfTB 2500 mvSB14 mvCB14
    = (2500, mvSB15, mvCB15) := by
  kernel_rfl

theorem mvWB3_out : symEvalWindowTB bfTB 1970 mvSB15 mvCB15
    = (1970, mvSB16, mvCB16) := by
  kernel_rfl

/-- The send-assembly appendSpill (latitude; the vote ring's X-series
starts — the MsgVoteResp appended to msgsAfterAppend). -/
theorem roundVote_spill1 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB16) (γC ρ mvCB16) (0 :: rest)
      = .ok (γC ρ mvCB17, γS ρ σ mvSB17, rest) := by
  kernel_rfl

/-- **The MID segment span** (6,971 steps, 1 latitude draw). -/
theorem roundVote_midSpan (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 6971 (γS ρ σ mvSB13) (γC ρ mvCB13) (0 :: rest)
      = .ok (γC ρ mvCB17, γS ρ σ mvSB17, rest) := by
  have h1 := symEvalWindowTB_refines mvWB1_out ρ σ (0 :: rest) hag
  have h2 := symEvalWindowTB_refines mvWB2_out ρ σ (0 :: rest) hag
  have h3 := symEvalWindowTB_refines mvWB3_out ρ σ (0 :: rest) hag
  have hs := roundVote_spill1 ρ σ rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain h1 h2)
      h3)
    (Surface.stepFnIter_one hs)

end GoLean.RaftSeam.RoundVote
