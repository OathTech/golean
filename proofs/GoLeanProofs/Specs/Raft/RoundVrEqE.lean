import GoLeanProofs.Specs.Raft.RoundVrLit14
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVrEqE — segment E of the MsgVoteResp election-completion
round's canonical run (A4-U25): B67 -> B69, 3679 steps,
0 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundVrLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem vrWE38_out : symEvalWindowTB bfTB 2500 vrSB67 vrCB67
    = (2500, vrSB68, vrCB68) := by
  kernel_rfl

theorem vrWE39_out : symEvalWindowTB bfTB 1179 vrSB68 vrCB68
    = (1179, vrSB69, vrCB69) := by
  kernel_rfl

/-- Segment span E: 3679 steps, 0 draw(s). -/
theorem roundVr_spanE (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 3679 (γS ρ σ vrSB67) (γC ρ vrCB67) (rest)
      = .ok (γC ρ vrCB69, γS ρ σ vrSB69, rest) := by
  have h0 := symEvalWindowTB_refines vrWE38_out ρ σ (rest) hag
  have h1 := symEvalWindowTB_refines vrWE39_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain h0 h1

end GoLean.RaftSeam.RoundVr
