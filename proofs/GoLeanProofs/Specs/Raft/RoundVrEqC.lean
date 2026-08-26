import GoLeanProofs.Specs.Raft.RoundVrLit10
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVrEqC — segment C of the MsgVoteResp election-completion
round's canonical run (A4-U25): B45 -> B48, 7500 steps,
0 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundVrLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem vrWC25_out : symEvalWindowTB bfTB 2500 vrSB45 vrCB45
    = (2500, vrSB46, vrCB46) := by
  kernel_rfl

theorem vrWC26_out : symEvalWindowTB bfTB 2500 vrSB46 vrCB46
    = (2500, vrSB47, vrCB47) := by
  kernel_rfl

theorem vrWC27_out : symEvalWindowTB bfTB 2500 vrSB47 vrCB47
    = (2500, vrSB48, vrCB48) := by
  kernel_rfl

/-- Segment span C: 7500 steps, 0 draw(s). -/
theorem roundVr_spanC (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7500 (γS ρ σ vrSB45) (γC ρ vrCB45) (rest)
      = .ok (γC ρ vrCB48, γS ρ σ vrSB48, rest) := by
  have h0 := symEvalWindowTB_refines vrWC25_out ρ σ (rest) hag
  have h1 := symEvalWindowTB_refines vrWC26_out ρ σ (rest) hag
  have h2 := symEvalWindowTB_refines vrWC27_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 h1) h2

end GoLean.RaftSeam.RoundVr
