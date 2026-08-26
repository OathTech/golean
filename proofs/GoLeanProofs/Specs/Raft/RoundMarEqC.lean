import GoLeanProofs.Specs.Raft.RoundMarLit5
import GoLeanProofs.Specs.Raft.RoundMarLit6
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMarEqC — segment C of the MsgAppResp maybeCommit
round's canonical run (A4-U24): B23 -> B26, 7500 steps,
0 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundMarLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem mrWC14_out : symEvalWindowTB bfTB 2500 mrSB23 mrCB23
    = (2500, mrSB24, mrCB24) := by
  kernel_rfl

theorem mrWC15_out : symEvalWindowTB bfTB 2500 mrSB24 mrCB24
    = (2500, mrSB25, mrCB25) := by
  kernel_rfl

theorem mrWC16_out : symEvalWindowTB bfTB 2500 mrSB25 mrCB25
    = (2500, mrSB26, mrCB26) := by
  kernel_rfl

/-- Segment span C: 7500 steps, 0 draw(s). -/
theorem roundMar_spanC (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7500 (γS ρ σ mrSB23) (γC ρ mrCB23) (rest)
      = .ok (γC ρ mrCB26, γS ρ σ mrSB26, rest) := by
  have h0 := symEvalWindowTB_refines mrWC14_out ρ σ (rest) hag
  have h1 := symEvalWindowTB_refines mrWC15_out ρ σ (rest) hag
  have h2 := symEvalWindowTB_refines mrWC16_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 h1) h2

end GoLean.RaftSeam.RoundMar
