import GoLeanProofs.Specs.Raft.RoundMarLit4
import GoLeanProofs.Specs.Raft.RoundMarLit5
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMarEqB — segment B of the MsgAppResp maybeCommit
round's canonical run (A4-U24): B19 -> B23, 5816 steps,
1 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundMarLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem mrWB11_out : symEvalWindowTB bfTB 2500 mrSB19 mrCB19
    = (2500, mrSB20, mrCB20) := by
  kernel_rfl

theorem mrWB12_out : symEvalWindowTB bfTB 815 mrSB20 mrCB20
    = (815, mrSB21, mrCB21) := by
  kernel_rfl

/-- Crossing 10 (spill; latitude unless noted). -/
theorem roundMar_x10 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mrSB21) (γC ρ mrCB21) (0 :: rest)
      = .ok (γC ρ mrCB22, γS ρ σ mrSB22, rest) := by
  kernel_rfl

theorem mrWB13_out : symEvalWindowTB bfTB 2500 mrSB22 mrCB22
    = (2500, mrSB23, mrCB23) := by
  kernel_rfl

/-- Segment span B: 5816 steps, 1 draw(s). -/
theorem roundMar_spanB (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 5816 (γS ρ σ mrSB19) (γC ρ mrCB19) (0 :: rest)
      = .ok (γC ρ mrCB23, γS ρ σ mrSB23, rest) := by
  have h0 := symEvalWindowTB_refines mrWB11_out ρ σ (0 :: rest) hag
  have h1 := symEvalWindowTB_refines mrWB12_out ρ σ (0 :: rest) hag
  have h2 := roundMar_x10 ρ σ (rest)
  have h3 := symEvalWindowTB_refines mrWB13_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 h1) (Surface.stepFnIter_one h2)) h3

end GoLean.RaftSeam.RoundMar
