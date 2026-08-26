import GoLeanProofs.Specs.Raft.RoundMarLit6
import GoLeanProofs.Specs.Raft.RoundMarLit7
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMarEqD — segment D of the MsgAppResp maybeCommit
round's canonical run (A4-U24): B26 -> B33, 7170 steps,
2 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundMarLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem mrWD17_out : symEvalWindowTB bfTB 475 mrSB26 mrCB26
    = (475, mrSB27, mrCB27) := by
  kernel_rfl

/-- Crossing 11 (spill; latitude unless noted). -/
theorem roundMar_x11 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mrSB27) (γC ρ mrCB27) (0 :: rest)
      = .ok (γC ρ mrCB28, γS ρ σ mrSB28, rest) := by
  kernel_rfl

theorem mrWD18_out : symEvalWindowTB bfTB 49 mrSB28 mrCB28
    = (49, mrSB29, mrCB29) := by
  kernel_rfl

/-- Crossing 12 (spill; latitude unless noted). -/
theorem roundMar_x12 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mrSB29) (γC ρ mrCB29) (0 :: rest)
      = .ok (γC ρ mrCB30, γS ρ σ mrSB30, rest) := by
  kernel_rfl

theorem mrWD19_out : symEvalWindowTB bfTB 2500 mrSB30 mrCB30
    = (2500, mrSB31, mrCB31) := by
  kernel_rfl

theorem mrWD20_out : symEvalWindowTB bfTB 2500 mrSB31 mrCB31
    = (2500, mrSB32, mrCB32) := by
  kernel_rfl

theorem mrWD21_out : symEvalWindowTB bfTB 1644 mrSB32 mrCB32
    = (1644, mrSB33, mrCB33) := by
  kernel_rfl

/-- Segment span D: 7170 steps, 2 draw(s). -/
theorem roundMar_spanD (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7170 (γS ρ σ mrSB26) (γC ρ mrCB26) (0 :: 0 :: rest)
      = .ok (γC ρ mrCB33, γS ρ σ mrSB33, rest) := by
  have h0 := symEvalWindowTB_refines mrWD17_out ρ σ (0 :: 0 :: rest) hag
  have h1 := roundMar_x11 ρ σ (0 :: rest)
  have h2 := symEvalWindowTB_refines mrWD18_out ρ σ (0 :: rest) hag
  have h3 := roundMar_x12 ρ σ (rest)
  have h4 := symEvalWindowTB_refines mrWD19_out ρ σ (rest) hag
  have h5 := symEvalWindowTB_refines mrWD20_out ρ σ (rest) hag
  have h6 := symEvalWindowTB_refines mrWD21_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 (Surface.stepFnIter_one h1)) h2) (Surface.stepFnIter_one h3)) h4) h5) h6

end GoLean.RaftSeam.RoundMar
