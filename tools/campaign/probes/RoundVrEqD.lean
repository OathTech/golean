import GoLeanProofs.Specs.Raft.RoundVrLit10
import GoLeanProofs.Specs.Raft.RoundVrLit11
import GoLeanProofs.Specs.Raft.RoundVrLit12
import GoLeanProofs.Specs.Raft.RoundVrLit13
import GoLeanProofs.Specs.Raft.RoundVrLit14
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVrEqD — segment D of the MsgVoteResp election-completion
round's canonical run (A4-U25): B48 -> B67, 7461 steps,
8 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundVrLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem vrWD28_out : symEvalWindowTB bfTB 2077 vrSB48 vrCB48
    = (2077, vrSB49, vrCB49) := by
  kernel_rfl

/-- Crossing 22 (spill; latitude unless noted). -/
theorem roundVr_x22 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB49) (γC ρ vrCB49) (0 :: rest)
      = .ok (γC ρ vrCB50, γS ρ σ vrSB50, rest) := by
  kernel_rfl

theorem vrWD29_out : symEvalWindowTB bfTB 435 vrSB50 vrCB50
    = (435, vrSB51, vrCB51) := by
  kernel_rfl

/-- Crossing 23 (spill; latitude unless noted). -/
theorem roundVr_x23 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB51) (γC ρ vrCB51) (0 :: rest)
      = .ok (γC ρ vrCB52, γS ρ σ vrSB52, rest) := by
  kernel_rfl

theorem vrWD30_out : symEvalWindowTB bfTB 49 vrSB52 vrCB52
    = (49, vrSB53, vrCB53) := by
  kernel_rfl

/-- Crossing 24 (spill; latitude unless noted). -/
theorem roundVr_x24 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB53) (γC ρ vrCB53) (0 :: rest)
      = .ok (γC ρ vrCB54, γS ρ σ vrSB54, rest) := by
  kernel_rfl

theorem vrWD31_out : symEvalWindowTB bfTB 98 vrSB54 vrCB54
    = (98, vrSB55, vrCB55) := by
  kernel_rfl

/-- Crossing 25 (spill; latitude unless noted). -/
theorem roundVr_x25 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB55) (γC ρ vrCB55) (0 :: rest)
      = .ok (γC ρ vrCB56, γS ρ σ vrSB56, rest) := by
  kernel_rfl

theorem vrWD32_out : symEvalWindowTB bfTB 49 vrSB56 vrCB56
    = (49, vrSB57, vrCB57) := by
  kernel_rfl

/-- Crossing 26 (spill; latitude unless noted). -/
theorem roundVr_x26 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB57) (γC ρ vrCB57) (0 :: rest)
      = .ok (γC ρ vrCB58, γS ρ σ vrSB58, rest) := by
  kernel_rfl

theorem vrWD33_out : symEvalWindowTB bfTB 1893 vrSB58 vrCB58
    = (1893, vrSB59, vrCB59) := by
  kernel_rfl

/-- Crossing 27 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x27 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB59) (γC ρ vrCB59) (0 :: rest)
      = .ok (γC ρ vrCB60, γS ρ σ vrSB60, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWD34_out : symEvalWindowTB bfTB 117 vrSB60 vrCB60
    = (117, vrSB61, vrCB61) := by
  kernel_rfl

/-- Crossing 28 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x28 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB61) (γC ρ vrCB61) (0 :: rest)
      = .ok (γC ρ vrCB62, γS ρ σ vrSB62, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWD35_out : symEvalWindowTB bfTB 117 vrSB62 vrCB62
    = (117, vrSB63, vrCB63) := by
  kernel_rfl

/-- Crossing 29 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x29 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB63) (γC ρ vrCB63) (0 :: rest)
      = .ok (γC ρ vrCB64, γS ρ σ vrSB64, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWD36_out : symEvalWindowTB bfTB 117 vrSB64 vrCB64
    = (117, vrSB65, vrCB65) := by
  kernel_rfl

/-- Crossing 30: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundVr_x30free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB65) (γC ρ vrCB65) rest
      = .ok (γC ρ vrCB66, γS ρ σ vrSB66, rest) := by
  kernel_rfl

theorem vrWD37_out : symEvalWindowTB bfTB 2500 vrSB66 vrCB66
    = (2500, vrSB67, vrCB67) := by
  kernel_rfl

/-- Segment span D: 7461 steps, 8 draw(s). -/
theorem roundVr_spanD (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7461 (γS ρ σ vrSB48) (γC ρ vrCB48) (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ vrCB67, γS ρ σ vrSB67, rest) := by
  have h0 := symEvalWindowTB_refines vrWD28_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h1 := roundVr_x22 ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines vrWD29_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h3 := roundVr_x23 ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h4 := symEvalWindowTB_refines vrWD30_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h5 := roundVr_x24 ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h6 := symEvalWindowTB_refines vrWD31_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h7 := roundVr_x25 ρ σ (0 :: 0 :: 0 :: 0 :: rest)
  have h8 := symEvalWindowTB_refines vrWD32_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have h9 := roundVr_x26 ρ σ (0 :: 0 :: 0 :: rest)
  have h10 := symEvalWindowTB_refines vrWD33_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have h11 := roundVr_x27 ρ σ hag (0 :: 0 :: rest)
  have h12 := symEvalWindowTB_refines vrWD34_out ρ σ (0 :: 0 :: rest) hag
  have h13 := roundVr_x28 ρ σ hag (0 :: rest)
  have h14 := symEvalWindowTB_refines vrWD35_out ρ σ (0 :: rest) hag
  have h15 := roundVr_x29 ρ σ hag (rest)
  have h16 := symEvalWindowTB_refines vrWD36_out ρ σ (rest) hag
  have h17 := roundVr_x30free ρ σ (rest)
  have h18 := symEvalWindowTB_refines vrWD37_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 (Surface.stepFnIter_one h1)) h2) (Surface.stepFnIter_one h3)) h4) (Surface.stepFnIter_one h5)) h6) (Surface.stepFnIter_one h7)) h8) (Surface.stepFnIter_one h9)) h10) (Surface.stepFnIter_one h11)) h12) (Surface.stepFnIter_one h13)) h14) (Surface.stepFnIter_one h15)) h16) (Surface.stepFnIter_one h17)) h18

end GoLean.RaftSeam.RoundVr
