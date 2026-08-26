import GoLeanProofs.Specs.Raft.RoundVrLit7
import GoLeanProofs.Specs.Raft.RoundVrLit8
import GoLeanProofs.Specs.Raft.RoundVrLit9
import GoLeanProofs.Specs.Raft.RoundVrLit10
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVrEqB — segment B of the MsgVoteResp election-completion
round's canonical run (A4-U25): B30 -> B45, 7403 steps,
6 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundVrLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem vrWB17_out : symEvalWindowTB bfTB 1740 vrSB30 vrCB30
    = (1740, vrSB31, vrCB31) := by
  kernel_rfl

/-- Crossing 15 (spill; latitude unless noted). -/
theorem roundVr_x15 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB31) (γC ρ vrCB31) (0 :: rest)
      = .ok (γC ρ vrCB32, γS ρ σ vrSB32, rest) := by
  kernel_rfl

theorem vrWB18_out : symEvalWindowTB bfTB 1180 vrSB32 vrCB32
    = (1180, vrSB33, vrCB33) := by
  kernel_rfl

/-- Crossing 16 (spill; latitude unless noted). -/
theorem roundVr_x16 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB33) (γC ρ vrCB33) (0 :: rest)
      = .ok (γC ρ vrCB34, γS ρ σ vrSB34, rest) := by
  kernel_rfl

theorem vrWB19_out : symEvalWindowTB bfTB 191 vrSB34 vrCB34
    = (191, vrSB35, vrCB35) := by
  kernel_rfl

/-- Crossing 17 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x17 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB35) (γC ρ vrCB35) (0 :: rest)
      = .ok (γC ρ vrCB36, γS ρ σ vrSB36, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWB20_out : symEvalWindowTB bfTB 28 vrSB36 vrCB36
    = (28, vrSB37, vrCB37) := by
  kernel_rfl

/-- Crossing 18 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x18 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB37) (γC ρ vrCB37) (0 :: rest)
      = .ok (γC ρ vrCB38, γS ρ σ vrSB38, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWB21_out : symEvalWindowTB bfTB 28 vrSB38 vrCB38
    = (28, vrSB39, vrCB39) := by
  kernel_rfl

/-- Crossing 19 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x19 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB39) (γC ρ vrCB39) (0 :: rest)
      = .ok (γC ρ vrCB40, γS ρ σ vrSB40, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWB22_out : symEvalWindowTB bfTB 28 vrSB40 vrCB40
    = (28, vrSB41, vrCB41) := by
  kernel_rfl

/-- Crossing 20: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundVr_x20free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB41) (γC ρ vrCB41) rest
      = .ok (γC ρ vrCB42, γS ρ σ vrSB42, rest) := by
  kernel_rfl

theorem vrWB23_out : symEvalWindowTB bfTB 2500 vrSB42 vrCB42
    = (2500, vrSB43, vrCB43) := by
  kernel_rfl

theorem vrWB24_out : symEvalWindowTB bfTB 1701 vrSB43 vrCB43
    = (1701, vrSB44, vrCB44) := by
  kernel_rfl

/-- Crossing 21 (spill; latitude unless noted). -/
theorem roundVr_x21 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB44) (γC ρ vrCB44) (0 :: rest)
      = .ok (γC ρ vrCB45, γS ρ σ vrSB45, rest) := by
  kernel_rfl

/-- Segment span B: 7403 steps, 6 draw(s). -/
theorem roundVr_spanB (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7403 (γS ρ σ vrSB30) (γC ρ vrCB30) (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ vrCB45, γS ρ σ vrSB45, rest) := by
  have h0 := symEvalWindowTB_refines vrWB17_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h1 := roundVr_x15 ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines vrWB18_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h3 := roundVr_x16 ρ σ (0 :: 0 :: 0 :: 0 :: rest)
  have h4 := symEvalWindowTB_refines vrWB19_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have h5 := roundVr_x17 ρ σ hag (0 :: 0 :: 0 :: rest)
  have h6 := symEvalWindowTB_refines vrWB20_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have h7 := roundVr_x18 ρ σ hag (0 :: 0 :: rest)
  have h8 := symEvalWindowTB_refines vrWB21_out ρ σ (0 :: 0 :: rest) hag
  have h9 := roundVr_x19 ρ σ hag (0 :: rest)
  have h10 := symEvalWindowTB_refines vrWB22_out ρ σ (0 :: rest) hag
  have h11 := roundVr_x20free ρ σ (0 :: rest)
  have h12 := symEvalWindowTB_refines vrWB23_out ρ σ (0 :: rest) hag
  have h13 := symEvalWindowTB_refines vrWB24_out ρ σ (0 :: rest) hag
  have h14 := roundVr_x21 ρ σ (rest)
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 (Surface.stepFnIter_one h1)) h2) (Surface.stepFnIter_one h3)) h4) (Surface.stepFnIter_one h5)) h6) (Surface.stepFnIter_one h7)) h8) (Surface.stepFnIter_one h9)) h10) (Surface.stepFnIter_one h11)) h12) h13) (Surface.stepFnIter_one h14)

end GoLean.RaftSeam.RoundVr
