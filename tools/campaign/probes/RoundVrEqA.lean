import GoLeanProofs.Specs.Raft.RoundVrLit1
import GoLeanProofs.Specs.Raft.RoundVrLit2
import GoLeanProofs.Specs.Raft.RoundVrLit3
import GoLeanProofs.Specs.Raft.RoundVrLit4
import GoLeanProofs.Specs.Raft.RoundVrLit5
import GoLeanProofs.Specs.Raft.RoundVrLit6
import GoLeanProofs.Specs.Raft.RoundVrLit7
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundVrEqA — segment A of the MsgVoteResp election-completion
round's canonical run (A4-U25): B0 -> B30, 7231 steps,
11 draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundVrLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem vrWA1_out : symEvalWindowTB bfTB 207 vrSB0 vrCB0
    = (207, vrSB1, vrCB1) := by
  kernel_rfl

/-- Crossing 1 (reflect; latitude unless noted). -/
theorem roundVr_x1 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB1) (γC ρ vrCB1) (0 :: rest)
      = .ok (γC ρ vrCB2, γS ρ σ vrSB2, rest) := by
  kernel_rfl

theorem vrWA2_out : symEvalWindowTB bfTB 2500 vrSB2 vrCB2
    = (2500, vrSB3, vrCB3) := by
  kernel_rfl

theorem vrWA3_out : symEvalWindowTB bfTB 252 vrSB3 vrCB3
    = (252, vrSB4, vrCB4) := by
  kernel_rfl

/-- Crossing 2 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x2 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB4) (γC ρ vrCB4) (0 :: rest)
      = .ok (γC ρ vrCB5, γS ρ σ vrSB5, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA4_out : symEvalWindowTB bfTB 61 vrSB5 vrCB5
    = (61, vrSB6, vrCB6) := by
  kernel_rfl

/-- Crossing 3 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x3 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB6) (γC ρ vrCB6) (0 :: rest)
      = .ok (γC ρ vrCB7, γS ρ σ vrSB7, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA5_out : symEvalWindowTB bfTB 61 vrSB7 vrCB7
    = (61, vrSB8, vrCB8) := by
  kernel_rfl

/-- Crossing 4 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x4 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB8) (γC ρ vrCB8) (0 :: rest)
      = .ok (γC ρ vrCB9, γS ρ σ vrSB9, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA6_out : symEvalWindowTB bfTB 46 vrSB9 vrCB9
    = (46, vrSB10, vrCB10) := by
  kernel_rfl

/-- Crossing 5: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundVr_x5free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB10) (γC ρ vrCB10) rest
      = .ok (γC ρ vrCB11, γS ρ σ vrSB11, rest) := by
  kernel_rfl

theorem vrWA7_out : symEvalWindowTB bfTB 59 vrSB11 vrCB11
    = (59, vrSB12, vrCB12) := by
  kernel_rfl

/-- Crossing 6 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x6 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB12) (γC ρ vrCB12) (0 :: rest)
      = .ok (γC ρ vrCB13, γS ρ σ vrSB13, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA8_out : symEvalWindowTB bfTB 48 vrSB13 vrCB13
    = (48, vrSB14, vrCB14) := by
  kernel_rfl

/-- Crossing 7 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x7 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB14) (γC ρ vrCB14) (0 :: rest)
      = .ok (γC ρ vrCB15, γS ρ σ vrSB15, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA9_out : symEvalWindowTB bfTB 48 vrSB15 vrCB15
    = (48, vrSB16, vrCB16) := by
  kernel_rfl

/-- Crossing 8 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x8 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB16) (γC ρ vrCB16) (0 :: rest)
      = .ok (γC ρ vrCB17, γS ρ σ vrSB17, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA10_out : symEvalWindowTB bfTB 46 vrSB17 vrCB17
    = (46, vrSB18, vrCB18) := by
  kernel_rfl

/-- Crossing 9: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundVr_x9free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB18) (γC ρ vrCB18) rest
      = .ok (γC ρ vrCB19, γS ρ σ vrSB19, rest) := by
  kernel_rfl

theorem vrWA11_out : symEvalWindowTB bfTB 1122 vrSB19 vrCB19
    = (1122, vrSB20, vrCB20) := by
  kernel_rfl

/-- Crossing 10 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x10 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB20) (γC ρ vrCB20) (0 :: rest)
      = .ok (γC ρ vrCB21, γS ρ σ vrSB21, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA12_out : symEvalWindowTB bfTB 183 vrSB21 vrCB21
    = (183, vrSB22, vrCB22) := by
  kernel_rfl

/-- Crossing 11 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x11 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB22) (γC ρ vrCB22) (0 :: rest)
      = .ok (γC ρ vrCB23, γS ρ σ vrSB23, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA13_out : symEvalWindowTB bfTB 28 vrSB23 vrCB23
    = (28, vrSB24, vrCB24) := by
  kernel_rfl

/-- Crossing 12 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x12 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB24) (γC ρ vrCB24) (0 :: rest)
      = .ok (γC ρ vrCB25, γS ρ σ vrSB25, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA14_out : symEvalWindowTB bfTB 28 vrSB25 vrCB25
    = (28, vrSB26, vrCB26) := by
  kernel_rfl

/-- Crossing 13 (reflect; latitude: map-iteration order; table-pinned per the U23 finding). -/
theorem roundVr_x13 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ vrSB26) (γC ρ vrCB26) (0 :: rest)
      = .ok (γC ρ vrCB27, γS ρ σ vrSB27, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem vrWA15_out : symEvalWindowTB bfTB 28 vrSB27 vrCB27
    = (28, vrSB28, vrCB28) := by
  kernel_rfl

/-- Crossing 14: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundVr_x14free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ vrSB28) (γC ρ vrCB28) rest
      = .ok (γC ρ vrCB29, γS ρ σ vrSB29, rest) := by
  kernel_rfl

theorem vrWA16_out : symEvalWindowTB bfTB 2500 vrSB29 vrCB29
    = (2500, vrSB30, vrCB30) := by
  kernel_rfl

/-- Segment span A: 7231 steps, 11 draw(s). -/
theorem roundVr_spanA (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7231 (γS ρ σ vrSB0) (γC ρ vrCB0) (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ vrCB30, γS ρ σ vrSB30, rest) := by
  have h0 := symEvalWindowTB_refines vrWA1_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h1 := roundVr_x1 ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines vrWA2_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h3 := symEvalWindowTB_refines vrWA3_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h4 := roundVr_x2 ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h5 := symEvalWindowTB_refines vrWA4_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h6 := roundVr_x3 ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h7 := symEvalWindowTB_refines vrWA5_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h8 := roundVr_x4 ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h9 := symEvalWindowTB_refines vrWA6_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h10 := roundVr_x5free ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h11 := symEvalWindowTB_refines vrWA7_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h12 := roundVr_x6 ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h13 := symEvalWindowTB_refines vrWA8_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h14 := roundVr_x7 ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h15 := symEvalWindowTB_refines vrWA9_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h16 := roundVr_x8 ρ σ hag (0 :: 0 :: 0 :: 0 :: rest)
  have h17 := symEvalWindowTB_refines vrWA10_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have h18 := roundVr_x9free ρ σ (0 :: 0 :: 0 :: 0 :: rest)
  have h19 := symEvalWindowTB_refines vrWA11_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have h20 := roundVr_x10 ρ σ hag (0 :: 0 :: 0 :: rest)
  have h21 := symEvalWindowTB_refines vrWA12_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have h22 := roundVr_x11 ρ σ hag (0 :: 0 :: rest)
  have h23 := symEvalWindowTB_refines vrWA13_out ρ σ (0 :: 0 :: rest) hag
  have h24 := roundVr_x12 ρ σ hag (0 :: rest)
  have h25 := symEvalWindowTB_refines vrWA14_out ρ σ (0 :: rest) hag
  have h26 := roundVr_x13 ρ σ hag (rest)
  have h27 := symEvalWindowTB_refines vrWA15_out ρ σ (rest) hag
  have h28 := roundVr_x14free ρ σ (rest)
  have h29 := symEvalWindowTB_refines vrWA16_out ρ σ (rest) hag
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 (Surface.stepFnIter_one h1)) h2) h3) (Surface.stepFnIter_one h4)) h5) (Surface.stepFnIter_one h6)) h7) (Surface.stepFnIter_one h8)) h9) (Surface.stepFnIter_one h10)) h11) (Surface.stepFnIter_one h12)) h13) (Surface.stepFnIter_one h14)) h15) (Surface.stepFnIter_one h16)) h17) (Surface.stepFnIter_one h18)) h19) (Surface.stepFnIter_one h20)) h21) (Surface.stepFnIter_one h22)) h23) (Surface.stepFnIter_one h24)) h25) (Surface.stepFnIter_one h26)) h27) (Surface.stepFnIter_one h28)) h29

end GoLean.RaftSeam.RoundVr
