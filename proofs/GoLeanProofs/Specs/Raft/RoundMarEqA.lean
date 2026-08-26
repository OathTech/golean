import GoLeanProofs.Specs.Raft.RoundMarLit1
import GoLeanProofs.Specs.Raft.RoundMarLit2
import GoLeanProofs.Specs.Raft.RoundMarLit3
import GoLeanProofs.Specs.Raft.RoundMarLit4
import GoLeanProofs.Specs.Raft.RoundVoteEqA
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMarEqA — the ARM segment of the MsgAppResp maybeCommit
round's canonical run (A4-U24): B0 → B19, 5,738 steps, 7 draws +
2 choice-free crossings. The SEMANTIC pick (x1, delivery); TWO
tracker-Visit mapIter triplets, each ending in a choice-free
mapIterK exhaustion-exit — maybeCommit's quorum walk
(`trk.Committed()`, x2–x4 + x5free) and bcastAppend's peer walk
(x6–x8 + x9free): the auto-discovered crossings a choice census
cannot see (U23 lesson (a), now at a THIRD round kind). The six
Visit mapIters iterate `map[uint64]*tracker.Progress` — the
defined-value-type table footprint — so they carry the `Agrees`
premise and rewrite through `RoundVote.γS_pin` (U23's finding; the
§7 second consumer, promotion noted in the ledger). See
`RoundMarLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem mrWA1_out : symEvalWindowTB bfTB 207 mrSB0 mrCB0
    = (207, mrSB1, mrCB1) := by
  kernel_rfl

/-- Crossing 1 (reflect; latitude unless noted). -/
theorem roundMar_x1 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mrSB1) (γC ρ mrCB1) (0 :: rest)
      = .ok (γC ρ mrCB2, γS ρ σ mrSB2, rest) := by
  kernel_rfl

theorem mrWA2_out : symEvalWindowTB bfTB 2500 mrSB2 mrCB2
    = (2500, mrSB3, mrCB3) := by
  kernel_rfl

theorem mrWA3_out : symEvalWindowTB bfTB 687 mrSB3 mrCB3
    = (687, mrSB4, mrCB4) := by
  kernel_rfl

/-- Crossing 2: maybeCommit quorum-Visit mapIter (latitude: map-iteration
order; tracker map = defined value type, so table-pinned). -/
theorem roundMar_x2 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mrSB4) (γC ρ mrCB4) (0 :: rest)
      = .ok (γC ρ mrCB5, γS ρ σ mrSB5, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem mrWA4_out : symEvalWindowTB bfTB 117 mrSB5 mrCB5
    = (117, mrSB6, mrCB6) := by
  kernel_rfl

/-- Crossing 3: maybeCommit quorum-Visit mapIter (latitude: map-iteration
order; tracker map = defined value type, so table-pinned). -/
theorem roundMar_x3 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mrSB6) (γC ρ mrCB6) (0 :: rest)
      = .ok (γC ρ mrCB7, γS ρ σ mrSB7, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem mrWA5_out : symEvalWindowTB bfTB 117 mrSB7 mrCB7
    = (117, mrSB8, mrCB8) := by
  kernel_rfl

/-- Crossing 4: maybeCommit quorum-Visit mapIter (latitude: map-iteration
order; tracker map = defined value type, so table-pinned). -/
theorem roundMar_x4 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mrSB8) (γC ρ mrCB8) (0 :: rest)
      = .ok (γC ρ mrCB9, γS ρ σ mrSB9, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem mrWA6_out : symEvalWindowTB bfTB 117 mrSB9 mrCB9
    = (117, mrSB10, mrCB10) := by
  kernel_rfl

/-- Crossing 5: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundMar_x5free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mrSB10) (γC ρ mrCB10) rest
      = .ok (γC ρ mrCB11, γS ρ σ mrSB11, rest) := by
  kernel_rfl

theorem mrWA7_out : symEvalWindowTB bfTB 1900 mrSB11 mrCB11
    = (1900, mrSB12, mrCB12) := by
  kernel_rfl

/-- Crossing 6: bcastAppend peer-Visit mapIter (latitude: map-iteration
order; tracker map = defined value type, so table-pinned). -/
theorem roundMar_x6 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mrSB12) (γC ρ mrCB12) (0 :: rest)
      = .ok (γC ρ mrCB13, γS ρ σ mrSB13, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem mrWA8_out : symEvalWindowTB bfTB 28 mrSB13 mrCB13
    = (28, mrSB14, mrCB14) := by
  kernel_rfl

/-- Crossing 7: bcastAppend peer-Visit mapIter (latitude: map-iteration
order; tracker map = defined value type, so table-pinned). -/
theorem roundMar_x7 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mrSB14) (γC ρ mrCB14) (0 :: rest)
      = .ok (γC ρ mrCB15, γS ρ σ mrSB15, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem mrWA9_out : symEvalWindowTB bfTB 28 mrSB15 mrCB15
    = (28, mrSB16, mrCB16) := by
  kernel_rfl

/-- Crossing 8: bcastAppend peer-Visit mapIter (latitude: map-iteration
order; tracker map = defined value type, so table-pinned). -/
theorem roundMar_x8 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mrSB16) (γC ρ mrCB16) (0 :: rest)
      = .ok (γC ρ mrCB17, γS ρ σ mrSB17, rest) := by
  simp only [RoundVote.γS_pin hag]
  kernel_rfl

theorem mrWA10_out : symEvalWindowTB bfTB 28 mrSB17 mrCB17
    = (28, mrSB18, mrCB18) := by
  kernel_rfl

/-- Crossing 9: CHOICE-FREE mirror quit (reflect); holds for every stream. -/
theorem roundMar_x9free (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mrSB18) (γC ρ mrCB18) rest
      = .ok (γC ρ mrCB19, γS ρ σ mrSB19, rest) := by
  kernel_rfl

/-- Segment span A: 5738 steps, 7 draw(s). -/
theorem roundMar_spanA (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 5738 (γS ρ σ mrSB0) (γC ρ mrCB0) (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ mrCB19, γS ρ σ mrSB19, rest) := by
  have h0 := symEvalWindowTB_refines mrWA1_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h1 := roundMar_x1 ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines mrWA2_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h3 := symEvalWindowTB_refines mrWA3_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h4 := roundMar_x2 ρ σ hag (0 :: 0 :: 0 :: 0 :: 0 :: rest)
  have h5 := symEvalWindowTB_refines mrWA4_out ρ σ (0 :: 0 :: 0 :: 0 :: 0 :: rest) hag
  have h6 := roundMar_x3 ρ σ hag (0 :: 0 :: 0 :: 0 :: rest)
  have h7 := symEvalWindowTB_refines mrWA5_out ρ σ (0 :: 0 :: 0 :: 0 :: rest) hag
  have h8 := roundMar_x4 ρ σ hag (0 :: 0 :: 0 :: rest)
  have h9 := symEvalWindowTB_refines mrWA6_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have h10 := roundMar_x5free ρ σ (0 :: 0 :: 0 :: rest)
  have h11 := symEvalWindowTB_refines mrWA7_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have h12 := roundMar_x6 ρ σ hag (0 :: 0 :: rest)
  have h13 := symEvalWindowTB_refines mrWA8_out ρ σ (0 :: 0 :: rest) hag
  have h14 := roundMar_x7 ρ σ hag (0 :: rest)
  have h15 := symEvalWindowTB_refines mrWA9_out ρ σ (0 :: rest) hag
  have h16 := roundMar_x8 ρ σ hag (rest)
  have h17 := symEvalWindowTB_refines mrWA10_out ρ σ (rest) hag
  have h18 := roundMar_x9free ρ σ (rest)
  exact Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain (Surface.stepFnIter_chain h0 (Surface.stepFnIter_one h1)) h2) h3) (Surface.stepFnIter_one h4)) h5) (Surface.stepFnIter_one h6)) h7) (Surface.stepFnIter_one h8)) h9) (Surface.stepFnIter_one h10)) h11) (Surface.stepFnIter_one h12)) h13) (Surface.stepFnIter_one h14)) h15) (Surface.stepFnIter_one h16)) h17) (Surface.stepFnIter_one h18)

end GoLean.RaftSeam.RoundMar
