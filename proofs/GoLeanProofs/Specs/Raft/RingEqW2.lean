import GoLeanProofs.Specs.Raft.RingLit1
import GoLeanProofs.Specs.Raft.RingLit2
import GoLeanProofs.Specs.Raft.RingLit3
import GoLeanProofs.Specs.Raft.RingLit4
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RingEqW2 — the W2 (acceptReady + storage-write + send) window
links, four crossings, and span (C2c; see `RingEqW1.lean`'s split
note and `RingEquation.lean`'s design docstring). -/

namespace GoLean.RaftSeam.Ring

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-! ## W2 — the acceptReady + storage-write + send span -/

theorem maW2a_out : symEvalWindowTB bfTB 1858 maS1 maC1
    = (1858, maSP2a, maCP2a) := by
  kernel_rfl

/-- Crossing X2 (the storage-append-resp `Responses` build). -/
theorem ma_spill2 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSP2a) (γC ρ maCP2a) (0 :: rest)
      = .ok (γC ρ maCP2b, γS ρ σ maSP2b, rest) := by
  kernel_rfl

theorem maW2b_out : symEvalWindowTB bfTB 2772 maSP2b maCP2b
    = (2772, maSP3a, maCP3a) := by
  kernel_rfl

/-- Crossing X3 (**the MemoryStorage.Append ents spill** — the
storage-resp axis's write: old backing `[dummy (1,1)]` at cap 1,
grown by the appended-entry pointer). -/
theorem ma_spill3 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSP3a) (γC ρ maCP3a) (0 :: rest)
      = .ok (γC ρ maCP3b, γS ρ σ maSP3b, rest) := by
  kernel_rfl

theorem maW2c_out : symEvalWindowTB bfTB 362 maSP3b maCP3b
    = (362, maSP4a, maCP4a) := by
  kernel_rfl

/-- Crossing X4 (the harness net append — the MsgAppResp entering the
doctored 1-cap net). -/
theorem ma_spill4 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSP4a) (γC ρ maCP4a) (0 :: rest)
      = .ok (γC ρ maCP4b, γS ρ σ maSP4b, rest) := by
  kernel_rfl

theorem maW2d_out : symEvalWindowTB bfTB 49 maSP4b maCP4b
    = (49, maSP5a, maCP5a) := by
  kernel_rfl

/-- Crossing X5 (the harness live-flag append, `[]bool`). -/
theorem ma_spill5 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSP5a) (γC ρ maCP5a) (0 :: rest)
      = .ok (γC ρ maCP5b, γS ρ σ maSP5b, rest) := by
  kernel_rfl

theorem maW2e_out : symEvalWindowTB bfTB 140 maSP5b maCP5b
    = (140, maS2, maC2) := by
  kernel_rfl

/-- **The acceptReady span**: acceptReady, both storage-resp message
builds, SetHardState, MemoryStorage.Append, the harness net/live
sends — 5,185 steps, four draws. -/
theorem ring_w2_span (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 5185 (γS ρ σ maS1) (γC ρ maC1) (0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ maC2, γS ρ σ maS2, rest) := by
  have h1 := symEvalWindowTB_refines maW2a_out ρ σ
    (0 :: 0 :: 0 :: 0 :: rest) hag
  have hx2 := ma_spill2 ρ σ (0 :: 0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines maW2b_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have hx3 := ma_spill3 ρ σ (0 :: 0 :: rest)
  have h3 := symEvalWindowTB_refines maW2c_out ρ σ (0 :: 0 :: rest) hag
  have hx4 := ma_spill4 ρ σ (0 :: rest)
  have h4 := symEvalWindowTB_refines maW2d_out ρ σ (0 :: rest) hag
  have hx5 := ma_spill5 ρ σ rest
  have h5 := symEvalWindowTB_refines maW2e_out ρ σ rest hag
  have hc := Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain
          (Surface.stepFnIter_chain
            (Surface.stepFnIter_chain
              (Surface.stepFnIter_chain
                (Surface.stepFnIter_chain h1 (Surface.stepFnIter_one hx2))
                h2)
              (Surface.stepFnIter_one hx3))
            h3)
          (Surface.stepFnIter_one hx4))
        h4)
      (Surface.stepFnIter_one hx5))
    h5
  exact hc

end GoLean.RaftSeam.Ring
