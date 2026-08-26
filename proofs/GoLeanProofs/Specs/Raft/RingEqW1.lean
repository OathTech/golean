import GoLeanProofs.Specs.Raft.RingLit1
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RingEqW1 — the W1 (Ready-assembly) window links, crossing, and
span (C2c; split from `RingEquation.lean` so the four window groups'
kernel work runs in PARALLEL modules — the one-module serial form
measured out at >63 min. The design record is `RingEquation.lean`'s
module docstring.) -/

namespace GoLean.RaftSeam.Ring

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-! ## W1 — the Ready-assembly span (HasReady → acceptReady call) -/

/-- Window link (kernel-checked mirror walk; drift alarm). -/
theorem maW1a_out : symEvalWindowTB bfTB 3257 maS0 maC0
    = (3257, maSP1a, maCP1a) := by
  kernel_rfl

/-- Crossing X1 (`[]*Message` spill, draw 0) — a DIRECT machine step
at the γ-image, every operand concrete. -/
theorem ma_spill1 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSP1a) (γC ρ maCP1a) (0 :: rest)
      = .ok (γC ρ maCP1b, γS ρ σ maSP1b, rest) := by
  kernel_rfl

theorem maW1b_out : symEvalWindowTB bfTB 69 maSP1b maCP1b
    = (69, maS1, maC1) := by
  kernel_rfl

/-- **The Ready-assembly span**: HasReady, Ready, readyWithoutAccept,
the first applyUnstableEntries — 3,327 steps, one draw. -/
theorem ring_w1_span (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 3327 (γS ρ σ maS0) (γC ρ maC0) (0 :: rest)
      = .ok (γC ρ maC1, γS ρ σ maS1, rest) := by
  have h1 := symEvalWindowTB_refines maW1a_out ρ σ (0 :: rest) hag
  have hx := ma_spill1 ρ σ rest
  have h2 := symEvalWindowTB_refines maW1b_out ρ σ rest hag
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain h1 (Surface.stepFnIter_one hx)) h2

end GoLean.RaftSeam.Ring
