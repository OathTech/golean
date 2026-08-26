import GoLeanProofs.Specs.Raft.RingLit4
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RingEqW345 — the choice-free window links and spans: the
checker apply (W3), THE STORAGE-RESP ARMS (W4), the second Ready
(W5) (C2c; see `RingEqW1.lean`'s split note and `RingEquation.lean`'s
design docstring). -/

namespace GoLean.RaftSeam.Ring

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-! ## W3–W5 — the choice-free spans -/

theorem maW3_out : symEvalWindowTB bfTB 324 maS2 maC2
    = (324, maS3, maC3) := by
  kernel_rfl

/-- **The checker-apply span** (`main.twin.apply`): 324 steps,
choice-free — the U18 "checker is not the balloon" measure, now a
statement. -/
theorem ring_w3_span (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    stepFnIter 324 (γS ρ σ maS2) (γC ρ maC2) ch
      = .ok (γC ρ maC3, γS ρ σ maS3, ch) :=
  symEvalWindowTB_refines maW3_out ρ σ ch hag

theorem maW4_out : symEvalWindowTB bfTB 3202 maS3 maC3
    = (3202, maS4, maC4) := by
  kernel_rfl

/-- **THE STORAGE-RESP SPAN** — `Advance` with BOTH nested
`raft.raft.Step` local arms (MsgStorageAppendResp →
`unstable.stableTo`; MsgStorageApplyResp → `raftLog.appliedTo`):
3,202 steps, CHOICE-FREE (SC1's determinism verdict, now a theorem
shape: the stream passes through untouched). The heartbeat fixture's
142-step no-op Advance could not reach these arms (U20's finding);
this fixture does. -/
theorem ring_w4_span (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    stepFnIter 3202 (γS ρ σ maS3) (γC ρ maC3) ch
      = .ok (γC ρ maC4, γS ρ σ maS4, ch) :=
  symEvalWindowTB_refines maW4_out ρ σ ch hag

theorem maW5_out : symEvalWindowTB bfTB 1832 maS4 maC4
    = (1832, maS5, maC5) := by
  kernel_rfl

/-- **The second-Ready span** (HasReady false exit, incl. the second
applyUnstableEntries): 1,832 steps, choice-free. -/
theorem ring_w5_span (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    stepFnIter 1832 (γS ρ σ maS4) (γC ρ maC4) ch
      = .ok (γC ρ maC5, γS ρ σ maS5, ch) :=
  symEvalWindowTB_refines maW5_out ρ σ ch hag

end GoLean.RaftSeam.Ring
