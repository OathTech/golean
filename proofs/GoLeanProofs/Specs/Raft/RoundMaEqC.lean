import GoLeanProofs.Specs.Raft.RoundMaLit4
import GoLeanProofs.Specs.Raft.RoundMaLit5
import GoLeanProofs.Specs.Raft.RoundMaLit6
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMaEqC — the SEND + SUFFIX segment of the MsgApp round's
canonical run (A4-U22 C2d): the harness net/live sends (X4/X5), the
apply + Advance + storage-resp arms + second Ready, the projection /
liveCount / trace suffix, back to the loop-head anchor. See
`RoundMaEqA.lean`'s split note. -/

namespace GoLean.RaftSeam.RoundMa

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem maWC1_out : symEvalWindowTB bfTB 362 maSRP6b maCRP6b
    = (362, maSRP7a, maCRP7a) := by
  kernel_rfl

/-- Ring X4 (the harness net append — the MsgAppResp; latitude). -/
theorem roundMa_spill6 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP7a) (γC ρ maCRP7a) (0 :: rest)
      = .ok (γC ρ maCRP7b, γS ρ σ maSRP7b, rest) := by
  kernel_rfl

theorem maWC2_out : symEvalWindowTB bfTB 49 maSRP7b maCRP7b
    = (49, maSRP8a, maCRP8a) := by
  kernel_rfl

/-- Ring X5 (the harness live-flag append; latitude). -/
theorem roundMa_spill7 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP8a) (γC ρ maCRP8a) (0 :: rest)
      = .ok (γC ρ maCRP8b, γS ρ σ maSRP8b, rest) := by
  kernel_rfl

theorem maWC3_out : symEvalWindowTB bfTB 2703 maSRP8b maCRP8b
    = (2703, maSR2, maCR2) := by
  kernel_rfl

theorem maWC4_out : symEvalWindowTB bfTB 2795 maSR2 maCR2
    = (2795, maSR3, maCR3) := by
  kernel_rfl

/-- The closing window: projection tail, liveCount, the trace glue,
back to the (self-returning) loop-head anchor. -/
theorem maWC5_out : symEvalWindowTB bfTB 2193 maSR3 maCR3
    = (2193, maSR4, maCR4) := by
  kernel_rfl

/-- **The SEND + SUFFIX segment span**: RP6b′ → the end anchor
(8,104 steps, 2 latitude draws). -/
theorem roundMa_suffixSpan (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 8104 (γS ρ σ maSRP6b) (γC ρ maCRP6b) (0 :: 0 :: rest)
      = .ok (γC ρ maCR4, γS ρ σ maSR4, rest) := by
  have h1 := symEvalWindowTB_refines maWC1_out ρ σ (0 :: 0 :: rest) hag
  have hs6 := roundMa_spill6 ρ σ (0 :: rest)
  have h2 := symEvalWindowTB_refines maWC2_out ρ σ (0 :: rest) hag
  have hs7 := roundMa_spill7 ρ σ rest
  have h3 := symEvalWindowTB_refines maWC3_out ρ σ rest hag
  have h4 := symEvalWindowTB_refines maWC4_out ρ σ rest hag
  have h5 := symEvalWindowTB_refines maWC5_out ρ σ rest hag
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain
          (Surface.stepFnIter_chain
            (Surface.stepFnIter_chain h1 (Surface.stepFnIter_one hs6))
            h2)
          (Surface.stepFnIter_one hs7))
        h3)
      h4)
    h5

end GoLean.RaftSeam.RoundMa
