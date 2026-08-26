import GoLeanProofs.Specs.Raft.RoundMaLit2
import GoLeanProofs.Specs.Raft.RoundMaLit3
import GoLeanProofs.Specs.Raft.RoundMaLit4
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMaEqB — the RING-HEAD segment of the MsgApp round's
canonical run (A4-U22 C2d): the harvest assembly through the storage
ents spill. All draws latitude (the C2c census's X1–X3). See
`RoundMaEqA.lean`'s split note. -/

namespace GoLean.RaftSeam.RoundMa

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

theorem maWB1_out : symEvalWindowTB bfTB 3469 maSRP3b maCRP3b
    = (3469, maSRP4a, maCRP4a) := by
  kernel_rfl

/-- Ring X1 (Ready-assembly `[]*Message` spill; latitude). -/
theorem roundMa_spill3 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP4a) (γC ρ maCRP4a) (0 :: rest)
      = .ok (γC ρ maCRP4b, γS ρ σ maSRP4b, rest) := by
  kernel_rfl

theorem maWB2_out : symEvalWindowTB bfTB 1927 maSRP4b maCRP4b
    = (1927, maSRP5a, maCRP5a) := by
  kernel_rfl

/-- Ring X2 (the storage-append-resp `Responses` build; latitude). -/
theorem roundMa_spill4 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP5a) (γC ρ maCRP5a) (0 :: rest)
      = .ok (γC ρ maCRP5b, γS ρ σ maSRP5b, rest) := by
  kernel_rfl

theorem maWB3_out : symEvalWindowTB bfTB 2772 maSRP5b maCRP5b
    = (2772, maSRP6a, maCRP6a) := by
  kernel_rfl

/-- Ring X3 (the MemoryStorage.Append ents spill; latitude). -/
theorem roundMa_spill5 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP6a) (γC ρ maCRP6a) (0 :: rest)
      = .ok (γC ρ maCRP6b, γS ρ σ maSRP6b, rest) := by
  kernel_rfl

/-- **The RING-HEAD segment span**: RP3b′ → RP6b′ (8,171 steps, 3
latitude draws). -/
theorem roundMa_ringHeadSpan (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 8171 (γS ρ σ maSRP3b) (γC ρ maCRP3b) (0 :: 0 :: 0 :: rest)
      = .ok (γC ρ maCRP6b, γS ρ σ maSRP6b, rest) := by
  have h1 := symEvalWindowTB_refines maWB1_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have hs3 := roundMa_spill3 ρ σ (0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines maWB2_out ρ σ (0 :: 0 :: rest) hag
  have hs4 := roundMa_spill4 ρ σ (0 :: rest)
  have h3 := symEvalWindowTB_refines maWB3_out ρ σ (0 :: rest) hag
  have hs5 := roundMa_spill5 ρ σ rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain
          (Surface.stepFnIter_chain h1 (Surface.stepFnIter_one hs3))
          h2)
        (Surface.stepFnIter_one hs4))
      h3)
    (Surface.stepFnIter_one hs5)

end GoLean.RaftSeam.RoundMa
