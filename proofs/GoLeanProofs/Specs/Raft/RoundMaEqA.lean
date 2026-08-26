import GoLeanProofs.Specs.Raft.RoundMaLit1
import GoLeanProofs.Specs.Raft.RoundMaLit2
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMaEqA — the ARM segment of the MsgApp round's canonical
run (A4-U22 C2d): anchor → the ring boundary. Windows + crossings in
the tree-propagation template; the round's SEMANTIC draw (the
delivery pick, round step 207) is `roundMa_pick` — the one draw whose
VALUE selects behavior (which live message is delivered); the two arm
spills are latitude (capacity only). Split across three RoundMaEq*
modules so the kernel work parallelizes (the C2c lesson). Design
record: `RoundMaLemma.lean`'s docstring. -/

namespace GoLean.RaftSeam.RoundMa

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- Window: anchor → the delivery pick (207 steps — loop-head cond,
live-map rebuild at |net| = 1, into the pick). -/
theorem maWA1_out : symEvalWindowTB bfTB 207 maSR0 maCR0
    = (207, maSRP1a, maCRP1a) := by
  kernel_rfl

/-- **THE SEMANTIC CROSSING** — the delivery pick (mapIter draw at
head 0: deliver net[0], the doctored MsgApp). The post-state is one
appended iteration cell; the choice VALUE selects which message the
round delivers — the draw the choice-invariance factoring keeps
EXPLICIT (coordinator note, campaign log 2026-08-27). -/
theorem roundMa_pick (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP1a) (γC ρ maCRP1a) (0 :: rest)
      = .ok (γC ρ maCRP1b, γS ρ σ maSRP1b, rest) := by
  kernel_rfl

theorem maWA2_out : symEvalWindowTB bfTB 2792 maSRP1b maCRP1b
    = (2792, maSR1, maCR1) := by
  kernel_rfl

theorem maWA3_out : symEvalWindowTB bfTB 2837 maSR1 maCR1
    = (2837, maSRP2a, maCRP2a) := by
  kernel_rfl

/-- Arm spill 1 (the log-append region; latitude draw at head 0). -/
theorem roundMa_spill1 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP2a) (γC ρ maCRP2a) (0 :: rest)
      = .ok (γC ρ maCRP2b, γS ρ σ maSRP2b, rest) := by
  kernel_rfl

theorem maWA4_out : symEvalWindowTB bfTB 1374 maSRP2b maCRP2b
    = (1374, maSRP3a, maCRP3a) := by
  kernel_rfl

/-- Arm spill 2 (the commitTo region; latitude). -/
theorem roundMa_spill2 (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ maSRP3a) (γC ρ maCRP3a) (0 :: rest)
      = .ok (γC ρ maCRP3b, γS ρ σ maSRP3b, rest) := by
  kernel_rfl

/-- **The ARM segment span**: anchor → ring boundary RP3b′ (7,213
steps, 3 draws: the pick + two latitude spills). -/
theorem roundMa_armSpan (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 7213 (γS ρ σ maSR0) (γC ρ maCR0) (0 :: 0 :: 0 :: rest)
      = .ok (γC ρ maCRP3b, γS ρ σ maSRP3b, rest) := by
  have h1 := symEvalWindowTB_refines maWA1_out ρ σ (0 :: 0 :: 0 :: rest) hag
  have hp := roundMa_pick ρ σ (0 :: 0 :: rest)
  have h2 := symEvalWindowTB_refines maWA2_out ρ σ (0 :: 0 :: rest) hag
  have h3 := symEvalWindowTB_refines maWA3_out ρ σ (0 :: 0 :: rest) hag
  have hs1 := roundMa_spill1 ρ σ (0 :: rest)
  have h4 := symEvalWindowTB_refines maWA4_out ρ σ (0 :: rest) hag
  have hs2 := roundMa_spill2 ρ σ rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain
          (Surface.stepFnIter_chain
            (Surface.stepFnIter_chain h1 (Surface.stepFnIter_one hp))
            h2)
          h3)
        (Surface.stepFnIter_one hs1))
      h4)
    (Surface.stepFnIter_one hs2)

end GoLean.RaftSeam.RoundMa
