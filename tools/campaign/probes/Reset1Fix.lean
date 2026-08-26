import GoLeanProofs.Specs.Raft.RoundVoteLit1
import GoLeanProofs.Specs.Raft.RoundVoteLit2
import GoLeanProofs.Specs.Raft.RoundVoteLit3
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.KernelRfl

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam
open GoLean.RaftSeam.RoundVote

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- Table pin: under `Agrees`, the γ-image over ANY carrier equals the
γ-image over the pack's own heapless state. -/
theorem γS_pin {σ : ExecState} (hag : bfTB.Agrees σ)
    (ρ : Valuation) (S : SymState) :
    γS ρ σ S = γS ρ bfTB.toState S := by
  obtain ⟨h1, h2, h3, h4⟩ := hag
  cases σ
  simp only [γS, concS, SymTables.toState] at *
  subst h1 h2 h3 h4
  rfl

theorem reset1_fix (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFn (γS ρ σ mvSB4) (γC ρ mvCB4) (0 :: rest)
      = .ok (γC ρ mvCB5, γS ρ σ mvSB5, rest) := by
  simp only [γS_pin hag]
  kernel_rfl

-- does the choice-free exit need the pin? (free σ, no premise)
theorem visitExit_try (ρ : Valuation) (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ σ mvSB12) (γC ρ mvCB12) rest
      = .ok (γC ρ mvCB13, γS ρ σ mvSB13, rest) := by
  kernel_rfl
