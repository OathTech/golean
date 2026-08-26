import GoLeanProofs.Specs.Raft.RoundVoteLit1
import GoLeanProofs.Specs.Raft.RoundVoteLit2
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.KernelRfl

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam
open GoLean.RaftSeam.RoundVote

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

def ρ0 : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }
def σT : ExecState := bfTB.toState

-- fully concrete
theorem r1_conc (rest : Choices) :
    stepFn (γS ρ0 σT mvSB4) (γC ρ0 mvCB4) (0 :: rest)
      = .ok (γC ρ0 mvCB5, γS ρ0 σT mvSB5, rest) := by
  kernel_rfl

-- free σ only
theorem r1_freeσ (σ : ExecState) (rest : Choices) :
    stepFn (γS ρ0 σ mvSB4) (γC ρ0 mvCB4) (0 :: rest)
      = .ok (γC ρ0 mvCB5, γS ρ0 σ mvSB5, rest) := by
  kernel_rfl

-- free ρ only
theorem r1_freeρ (ρ : Valuation) (rest : Choices) :
    stepFn (γS ρ σT mvSB4) (γC ρ mvCB4) (0 :: rest)
      = .ok (γC ρ mvCB5, γS ρ σT mvSB5, rest) := by
  kernel_rfl
