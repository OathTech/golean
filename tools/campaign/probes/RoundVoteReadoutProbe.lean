import GoLeanProofs.Specs.Raft.RoundVoteLit1
import GoLeanProofs.Specs.Raft.RoundVoteLit6
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Specs.Raft.HandlerEqSym

/-! A4-U23: #eval-first readout probe for the vote-round lemma module
(the rule: evaluate every Bool/value before asking the kernel). -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam
open GoLean.RaftSeam.RoundVote

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def rvρ0 : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }

def rvσT : ExecState := bfTB.toState
def canonVote : ExecState := γS rvρ0 rvσT mvSB0
def canonVote' : ExecState := γS rvρ0 rvσT mvSB26
def rvTwinLoc : Loc := .base ⟨121⟩

#eval (toString (repr (γC rvρ0 mvCB26)) == toString (repr (γC rvρ0 mvCB0)))  -- self-return?

#eval (absTwinRead canonVote rvTwinLoc).map
  (fun a => (a.violations, a.claims, a.committed,
             a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))

#eval (absTwinRead canonVote' rvTwinLoc).map
  (fun a => (a.violations, a.claims, a.committed,
             a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))

#eval (absTwinNodeRaft canonVote rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote a ⟨"raft.raft"⟩ "Term")
#eval (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "Term")
#eval (absTwinNodeRaft canonVote rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote a ⟨"raft.raft"⟩ "Vote")
#eval (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "Vote")
#eval (absTwinNodeRaft canonVote rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote a ⟨"raft.raft"⟩ "lead")
#eval (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "lead")
-- state field (becomeFollower: stays follower = 0)
#eval (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
  (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "state")
