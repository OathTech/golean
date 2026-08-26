import GoLeanProofs.Specs.Raft.RoundVrLit1
import GoLeanProofs.Specs.Raft.RoundVrLit14
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Specs.Raft.HandlerEqSym

/-! A4-U25: #eval-first readouts for the Vr (election-completion)
lemma module. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam
open GoLean.RaftSeam.RoundVr

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def vrρ : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }
def vrσ : ExecState := bfTB.toState
def cV : ExecState := γS vrρ vrσ vrSB0
def cV' : ExecState := γS vrρ vrσ vrSB69
def tl : Loc := .base ⟨121⟩

-- self-return at the γ level
#eval (toString (repr (γC vrρ vrCB69)) == toString (repr (γC vrρ vrCB0)))

-- (violations, claims, committed, net view) pre/post
#eval (absTwinRead cV tl).map
  (fun a => (a.violations, a.claims, a.committed,
             a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
#eval (absTwinRead cV' tl).map
  (fun a => (a.violations, a.claims, a.committed,
             a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))

-- node 1 raft shell: state / lead / Term / Vote, pre and post
def shellRead (σx : ExecState) (f : String) : Option Int :=
  (absTwinNodeRaft σx tl 0).bind
    (fun a => GoLean.Lens.fieldReadU64 σx a ⟨"raft.raft"⟩ f)
#eval (shellRead cV "state", shellRead cV' "state")
#eval (shellRead cV "lead", shellRead cV' "lead")
#eval (shellRead cV "Term", shellRead cV' "Term")

-- raftLog committed/applied (expect unchanged 1→1: the noop is
-- appended but its quorum-commit is the Mar family's round)
def logRead (σx : ExecState) (f : String) : Option Int :=
  (absTwinNodeRaft σx tl 0).bind
    (fun a => (GoLean.Lens.fieldRead σx a ⟨"raft.raft"⟩ "raftLog").bind
      (fun v => match v with
        | .addr (.base la) =>
            GoLean.Lens.fieldReadU64 σx la ⟨"raft.raftLog"⟩ f
        | _ => none))
#eval (logRead cV "committed", logRead cV' "committed")
#eval (logRead cV "applied", logRead cV' "applied")
