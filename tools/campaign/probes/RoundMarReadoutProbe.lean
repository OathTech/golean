import GoLeanProofs.Specs.Raft.RoundMarLit1
import GoLeanProofs.Specs.Raft.RoundMarLit7
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Specs.Raft.HandlerEqSym

/-! A4-U24: #eval-first readouts for the Mar lemma module. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam
open GoLean.RaftSeam.RoundMar

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def rmρ : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }
def rmσ : ExecState := bfTB.toState
def cM : ExecState := γS rmρ rmσ mrSB0
def cM' : ExecState := γS rmρ rmσ mrSB33
def tl : Loc := .base ⟨121⟩

#eval (toString (repr (γC rmρ mrCB33)) == toString (repr (γC rmρ mrCB0)))

#eval (absTwinRead cM tl).map
  (fun a => (a.violations, a.claims, a.committed,
             a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
#eval (absTwinRead cM' tl).map
  (fun a => (a.violations, a.claims, a.committed,
             a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))

def logRead (σx : ExecState) (f : String) : Option Int :=
  (absTwinNodeRaft σx tl 0).bind
    (fun a => (GoLean.Lens.fieldRead σx a ⟨"raft.raft"⟩ "raftLog").bind
      (fun v => match v with
        | .addr (.base la) =>
            GoLean.Lens.fieldReadU64 σx la ⟨"raft.raftLog"⟩ f
        | _ => none))
#eval (logRead cM "committed", logRead cM' "committed")
#eval (logRead cM "applied", logRead cM' "applied")
#eval (absTwinNodeRaft cM' tl 0).bind
  (fun a => GoLean.Lens.fieldReadU64 cM' a ⟨"raft.raft"⟩ "state")
