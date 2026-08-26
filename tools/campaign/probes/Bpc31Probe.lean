import GoLeanProofs
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.Frame GoLean.RaftSeam

-- the re-sited BPC fixture: every cell shifted +31, off the static locLit range [0,31)
def sh31 : Nat → Nat := (· + 31)

def bpc31SymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (renameValue sh31 (uRaftVal 0 0 0 0)))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def bpc31SymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (renameLoc sh31 l, .mk c.declaredTy bpc31SymRaft)
    else (renameLoc sh31 l, .mk c.declaredTy (embedGo (renameValue sh31 c.value))))

def bpc31S0 : SymState := { heap := bpc31SymHeap, nextAddr := 52 }

def bpc31C0 : SymConfig :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)

-- phase 2 (mirror): window count + terminal + projections
#eval (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).1
#eval toString (repr (γC bpcρw (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).2.2))
#eval toString (repr (absRaftNode (γS bpcρw wBase bpc31S0) ⟨31⟩))
#eval toString (repr (absRaftNode (γS bpcρw wBase (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).2.1) ⟨31⟩))
#eval toString (repr (specBecomePreCandidate ⟨0, 7, 2, 0, 1, 1⟩))
-- phase 1 (machine): the concrete run at the shifted γ-image
#eval match stepFnIter 152 (γS bpcρw wBase bpc31S0) (γC bpcρw bpc31C0) [] with
  | .ok (c, σf, ch) => toString (repr c) ++ " / ch=" ++ toString ch.length ++ " / proj=" ++ toString (repr (absRaftNode σf ⟨31⟩)) ++ " / na=" ++ toString σf.nextAddr
  | .error e => "ERR " ++ toString (repr e)
-- γ-image == machine final heap check
#eval (γS bpcρw wBase (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).2.1).heap
  == (match stepFnIter 152 (γS bpcρw wBase bpc31S0) (γC bpcρw bpc31C0) [] with
      | .ok (_, σf, _) => σf.heap
      | .error _ => [])
-- the wrap depth of Vote at the shifted fixture (for the hvote side condition shape)
-- swap31_32 sanity: the relocated placement still projects
def swap31_32 : Nat → Nat := fun x => if x = 31 then 32 else if x = 32 then 31 else x
#eval toString (repr (absRaftNode (renameState swap31_32 (γS bpcρw wBase bpc31S0)) ⟨32⟩))
