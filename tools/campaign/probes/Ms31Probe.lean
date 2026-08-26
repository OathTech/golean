import GoLeanProofs
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.Frame GoLean.RaftSeam

def ms31SymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (msHeapExt 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (renameLoc sh31 l, .mk c.declaredTy bpc31SymRaft)
    else (renameLoc sh31 l, .mk c.declaredTy (embedGo (renameValue sh31 c.value))))
def ms31S0 : SymState := { heap := ms31SymHeap, nextAddr := 55 }
def ms31Env : LocalEnv := [[("fi", .base ⟨52⟩), ("er", .base ⟨53⟩), ("ms", .base ⟨54⟩)]]
def ms31FiC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.FirstIndex"⟩ #[Expr.var "ms"]) ms31Env .stop
def ms31TmC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩ #[Expr.var "ms", Expr.intLit 1 .uint64]) ms31Env .stop

-- windows
#eval (symEvalWindowTB bfTB 178 ms31S0 ms31FiC0).1
#eval (symEvalWindowTB bfTB 246 ms31S0 ms31TmC0).1
-- machine runs vs γ-images
#eval match stepFnIter 178 (γS bcρw wBase ms31S0) (γC bcρw ms31FiC0) [] with
  | .ok (c, σ', ch) => s!"Fi machine: cfg-stop={match c with | Machine.Config.next .stop => true | _ => false} ch={ch.length} heapEq={σ'.heap == (γS bcρw wBase (symEvalWindowTB bfTB 178 ms31S0 ms31FiC0).2.1).heap} na={σ'.nextAddr}"
  | .error e => s!"Fi ERROR {e.status}: {e.message}"
#eval match stepFnIter 246 (γS bcρw wBase ms31S0) (γC bcρw ms31TmC0) [] with
  | .ok (c, σ', ch) => s!"Tm machine: cfg-stop={match c with | Machine.Config.next .stop => true | _ => false} ch={ch.length} heapEq={σ'.heap == (γS bcρw wBase (symEvalWindowTB bfTB 246 ms31S0 ms31TmC0).2.1).heap} na={σ'.nextAddr}"
  | .error e => s!"Tm ERROR {e.status}: {e.message}"
-- projections/results at the re-sited addresses
def ms31FiS1 : SymState := (symEvalWindowTB bfTB 178 ms31S0 ms31FiC0).2.1
def ms31TmS1 : SymState := (symEvalWindowTB bfTB 246 ms31S0 ms31TmC0).2.1
#eval toString (repr (absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩))
#eval toString (repr ((Heap.lookup (γS bcρw wBase ms31FiS1).heap (.base ⟨52⟩)).map (fun c => c.value)))
#eval toString (repr ((Heap.lookup (γS bcρw wBase ms31FiS1).heap (.base ⟨53⟩)).map (fun c => c.value)))
#eval toString (repr (absStorageEnts (γS bcρw wBase ms31FiS1) ⟨37⟩))
#eval toString (repr ((Heap.lookup (γS bcρw wBase ms31TmS1).heap (.base ⟨52⟩)).map (fun c => c.value)))
#eval toString (repr ((Heap.lookup (γS bcρw wBase ms31TmS1).heap (.base ⟨53⟩)).map (fun c => c.value)))
#eval toString (repr (absStorageEnts (γS bcρw wBase ms31TmS1) ⟨37⟩))
