import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.MsResite
import GoLeanProofs.Specs.Raft.StaticCells

/-! # A4-U13 slot 3 census: the MemoryStorage.Term ERROR branches on
THE STATIC-CELL COMPLEMENT (its second consumer — the U4 residual:
"the lowered error path loads package-level error vars at static twin
addresses the leaf fixture does not carry"). Term(0) → ErrCompacted
(cell 23); Term(5) → ErrUnavailable (cell 25). -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def mseHeap : GoCore.Heap :=
  ((msHeapExt 7 0 0 0).map (fun (l, c) =>
    (renameLoc sh31 l, ⟨c.declaredTy, renameValue sh31 c.value⟩))) ++
  staticComplement

def mseσ0 : ExecState := { wBase with heap := mseHeap, nextAddr := staticComplementNa }

def mseEnv : LocalEnv :=
  [[("fi", .base ⟨52⟩), ("er", .base ⟨53⟩), ("ms", .base ⟨54⟩)]]

def mseC0 (i : Int) : Machine.Config :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩
    #[Expr.var "ms", Expr.intLit i .uint64]) mseEnv .stop

def bigStream : Choices := List.replicate 20 0

partial def walk (n : Nat) (σ : ExecState) (c : Machine.Config) (ch : Choices)
    (fuel : Nat) : String :=
  if fuel = 0 then s!"NO TERMINATION by {n}"
  else match stepFn σ c ch with
    | .ok (Machine.Config.next .stop, σ2, ch2) =>
        s!"STOP at step {n+1}; na={σ2.nextAddr} choices={20 - ch2.length}"
    | .ok (c2, σ2, ch2) => walk (n+1) σ2 c2 ch2 (fuel - 1)
    | .error e => s!"ERROR at {n+1}: {e.status} : {e.message.take 200}"
#eval s!"Term(0): {walk 0 mseσ0 (mseC0 0) bigStream 3000}"
#eval s!"Term(5): {walk 0 mseσ0 (mseC0 5) bigStream 3000}"

partial def findStop (c0 : Machine.Config) (n : Nat) : Nat :=
  if n > 3000 then 0
  else match stepFnIter n mseσ0 c0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | .error _ => n + 1000000
    | _ => findStop c0 (n + 1)

#eval show IO Unit from do
  for i in [(0 : Int), 5] do
    let n := findStop (mseC0 i) 100
    match stepFnIter n mseσ0 (mseC0 i) bigStream with
    | .ok (_, σ', _) =>
        let fi := (Heap.lookup σ'.heap (.base ⟨52⟩)).map (·.value)
        let er := (Heap.lookup σ'.heap (.base ⟨53⟩)).map (·.value)
        IO.println s!"Term({i}): {n} steps; fi={toString (repr fi)} er={(toString (repr er)).take 200}"
    | .error e => IO.println s!"Term({i}) ERR {e.message.take 80}"

-- mirror windows
def mseSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  mseHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value)))
def mseS0 : SymState := { heap := mseSymHeap, nextAddr := staticComplementNa }
def mseC0sym (i : Int) : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩
    #[Expr.var "ms", Expr.intLit i .uint64]) mseEnv .stop
#eval show IO Unit from do
  for i in [(0 : Int), 5] do
    let (n, S', C') := symEvalWindowTB bfTB 3000 mseS0 (mseC0sym i)
    let stop := match C' with | GoLean.Sym.Config.next .stop => true | _ => false
    IO.println s!"mirror Term({i}): {n} steps; stop={stop}; na={S'.nextAddr}"
