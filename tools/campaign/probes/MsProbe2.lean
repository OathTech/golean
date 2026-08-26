/- A4-U4: MemoryStorage leaves via a caller-shaped Stmt.call with
var targets (fi, er) — result plumbing + counts + mirror window. -/
import GoLean.GoCore.MachineEqb
import GoLeanProofs.Specs.Raft.BcFixture
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

def msHeapExt (vote lead state ldT : Int) : GoCore.Heap :=
  uHeap vote lead state ldT ++
  [(.base ⟨21⟩, ⟨some (.int .uint64), .int 0 .uint64⟩),
   (.base ⟨22⟩, ⟨none, .nil⟩),
   (.base ⟨23⟩, ⟨none, .addr (.base ⟨6⟩)⟩)]

def msσ : ExecState :=
  { wBase with heap := msHeapExt 7 2 0 5, nextAddr := 24 }

def msEnv : LocalEnv := [[("fi", .base ⟨21⟩), ("er", .base ⟨22⟩), ("ms", .base ⟨23⟩)]]

def msCallC (fid : String) (extra : List Expr) : Machine.Config :=
  .exec (.call #[.var "fi", .var "er"] ⟨fid⟩
    (#[Expr.var "ms"] ++ extra.toArray)) msEnv .stop

def runMs (tag fid : String) (extra : List Expr) : IO Unit := do
  let mut s := msσ
  let mut c := msCallC fid extra
  let mut ch : Choices := []
  let mut i : Nat := 0
  let mut done := false
  while i < 5000 && !done do
    match c with
    | .next .stop => done := true
    | _ =>
      match stepFn s c ch with
      | .ok (c', s', ch') => c := c'; s := s'; ch := ch'; i := i + 1
      | .error e =>
          IO.println s!"{tag}: ERROR at step {i}: {(repr e).pretty 100}"
          return
  IO.println s!"{tag}: DONE at step {i}; nextAddr -> {s.nextAddr}"
  IO.println s!"  fi = {((repr (Heap.lookup s.heap (.base ⟨21⟩))).pretty 100).replace "\n" " "}"
  IO.println s!"  er = {((repr (Heap.lookup s.heap (.base ⟨22⟩))).pretty 100).replace "\n" " "}"

#eval runMs "FirstIndex" "raft.MemoryStorage.FirstIndex" []
#eval runMs "Term@1" "raft.MemoryStorage.Term" [.intLit 1 .uint64]
#eval runMs "Term@0" "raft.MemoryStorage.Term" [.intLit 0 .uint64]
#eval runMs "LastIndex" "raft.MemoryStorage.LastIndex" []

-- mirror
def msSymHeapExt : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (msHeapExt 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy (setSymField (setSymField (setSymField
      (embedGo (uRaftVal 0 0 0 0))
      "Vote" (.int (.var 1) .uint64))
      "lead" (.int (.var 2) .uint64))
      "leadTransferee" (.int (.var 4) .uint64)))
    else (l, .mk c.declaredTy (embedGo c.value)))

def msS0 : SymState := { heap := msSymHeapExt, nextAddr := 24 }

def msSymC (fid : String) (extra : List Expr) : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨fid⟩
    (#[Expr.var "ms"] ++ extra.toArray)) msEnv .stop

def runSym (tag fid : String) (extra : List Expr) : IO Unit := do
  let (n, S1, C1) := symEvalWindowTB bfTB 5000 msS0 (msSymC fid extra)
  let desc := match C1 with
    | .next .stop => "next stop"
    | _ => "other"
  IO.println s!"{tag} mirror: {n} steps, ends {desc}"
  if let .next .stop := C1 then
    -- γ-check vs machine
    let ρc : Valuation :=
      { ints := fun i => [0, 7, 2, 0, 5].getD i 0
        bools := fun _ => false, vals := fun _ => .nil
        cells := fun _ => ⟨none, .nil⟩ }
    let mut s := { wBase with heap := msHeapExt 7 2 0 5, nextAddr := 24 }
    let mut c := msCallC fid extra
    let mut ch : Choices := []
    for _ in [0:n] do
      match stepFn s c ch with
      | .ok (c', s', ch') => c := c'; s := s'; ch := ch'
      | .error _ => pure ()
    let img := γS ρc { wBase with heap := msHeapExt 7 2 0 5, nextAddr := 24 } S1
    IO.println s!"  γ == machine heap: {img.heap == s.heap} (nextAddr {img.nextAddr}/{s.nextAddr})"
  else
    match stepFnSTB bfTB S1 C1 with
    | .error q => IO.println s!"  quit: {repr q}"
    | .ok _ => pure ()

#eval runSym "FirstIndex" "raft.MemoryStorage.FirstIndex" []
#eval runSym "Term@1" "raft.MemoryStorage.Term" [.intLit 1 .uint64]
