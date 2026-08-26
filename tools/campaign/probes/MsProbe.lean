/- A4-U4 wave-1 probe: MemoryStorage.{FirstIndex,Term} — the drained
call shape, result plumbing, step counts, and the mirror window. -/
import GoLean.GoCore.MachineEqb
import GoLeanProofs.Specs.Raft.BcFixture
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

def msC (fid : String) (args : List GoValue) : Machine.Config :=
  match args with
  | [] => .retV (.addr (.base ⟨6⟩)) (.callArgsK ⟨fid⟩ [] [] [] [] .stop)
  | [a] => .retV a (.callArgsK ⟨fid⟩ [] [.addr (.base ⟨6⟩)] [] [] .stop)
  | _ => .panicked "?"

def runMs (tag fid : String) (args : List GoValue) : IO Unit := do
  let σ0 := uσ 7 2 1 5
  let mut s := σ0
  let mut c := msC fid args
  let mut ch : Choices := []
  let mut i : Nat := 0
  let mut done := false
  while i < 5000 && !done do
    match c with
    | .next .stop => done := true
    | .retV v .stop =>
        IO.println s!"{tag}: ended retV {(repr v).pretty 200} at step {i}"
        done := true
    | _ =>
      match stepFn s c ch with
      | .ok (c', s', ch') => c := c'; s := s'; ch := ch'; i := i + 1
      | .error e =>
          IO.println s!"{tag}: ERROR at step {i}: {(repr e).pretty 100}"
          return
  IO.println s!"{tag}: done at step {i}; nextAddr {σ0.nextAddr} -> {s.nextAddr}"
  -- dump the fresh cells (result cells among them)
  for (l, cell) in s.heap do
    match l with
    | .base a =>
        if a.id >= 21 then
          IO.println s!"  cell {a.id}: {((repr cell.value).pretty 120).replace "\n" " "}"
    | _ => pure ()

#eval runMs "FirstIndex" "raft.MemoryStorage.FirstIndex" []
#eval runMs "Term1" "raft.MemoryStorage.Term" [.int 1 .uint64]

-- mirror windows at the symbolic fixture (uS0 — Vote etc. symbolic ride)
def msSymC (fid : String) (args : List SymValue) : SymConfig :=
  match args with
  | [] => .retV (.addr (.base ⟨6⟩)) (.callArgsK ⟨fid⟩ [] [] [] [] .stop)
  | [a] => .retV a (.callArgsK ⟨fid⟩ [] [.addr (.base ⟨6⟩)] [] [] .stop)
  | _ => .panicked "?"

def runSym (tag fid : String) (args : List SymValue) : IO Unit := do
  let (n, S1, C1) := symEvalWindowTB bfTB 5000 uS0 (msSymC fid args)
  let desc := match C1 with
    | .next .stop => "next stop"
    | .retV _ .stop => "retV stop"
    | _ => "other"
  IO.println s!"{tag} mirror: {n} steps, ends {desc}"
  match stepFnSTB bfTB S1 C1 with
  | .error q => IO.println s!"  next would quit: {repr q}"
  | .ok _ => IO.println "  next steps fine"

#eval runSym "FirstIndex" "raft.MemoryStorage.FirstIndex" []
#eval runSym "Term1" "raft.MemoryStorage.Term" [.int (.lit 1) .uint64]
