import GoLeanProofs.Specs.Raft.BfSortStep
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

partial def ppI : SymInt → String
  | .lit v => s!"lit {v}"
  | .var i => s!"var {i}"
  | .norm k t => s!"norm {repr k} ({ppI t})"
  | _ => "other"

partial def ppV : SymValue → String
  | .int t k => s!".int ({ppI t}) {repr k}"
  | .addr l => s!".addr {repr l}"
  | v => "…"

def main : IO Unit := do
  match GoLean.Sym.Heap.lookup uS13.heap (.base ⟨0⟩) with
  | some (.mk _ (.struct _ fs)) =>
      for (n, v) in fs do
        if n == "Term" || n == "Vote" || n == "lead" || n == "state" then
          IO.println s!"{n} = {ppV v}"
  | _ => IO.println "no raft cell"
  match GoLean.Sym.Heap.lookup uS13.heap (.base ⟨1⟩) with
  | some (.mk _ (.struct _ fs)) =>
      for (n, v) in fs do
        if n == "committed" || n == "applied" then
          IO.println s!"raftLog.{n} = {ppV v}"
  | _ => IO.println "no raftLog cell"
