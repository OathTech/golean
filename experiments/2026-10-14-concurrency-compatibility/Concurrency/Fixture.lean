import Concurrency.Constraints

namespace Concurrency
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

def x : Loc := .base ⟨0⟩
def y : Loc := .base ⟨1⟩
def env : LocalEnv := [[(0, x)]]
def initialStore (b : Bool := false) : Store :=
  ⟨#[.value .bool (.bool b), .value .bool (.bool false)]⟩
def worker : Func :=
  { id := ⟨"worker"⟩, args := #[], results := #[],
    body := .assign (.addr (.global 1)) (.boolLit true) }
def ctx : ProgramCtx := .ofTables (functions := #[worker])
def program : Stmt := .seqn #[
  .goStmt (.funcVal ⟨"worker"⟩ #[]) #[],
  .print false #[.var 0], .print false #[.var 0]]
def initial : MultiConfig := ⟨#[.running (.exec program env .stop) none], initialStore, 0⟩
def tape : Choices := [0, 1]

end Concurrency
