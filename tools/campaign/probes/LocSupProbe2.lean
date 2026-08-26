import GoLeanProofs
open GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame GoLean.RaftSeam
-- which low addresses appear as locLits in ANY body: address a is referenced
-- iff bumping only a changes some body
def bump (a : Nat) : Nat → Nat := fun x => if x = a then 1000000 + a else x
#eval (List.range 32).filter (fun a =>
  wBase.functions.toList.any (fun f => !(renameStmt (bump a) f.body == f.body)))
