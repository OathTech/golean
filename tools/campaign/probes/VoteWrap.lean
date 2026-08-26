import GoLeanProofs.Specs.Raft.SfHbLit
open GoLean GoLean.GoCore GoLean.Sym GoLean.RaftSeam
def showV : GoLean.Sym.Value symDom → String
  | .int si k => s!"int {(repr si).pretty 10000} {(repr k).pretty 100}"
  | _ => "other"
#eval match GoLean.Sym.Heap.lookup sfhbS3.heap (.base ⟨31⟩) with
  | some (.mk _ (GoLean.Sym.Value.struct _ fs)) =>
      (fs.toList.filterMap (fun (p : String × GoLean.Sym.Value symDom) =>
        if p.1 == "Vote" || p.1 == "lead" || p.1 == "state" || p.1 == "leadTransferee"
        then some s!"{p.1} = {showV p.2}" else none))
  | _ => ["no raft cell"]
