import GoLeanProofs.Specs.Raft.HhEquation
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

-- recompute the walk quickly and measure wrap depths exactly
def scRaftHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨31⟩ then
      (p.1, match p.2 with
        | .mk dty (.struct tid fs) =>
            .mk dty (.struct tid (fs.map (fun (q : String × SymValue) =>
              if q.1 == "state" then (q.1, .int (.lit 1) .uint64) else q)))
        | c => c)
    else p)

partial def depthOf : SymInt → (Nat × String)
  | .norm _ a => let (d, s) := depthOf a; (d + 1, s)
  | .var i => (0, s!"var {i}")
  | .lit n => (0, s!"lit {n}")
  | _ => (0, "OTHER")

def scMsg : SymValue := .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def scS0d : SymState :=
  { heap := scRaftHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) scMsg),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 8) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def scC0d : SymConfig := .exec (.call #[.var "er"] ⟨"raft.stepCandidate"⟩
    #[Expr.var "r", Expr.var "m"])
    [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]] .stop

#eval show IO Unit from do
  let mut S := scS0d
  let mut C := scC0d
  let mut si := 0
  for stage in ["P5","P6","P7","P8","STOP","SORT","SPILL"] do
    let (_, S', C') := symEvalWindowTB bfTB 6000 S C
    match stage with
    | "P5" => let r := uCrossPick 5 .int S' C'; S := r.1; C := r.2
    | "P6" => let r := uCrossPick 6 .uint64 S' C'; S := r.1; C := r.2
    | "P7" => let r := uCrossPick 7 .uint64 S' C'; S := r.1; C := r.2
    | "P8" => let r := uCrossPick 8 .uint64 S' C'; S := r.1; C := r.2
    | "STOP" => let r := uCrossStop S' C'; S := r.1; C := r.2
    | "SORT" => let r := uCrossSort S' C'; S := r.1; C := r.2
    | _ =>
      match C' with
      | .retV (GoLean.Sym.Value.slice _) (.stmtOpK _ _ done _ _ k') =>
          let tgt := (match done with
            | [_, GoLean.Sym.Value.addr (.base t)] => t.id | _ => 0)
          let backing := S'.nextAddr
          S := { heap := (GoLean.Sym.Heap.set S'.heap (.base ⟨tgt⟩)
              (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩)))) (.atom 0)))
              ++ [(.base ⟨backing⟩, .atom 0)], nextAddr := backing + 1 }
          C := .next k'
      | _ => IO.println "spill shape"; si := 1
  if si == 1 then IO.println "aborted" else do
  let (_, S8, _) := symEvalWindowTB bfTB 6000 S C
  match GoLean.Sym.Heap.lookup S8.heap (.base ⟨31⟩) with
  | some (.mk _ (GoLean.Sym.Value.struct _ fs)) =>
      for p in fs.toList do
        match p.2 with
        | .int sterm _ =>
            let (d, core) := depthOf sterm
            IO.println s!"{p.1}: depth {d} core {core}"
        | _ => pure ()
  | _ => IO.println "no cell"
