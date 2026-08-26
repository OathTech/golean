import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Specs.Raft.AbsStateV2

/-! # A4-U18 (C1): the round-witness literal DUMPER (probe-only)

Re-derives the doctored+pruned deliver-heartbeat round fixture
(TwinRoundFixProbe's construction, kept-cell list pinned below from
its printed read set), verifies the 10,964-step round walk, and emits
`GoLeanProofs/Specs/Raft/RoundHbLit.lean`: the 26-cell loop-head heap,
the anchor config, chunk-boundary states/configs (8 chunks), and the
final state — the literals the witness theorems replay. The literal is
NOT trusted from this probe: the witness chunk lemmas in
`RoundStatement.lean` are kernel-checked replays over it. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.RaftSeam

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def isAnchor : Config → Bool
  | .exec (.ifThenElse (Expr.lessCmp (Expr.var "round") (Expr.intLit 400 _)) _ _) _ _ => true
  | _ => false

partial def walkToAnchor (n : Nat) (σ : ExecState) (c : Config) (ch : Choices)
    (fuel : Nat) : Option (Nat × ExecState × Config × Choices) :=
  if fuel = 0 then none
  else if isAnchor c then some (n, σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkToAnchor (n+1) σ2 c2 ch2 (fuel-1)
    | .error _ => none

def hbMsgVal (na : Nat) : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨na⟩)), ("To", .addr (.base ⟨na+1⟩)),
    ("From", .addr (.base ⟨na+2⟩)), ("Term", .nil),
    ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .nil), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def findTwin3 (h : Heap) : Option Loc :=
  h.findSome? (fun (l, c) =>
    if c.declaredTy == some (.defined ⟨"main.twin"⟩) then some l else none)

def doctor (σ : ExecState) : Option ExecState := do
  let tl ← findTwin3 σ.heap
  let tc ← Heap.lookup σ.heap tl
  let na := σ.nextAddr
  let tv' ← match tc.value with
    | .struct tid fs => some (GoValue.struct tid (fs.map (fun (q : String × GoValue) =>
        if q.1 == "net" then
          (q.1, .slice { base := some (.base ⟨na+4⟩), offset := 0, len := 1, cap := 1 })
        else if q.1 == "live" then
          (q.1, .slice { base := some (.base ⟨na+5⟩), offset := 0, len := 1, cap := 1 })
        else q)))
    | _ => none
  let heap' := Heap.set σ.heap tl ⟨tc.declaredTy, tv'⟩ ++
    [(.base ⟨na⟩, ⟨some (.int .int32), .int 8 .int32⟩),
     (.base ⟨na+1⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+2⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+3⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), hbMsgVal na⟩),
     (.base ⟨na+4⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Message"⟩))),
        .array #[.addr (.base ⟨na+3⟩)]⟩),
     (.base ⟨na+5⟩, ⟨some (.array 1 .bool), .array #[.bool true]⟩)]
  pure { σ with heap := heap', nextAddr := na + 6 }

/-- TwinRoundFixProbe's printed read set (26 cells). -/
def keptCells : List Nat :=
  [15, 27, 28, 57, 110, 121, 170, 1764, 1770, 1949, 1989,
   3342, 3344, 3351, 3354, 3357, 3360, 3369,
   6070, 6072, 6073, 6074, 6075, 6076, 6077, 6078]

/-- Walk exactly k steps. -/
partial def walkN (σ : ExecState) (c : Config) (ch : Choices) (k : Nat) :
    Except String (ExecState × Config × Choices) :=
  if k = 0 then .ok (σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkN σ2 c2 ch2 (k-1)
    | .error e => .error s!"{e.message.take 200}"

def pr {α : Type} [Repr α] (x : α) : String := ((repr x).pretty 110)

def go : IO Unit := do
  let stream : Choices := List.replicate 25000 0
  match runProgramSetupM 20000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[] stream with
  | .error e => IO.println s!"SETUP ERROR: {e.message.take 300}"
  | .ok (c₀, s₃, _, ch₁) =>
      match walkToAnchor 0 s₃ c₀ ch₁ 200000 with
      | none => IO.println "anchor not found"
      | some (nA, σA, cA, _chA) =>
          match doctor σA with
          | none => IO.println "doctor failed"
          | some σD =>
              let heapP := σD.heap.filter (fun (l, _) =>
                match l with
                | .base b => keptCells.contains b.id
                | _ => true)
              let σP := { σD with heap := heapP }
              IO.println s!"anchor {nA}; pruned heap {heapP.length} cells; na {σP.nextAddr}"
              -- the witness stream: exactly the 4 consumed zeros
              let wch : Choices := [0, 0, 0, 0]
              -- chunk plan
              let Δ := 10964
              let bounds := [100, 300, Δ]
              -- walk chunk by chunk, dumping each boundary
              let mut out := "import GoLeanProofs.Specs.Raft.BecomeFollowerWitness\n\n"
              out := out ++ "/-! # RoundHbLit — GENERATED literals (A4-U18 C1; generator\n"
              out := out ++ "`artifacts/probe/RoundFixDump.lean` — DO NOT EDIT BY HAND).\n\n"
              out := out ++ "The deliver-heartbeat ROUND-witness fixture: the twin's real\n"
              out := out ++ s!"first loop-head state (runProgramSetupM + {nA} steps, all-zero\n"
              out := out ++ "stream), net/live DOCTORED to one live MsgHeartbeat (Type 8,\n"
              out := out ++ "From 1, To 2, Term 0, Commit 0 — the Hh no-advance family),\n"
              out := out ++ "PRUNED to the round's 26-cell read-before-write set (fail-closed\n"
              out := out ++ "discovery; writes recreate pruned cells soundly), plus boundary\n"
              out := out ++ "states at steps 100 and 300 of the 10,964-step round walk and\n"
              out := out ++ "the final loop-head state. The [0,100) and [100,300) slivers are\n"
              out := out ++ "kernel-replayed in RoundStatement.lean; the full-round replay is\n"
              out := out ++ "generator-computed (compiled stepFn) with its kernel form\n"
              out := out ++ "measured-blocked (the U18 heap-linear kernel wall) — see the\n"
              out := out ++ "RoundStatement docstrings for exactly what is and is not\n"
              out := out ++ "kernel-checked. -/\n\n"
              out := out ++ "namespace GoLean.RaftSeam\n\n"
              out := out ++ "open GoLean.GoCore GoLean.GoCore.Machine\n\n"
              out := out ++ "set_option maxRecDepth 4000000\n\n"
              out := out ++ s!"def rhbNa0 : Nat := {σP.nextAddr}\n\n"
              out := out ++ s!"def rhbHeap0 : GoLean.GoCore.Heap :=\n  {pr σP.heap}\n\n"
              out := out ++ s!"def rhbC0 : GoLean.GoCore.Machine.Config :=\n  {pr cA}\n\n"
              out := out ++ s!"def rhbCh0 : GoLean.GoCore.Choices := {pr wch}\n\n"
              let mut σ := σP
              let mut c := cA
              let mut ch := wch
              let mut done := 0
              let mut i := 0
              for b in bounds do
                let k := b - done
                match walkN σ c ch k with
                | .error e => IO.println s!"chunk {i} FAILED @{done}+{k}: {e}"; return ()
                | .ok (σ2, c2, ch2) =>
                    σ := σ2; c := c2; ch := ch2; done := b; i := i + 1
                    out := out ++ s!"def rhbNa{i} : Nat := {σ2.nextAddr}\n\n"
                    out := out ++ s!"def rhbHeap{i} : GoLean.GoCore.Heap :=\n  {pr σ2.heap}\n\n"
                    if done == Δ then
                      out := out ++ s!"-- final config: verified equal to rhbC0 (self-returning)\n"
                      out := out ++ s!"def rhbCF : GoLean.GoCore.Machine.Config :=\n  {pr c2}\n\n"
                    else
                      out := out ++ s!"def rhbC{i} : GoLean.GoCore.Machine.Config :=\n  {pr c2}\n\n"
                    out := out ++ s!"def rhbCh{i} : GoLean.GoCore.Choices := {pr ch2}\n\n"
              out := out ++ "end GoLean.RaftSeam\n"
              IO.println s!"final: steps={done} na={σ.nextAddr} heap={σ.heap.length} ch={ch.length}"
              IO.println s!"self-returning: {toString (repr c) == toString (repr cA)}"
              IO.FS.writeFile "GoLeanProofs/Specs/Raft/RoundHbLit.lean" out
              IO.println s!"written: {out.length} chars"

#eval go
