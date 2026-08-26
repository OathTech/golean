import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Specs.Raft.AbsStateV2

/-! # A4-U25: the MsgVoteResp ELECTION-COMPLETION round fixture (probe-only)

The U18 doctor+prune template's SECOND instantiation (the ledger row's
owed one): doctor the real run's first loop-head state to a single
live **MsgApp** (Type 3, From 1, To 2, Term 0 = the local family,
Index 0 / LogTerm 0 = match at the empty log, ONE entry (Index 1,
Term 1, empty Data), Commit 1) — the append-and-commit family, chosen
to drive the harvest ring through the storage-resp arms
(MemoryStorage.Append / newStorageAppendRespMsg / the Advance-nested
`raft.raft.Step` MsgStorageAppendResp arm, and the apply side), which
the U20 census proved unreachable from the heartbeat fixture.

Outputs: round steps/choices/na, self-returning check, node-2
raft + raftLog pre/post, net view post, and the pruned
read-before-write cell set. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.RaftSeam

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

/-- The loop-head anchor: `if round < 400 { … } else break`. -/
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

/-- One round: step off the anchor, then walk to the next anchor. -/
partial def walkRound (n : Nat) (σ : ExecState) (c : Config) (ch : Choices)
    (fuel : Nat) : Except String (Nat × ExecState × Config × Choices) :=
  if fuel = 0 then .error "OUT OF FUEL"
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) =>
        if isAnchor c2 then .ok (n+1, σ2, c2, ch2)
        else walkRound (n+1) σ2 c2 ch2 (fuel-1)
    | .error e => .error s!"@{n}: {e.message.take 200}"

def findTwin2 (h : Heap) : Option Loc :=
  h.findSome? (fun (l, c) =>
    if c.declaredTy == some (.defined ⟨"main.twin"⟩) then some l else none)

/-- A4-U25: the doctored MsgVoteResp, THE ELECTION-COMPLETION FAMILY:
Type 6, To 1 (THE CANDIDATE, self-vote already polled), From 2, Term
na+6 (1 = the candidate's term), Index/LogTerm nil, no entries,
Reject nil (GetReject = false → the vote is GRANTED). stepCandidate ×
MsgVoteResp → poll(2, granted) → quorum won → becomeLeader() → the
noop append + bcastAppend: THE ANCHOR 2→3 TRANSITION (candidate →
leader), the round-kind matrix's last structural ring shape. -/
def maMsgVal (na : Nat) : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨na⟩)), ("To", .addr (.base ⟨na+1⟩)),
    ("From", .addr (.base ⟨na+2⟩)), ("Term", .addr (.base ⟨na+6⟩)),
    ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .nil), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def maEntryVal (na : Nat) : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨na+7⟩)), ("Index", .addr (.base ⟨na+8⟩)),
    ("Type", .nil),
    ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- Doctor: inject the 1-message MsgApp net at fresh addresses. -/
def doctor (σ : ExecState) : Option ExecState := do
  let tl ← findTwin2 σ.heap
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
    [(.base ⟨na⟩, ⟨some (.int .int32), .int 6 .int32⟩),
     (.base ⟨na+1⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+2⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+3⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), maMsgVal na⟩),
     (.base ⟨na+4⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Message"⟩))),
        .array #[.addr (.base ⟨na+3⟩)]⟩),
     (.base ⟨na+5⟩, ⟨some (.array 1 .bool), .array #[.bool true]⟩),
     (.base ⟨na+6⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+7⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+8⟩, ⟨some (.int .uint64), .int 2 .uint64⟩), -- unused (no entries)
     (.base ⟨na+9⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), maEntryVal na⟩),
     (.base ⟨na+10⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
        .array #[.addr (.base ⟨na+9⟩)]⟩),
     (.base ⟨na+11⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+12⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]
  pure { σ with heap := heap', nextAddr := na + 13 }

/-- absTwinRead v0's node reader (U18's). -/
def nodeRaftAddr (σ : ExecState) (tl : Loc) (i : Nat) : Option Addr := do
  let tc ← Heap.lookup σ.heap tl
  let nodesv ← match tc.value with
    | .struct _ fs => StructFields.lookup fs "nodes" | _ => none
  let sv ← match nodesv with | .slice s => some s | _ => none
  let base ← sv.base
  let bc ← Heap.lookup σ.heap base
  let elems ← match bc.value with | .array vs => some vs | _ => none
  let ndp ← elems[sv.offset + i]?
  let ndl ← match ndp with | .addr l => some l | _ => none
  let nc ← Heap.lookup σ.heap ndl
  let rnv ← match nc.value with
    | .struct _ fs => StructFields.lookup fs "rn" | _ => none
  let rnl ← match rnv with | .addr l => some l | _ => none
  let rc ← Heap.lookup σ.heap rnl
  let rv ← match rc.value with
    | .struct _ fs => StructFields.lookup fs "raft" | _ => none
  match rv with | .addr (.base a) => some a | _ => none

def readNode (σ : ExecState) (tl : Loc) (i : Nat) : String :=
  match nodeRaftAddr σ tl i with
  | none => "chain broken"
  | some a =>
      let f := fun n => (GoLean.Lens.fieldReadU64 σ a ⟨"raft.raft"⟩ n).map toString |>.getD "?"
      s!"raft@{a.id} state={f "state"} Term={f "Term"} lead={f "lead"} Vote={f "Vote"}"

/-- The raftLog readout: raft → raftLog ptr → committed/applying/applied. -/
def readLog (σ : ExecState) (tl : Loc) (i : Nat) : String :=
  match nodeRaftAddr σ tl i with
  | none => "chain broken"
  | some a =>
    match Heap.lookup σ.heap (.base a) with
    | some rc =>
      (match rc.value with
       | .struct _ fs =>
         (match StructFields.lookup fs "raftLog" with
          | some (.addr (.base la)) =>
            let f := fun n => (GoLean.Lens.fieldReadU64 σ la ⟨"raft.raftLog"⟩ n).map toString |>.getD "?"
            s!"raftLog@{la.id} committed={f "committed"} applying={f "applying"} applied={f "applied"}"
          | _ => "?raftLog")
       | _ => "?struct")
    | none => "?cell"

def netView (σ : ExecState) (tl : Loc) : String :=
  match Heap.lookup σ.heap tl with
  | some tc =>
      (match tc.value with
       | .struct _ fs =>
          let nv := StructFields.lookup fs "net"
          match nv with
          | some (.slice sv) =>
            (match sv.base >>= fun b => Heap.lookup σ.heap b with
             | some bc =>
                (match bc.value with
                 | .array vs =>
                    String.intercalate "; " (vs.toList.map (fun v =>
                      s!"{(toString (repr (absMessage σ v))).take 90}"))
                 | _ => "?backing")
             | none => "?nobase")
          | _ => "?net"
       | _ => "?struct")
  | none => "?twin"

def parseUnbound (msg : String) : Option Nat := do
  let parts := msg.splitOn "id := "
  if parts.length < 2 then none else
  let tail := parts[1]!
  let digits := tail.toList.takeWhile Char.isDigit
  if digits.isEmpty then none else (String.mk digits).toNat?

partial def pruneLoop (full : ExecState) (c0 : Config) (ch : Choices)
    (kept : List Nat) (iter : Nat) : IO (List Nat) := do
  if iter > 1500 then IO.println "PRUNE: iteration cap"; return kept
  let heap' := full.heap.filter (fun (l, _) =>
    match l with
    | .base b => kept.contains b.id
    | _ => true)
  let σ' := { full with heap := heap' }
  match walkRound 0 σ' c0 ch 80000 with
  | .ok (n, _, _, _) =>
      IO.println s!"PRUNE done: kept={kept.length} cells, round steps={n} (iter {iter})"
      return kept
  | .error e =>
      match parseUnbound e with
      | some cellId =>
          if kept.contains cellId then
            IO.println s!"PRUNE stuck (cell {cellId} already kept): {e.take 150}"
            return kept
          else pruneLoop full c0 ch (cellId :: kept) (iter + 1)
      | none =>
          IO.println s!"PRUNE unparseable error: {e.take 250}"
          return kept

/-- The chosen anchor index (from the AnchorScan probe): the first
loop head where node 1 is LEADER with the becomeLeader noop pending
quorum. -/
def anchorN : Nat := 2

partial def walkToAnchorN (rounds : Nat) (σ : ExecState) (c : Config)
    (ch : Choices) : Option (Nat × ExecState × Config × Choices) := do
  let (n, σA, cA, chA) ← walkToAnchor 0 σ c ch 300000
  if rounds = 0 then some (n, σA, cA, chA)
  else
    match stepFn σA cA chA with
    | .ok (c2, σ2, ch2) =>
        (walkToAnchorN (rounds - 1) σ2 c2 ch2).map
          (fun (m, s, cc, hh) => (n + 1 + m, s, cc, hh))
    | .error _ => none

def go : IO Unit := do
  let stream : Choices := List.replicate 25000 0
  match runProgramSetupM 20000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[] stream with
  | .error e => IO.println s!"SETUP ERROR: {e.message.take 300}"
  | .ok (c₀, s₃, _, ch₁) =>
      match walkToAnchorN anchorN s₃ c₀ ch₁ with
      | none => IO.println "anchor not found"
      | some (nA, σA, cA, chA) =>
          IO.println s!"anchor at {nA}, na={σA.nextAddr}, heap={σA.heap.length}, ch={chA.length}"
          match doctor σA with
          | none => IO.println "doctor failed"
          | some σD =>
              match findTwin2 σD.heap with
              | none => IO.println "no twin post-doctor"
              | some tl =>
                IO.println s!"twin@{(toString (repr tl)).take 40}"
                IO.println s!"PRE : node1 {readNode σD tl 0}"
                IO.println s!"PRE : node1 {readLog σD tl 0}"
                IO.println s!"PRE : net {netView σD tl}"
                match walkRound 0 σD cA chA 80000 with
                | .error e => IO.println s!"round walk FAILED {e}"
                | .ok (Δ, σ', c', ch') =>
                    IO.println s!"ROUND: steps={Δ} choices={chA.length - ch'.length} na={σ'.nextAddr} (was {σD.nextAddr}) heap={σ'.heap.length}"
                    IO.println s!"config identical: {toString (repr c') == toString (repr cA)}"
                    IO.println s!"POST: node1 {readNode σ' tl 0}"
                    IO.println s!"POST: node1 {readLog σ' tl 0}"
                    IO.println s!"POST: net {netView σ' tl}"
                    let seed := (List.range 13).map (σA.nextAddr + ·) ++
                      (match tl with | .base b => [b.id] | _ => [])
                    let kept ← pruneLoop σD cA chA seed 0
                    IO.println s!"read set size: {kept.length}"
                    IO.println s!"read set (sorted): {(kept.toArray.qsort (· < ·)).toList}"

#eval go
