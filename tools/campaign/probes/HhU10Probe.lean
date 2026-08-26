import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.BfEquation

/-! # A4-U10 probe 1: the appendSpill site's exact step/choice shape
(charter deliverable 1's PROBE FIRST) + the window schedule for the
handleHeartbeat equation. Fixture = U9's `HhProbe` recipe verbatim
(born re-sited, bf31 pattern). -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

-- ## The U9 fixture, verbatim

def hhMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def hhHeap : GoCore.Heap :=
  ((uHeap 7 2 0 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), hhMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def hhσ0 : ExecState := { wBase with heap := hhHeap, nextAddr := 55 }

def hhC0 : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def bigStream : Choices := List.replicate 40 0

-- ## 1. Find the spill step (first step that pops the stream)

partial def findSpill (n : Nat) : Nat :=
  if n > 2000 then 0
  else match stepFnIter n hhσ0 hhC0 bigStream with
    | .ok (_, _, ch) => if ch.length < 40 then n else findSpill (n + 1)
    | _ => 0
def nSpill := findSpill 1
#eval s!"first stream pop after step {nSpill} (spill step index = {nSpill - 1})"

-- ## 2. The config AT the spill (one step before the pop completes)

def preSpill := stepFnIter (nSpill - 1) hhσ0 hhC0 bigStream

#eval match preSpill with
  | .ok (c, σ, ch) =>
      match c with
      | .retV v (.stmtOpK op nt done pending _ _) =>
          s!"SPILL CONFIG: retV/stmtOpK op={toString (repr op)} nt={nt} " ++
          s!"v={toString (repr v)} done={toString (repr done)} " ++
          s!"pending={pending.length} na={σ.nextAddr} ch={ch.length}"
      | _ => "UNEXPECTED config shape"
  | .error e => s!"ERROR {e.message}"

-- the operand list the apply sees: (v :: done).reverse
#eval match preSpill with
  | .ok (.retV v (.stmtOpK _ _ done _ _ _), _, _) =>
      s!"vs = {toString (repr ((v :: done).reverse))}"
  | _ => "?"

-- ## 3. The post-spill delta at three choice values

def spillAt (c : Nat) : Except GoError (Machine.Config × ExecState × Choices) :=
  stepFnIter nSpill hhσ0 hhC0 (c :: bigStream)

def cellStr (σ : ExecState) (l : Loc) : String :=
  match Heap.lookup σ.heap l with
  | some cell => s!"⟨{toString (repr cell.declaredTy)}, {(toString (repr cell.value)).take 300}⟩"
  | none => "MISSING"

#eval match preSpill, spillAt 0 with
  | .ok (_, σ₁, _), .ok (_, σ₂, ch) =>
      s!"c=0: na {σ₁.nextAddr}→{σ₂.nextAddr} ch={ch.length} " ++
      s!"backing={cellStr σ₂ (.base ⟨σ₁.nextAddr⟩)} "
  | _, _ => "?"
#eval match preSpill, spillAt 0 with
  | .ok (_, σ₁, _), .ok (_, σ₂, _) =>
      s!"c=0: raft-msgs-after: " ++
      (toString (repr (GoLean.Lens.fieldRead σ₂ ⟨31⟩ ⟨"raft.raft"⟩ "msgs"))).take 200
  | _, _ => "?"
#eval match spillAt 5 with
  | .ok (_, σ₂, _) =>
      s!"c=5: backing={cellStr σ₂ (.base ⟨(σ₂.nextAddr) - 1⟩)}"
  | _ => "?"
#eval match spillAt 31 with
  | .ok (_, σ₂, _) =>
      s!"c=31: backing declaredTy+len: " ++
      (match Heap.lookup σ₂.heap (.base ⟨σ₂.nextAddr - 1⟩) with
       | some ⟨ty, .array vs⟩ => s!"{toString (repr ty)} len={vs.size}"
       | _ => "?")
  | _ => "?"

-- ## 4. The post-window: steps after the spill to completion, and
-- whether the post-window touches the heap at all

partial def findStop2 (n : Nat) : Nat :=
  if n > 2000 then 0
  else match stepFnIter n hhσ0 hhC0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | _ => findStop2 (n + 1)
def nStop := findStop2 nSpill
#eval s!"completion at {nStop}; post-window = {nStop - nSpill} steps"

#eval match spillAt 3, stepFnIter nStop hhσ0 hhC0 (3 :: bigStream) with
  | .ok (_, σ₂, _), .ok (c₃, σ₃, ch₃) =>
      let stop := match c₃ with | .next .stop => true | _ => false
      s!"post-window heap unchanged: {σ₂.heap == σ₃.heap} " ++
      s!"na unchanged: {σ₂.nextAddr == σ₃.nextAddr} final-stop={stop} ch={ch₃.length}"
  | _, _ => "?"

-- ## 5. The mirror: pre-window quit position + γ-image agreement

def hhS0sym : SymState :=
  { heap := hhHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value))),
    nextAddr := 55 }

def hhC0sym : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def preWin := symEvalWindowTB bfTB 2000 hhS0sym hhC0sym

#eval s!"mirror pre-window: {preWin.1} steps (expect {nSpill - 1})"
#eval match preWin.2.2 with
  | .retV _ (.stmtOpK op nt _ pending _ _) =>
      s!"mirror quit config: retV/stmtOpK op={toString (repr op)} nt={nt} pending={pending.length}"
  | _ => "UNEXPECTED mirror quit shape"

-- γ-image at the quit == machine state at the same step?
#eval match preSpill with
  | .ok (cM, σM, _) =>
      let σγ := γS uρw hhσ0 preWin.2.1
      let cγ := γC uρw preWin.2.2
      let cfgEq := match cγ, cM with
        | .retV v1 k1, .retV v2 _ => v1 == v2
        | _, _ => false
      s!"γ-heap == machine heap: {σγ.heap == σM.heap} " ++
      s!"γ-na == machine na: {σγ.nextAddr == σM.nextAddr} " ++
      s!"γ-retV-value == machine: {cfgEq}"
  | _ => "?"

-- ## 6. Projections at the final state (U9 re-check at this probe)

def msgsStr : String := "msgs"
#eval match stepFnIter nStop hhσ0 hhC0 (3 :: bigStream) with
  | .ok (_, σ₃, _) =>
      let ob := absOutbox σ₃ ⟨31⟩ msgsStr
      let cm := (absRaftLog σ₃ ⟨32⟩).map AbsLog.committed
      let vt := GoLean.Lens.fieldReadU64 σ₃ ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      s!"absOutbox = {toString (repr ob)}\ncommitted = {toString (repr cm)} Vote = {toString (repr vt)}"
  | _ => "?"
