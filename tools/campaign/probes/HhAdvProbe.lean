import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.StaleEquation

/-! # A4-U13 slot 2 census: the handleHeartbeat COMMIT-ADVANCE family
(the U10 residual — closes handleHeartbeat). Fixture: the stale
two-entry stable log at committed = 1 (lastIndex = 2 > committed),
m.Commit = 2 → commitTo takes the ADVANCE branch (committed := 2),
calling lastIndex() through the Bf dispatch chain; then the same
heartbeat-response send into `msgs`. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

/-- The two-entry log at committed = 1 (advance headroom). -/
def hhaLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", uEmptySlice), ("offset", uU64 3),
      ("snapshotInProgress", .bool false), ("offsetInProgress", uU64 3),
      ("logger", .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩)))]),
    ("committed", uU64 1), ("applying", uU64 1), ("applied", uU64 1),
    ("logger", .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))),
    ("maxApplyingEntsSize", uU64 1048576),
    ("applyingEntsSize", uU64 0), ("applyingEntsPaused", .bool false)]

def hhaMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def hhaHeap : GoCore.Heap :=
  (((uHeap 7 2 0 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))).map
    (fun (p : Loc × GoCore.HeapCell) =>
      if p.1 == .base ⟨32⟩ then (p.1, ⟨p.2.declaredTy, hhaLogVal⟩)
      else if p.1 == .base ⟨37⟩ then (p.1, ⟨p.2.declaredTy, staleMsValG⟩)
      else if p.1 == .base ⟨46⟩ then
        (p.1, ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
             .array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)]⟩)
      else p)) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), hhaMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), staleEntry2G⟩),
   (.base ⟨58⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def hhaσ0 : ExecState := { wBase with heap := hhaHeap, nextAddr := 60 }

def hhaC0 : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def bigStream : Choices := List.replicate 60 0

partial def walk (n : Nat) (σ : ExecState) (c : Machine.Config) (ch : Choices)
    (fuel : Nat) : String :=
  if fuel = 0 then s!"NO TERMINATION by {n}"
  else match stepFn σ c ch with
    | .ok (Machine.Config.next .stop, σ2, ch2) =>
        s!"STOP at step {n+1}; na={σ2.nextAddr} choices={60 - ch2.length}"
    | .ok (c2, σ2, ch2) => walk (n+1) σ2 c2 ch2 (fuel - 1)
    | .error e => s!"ERROR at {n+1}: {e.status} : {e.message.take 200}"
#eval walk 0 hhaσ0 hhaC0 bigStream 5000

partial def findStop (n : Nat) : Nat :=
  if n > 5000 then 0
  else match stepFnIter n hhaσ0 hhaC0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | .error _ => n + 1000000
    | _ => findStop (n + 1)
def nStop := findStop 1200
#eval s!"completion at {nStop}"

#eval match stepFnIter nStop hhaσ0 hhaC0 bigStream with
  | .ok (_, σ', ch) =>
      let msgsStr : String := "msgs"
      let maaStr : String := "msgsAfterAppend"
      s!"choices={60 - ch.length} na={σ'.nextAddr}\n" ++
      s!"msgs={(toString (repr (absOutbox σ' ⟨31⟩ msgsStr))).take 420}\n" ++
      s!"maa={(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 100}\n" ++
      s!"absRaftLog post={(toString (repr (absRaftLog σ' ⟨32⟩))).take 300}\n" ++
      s!"absRaftLog pre={(toString (repr (absRaftLog hhaσ0 ⟨32⟩))).take 300}"
  | .error e => s!"ERR {e.message.take 100}"

partial def findPops (n : Nat) (last : Nat) (acc : List Nat) : List Nat :=
  if n > nStop then acc.reverse
  else match stepFnIter n hhaσ0 hhaC0 bigStream with
    | .ok (_, _, ch) =>
        if 60 - ch.length > last then findPops (n+1) (60 - ch.length) ((n-1) :: acc)
        else findPops (n+1) last acc
    | _ => acc.reverse
#eval s!"choice pops: {toString (repr (findPops 1200 0 []))}"

-- mirror
def hhaS0sym : SymState :=
  { heap := hhaHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value))),
    nextAddr := 60 }
def hhaC0sym : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)
def w1 := symEvalWindowTB bfTB 8000 hhaS0sym hhaC0sym
#eval s!"mirror w1: {w1.1} steps; na={w1.2.1.nextAddr}"
#eval match stepFnSTB bfTB w1.2.1 w1.2.2 with
  | .ok _ => "w1 end: steps on?!"
  | .error q => s!"w1 quit: {toString (repr q)}"
def cfgHead : SymConfig → String
  | .retV _ (.stmtOpK op nt _ _ _ _) =>
      s!"retV/stmtOpK({(toString (repr op)).take 80}) nt={nt}"
  | _ => "other"
#eval s!"w1 quit config: {cfgHead w1.2.2}"
-- spill operands
#eval match stepFnIter w1.1 hhaσ0 hhaC0 bigStream with
  | .ok (.retV v (.stmtOpK _ _ done _ _ _), σ, _) =>
      s!"spill operands: vs = {(toString (repr ((v :: done).reverse))).take 260} na={σ.nextAddr}"
  | _ => "?"
#eval s!"post-window = {nStop - w1.1 - 1}"
