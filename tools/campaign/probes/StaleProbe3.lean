import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.BfEquation

/-! # A4-U12 slice 1 census: the STALE family at the U11 fixture-value
note's fixture — a CONSISTENT two-entry log (storage ents (1,1),(1,2);
committed = 2 = lastIndex; unstable offset 3) with the Hae message
VERBATIM (Index→56 = 1, LogTerm→55 = 1, Commit→53 = 1, From→54 = 2):
prev.index = 1 < committed = 2 → the STALE branch; resp Index =
committed = 2, observably distinct from the landed success record
(Index 1). The two families now differ ONLY in the pre-state log. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def ifaceHarness36 : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))

/-- The two-entry raftLog cell (at 32; addresses written re-sited). -/
def staleLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", uEmptySlice), ("offset", uU64 3),
      ("snapshotInProgress", .bool false), ("offsetInProgress", uU64 3),
      ("logger", ifaceHarness36)]),
    ("committed", uU64 2), ("applying", uU64 2), ("applied", uU64 2),
    ("logger", ifaceHarness36), ("maxApplyingEntsSize", uU64 1048576),
    ("applyingEntsSize", uU64 0), ("applyingEntsPaused", .bool false)]

/-- MemoryStorage with a 2-entry ents slice (at 37). -/
def staleMsVal : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨46⟩), offset := 0, len := 2, cap := 2 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", uI64 0), ("firstIndex", uI64 0), ("lastIndex", uI64 0),
      ("entries", uI64 0), ("term", uI64 0), ("snapshot", uI64 0)])]

def staleMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)), ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def staleEntry2 : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨58⟩)), ("Index", .addr (.base ⟨59⟩)),
    ("Type", .nil), ("Data", uEmptySlice)]

def staleBase : GoCore.Heap :=
  (uHeap 7 2 0 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))

def staleReplace : Loc × HeapCell → Loc × HeapCell := fun (l, c) =>
  if l == .base ⟨32⟩ then (l, ⟨c.declaredTy, staleLogVal⟩)
  else if l == .base ⟨37⟩ then (l, ⟨c.declaredTy, staleMsVal⟩)
  else if l == .base ⟨46⟩ then
    (l, ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
         .array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)]⟩)
  else (l, c)

def staleHeap : GoCore.Heap :=
  (staleBase.map staleReplace) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), staleMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨56⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), staleEntry2⟩),
   (.base ⟨58⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def staleσ0 : ExecState := { wBase with heap := staleHeap, nextAddr := 60 }

def staleC0 : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def bigStream : Choices := List.replicate 60 0

partial def findStop (n : Nat) : Nat :=
  if n > 8000 then 0
  else match stepFnIter n staleσ0 staleC0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | .error _ => n + 100000
    | _ => findStop (n + 1)
def nStop := findStop 1
#eval s!"completion at step {nStop}"

#eval match stepFnIter nStop staleσ0 staleC0 bigStream with
  | .ok (_, σ', ch) =>
      let maaStr : String := "msgsAfterAppend"
      let msgsStr : String := "msgs"
      s!"choices={60 - ch.length} na={σ'.nextAddr}\n" ++
      s!"msgsAfterAppend={(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 420}\n" ++
      s!"msgs={(toString (repr (absOutbox σ' ⟨31⟩ msgsStr))).take 120}\n" ++
      s!"absRaftLog post={(toString (repr (absRaftLog σ' ⟨32⟩))).take 300}"
  | .error e => s!"ERROR {e.status}: {e.message.take 200}"

#eval s!"absRaftLog pre={(toString (repr (absRaftLog staleσ0 ⟨32⟩))).take 300}"
#eval s!"absMessage pre={(toString (repr (absMessage staleσ0 (.addr (.base ⟨52⟩))))).take 200}"

partial def findPops (n : Nat) (last : Nat) (acc : List Nat) : List Nat :=
  if n > nStop then acc.reverse
  else match stepFnIter n staleσ0 staleC0 bigStream with
    | .ok (_, _, ch) =>
        if 60 - ch.length > last then findPops (n+1) (60 - ch.length) ((n-1) :: acc)
        else findPops (n+1) last acc
    | _ => acc.reverse
#eval s!"choice-consumption step indices: {toString (repr (findPops 1 0 []))}"

-- mirror window schedule
def staleS0sym : SymState :=
  { heap := staleHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value))),
    nextAddr := 60 }
def staleC0sym : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def w1 := symEvalWindowTB bfTB 8000 staleS0sym staleC0sym
#eval s!"mirror window 1: {w1.1} steps"
#eval match stepFnSTB bfTB w1.2.1 w1.2.2 with
  | .ok _ => "w1 end: steps on (budget exhausted?)"
  | .error q => s!"w1 quit: {toString (repr q)}"
def cfgHead : SymConfig → String
  | .exec _ _ _ => "exec" | .evalE _ _ _ => "evalE"
  | .retV _ (.stmtOpK op nt _ _ _ _) =>
      s!"retV/stmtOpK({(toString (repr op)).take 80}) nt={nt}"
  | .retV _ (.callArgsK f _ _ _ _ _) => s!"retV/callArgsK({f.key})"
  | .retV _ _ => "retV/other" | .next _ => "next" | _ => "other"
#eval s!"w1 quit config: {cfgHead w1.2.2}"
#eval s!"w1 out na: {w1.2.1.nextAddr}"
-- spill operands at the machine quit step
#eval match stepFnIter w1.1 staleσ0 staleC0 bigStream with
  | .ok (.retV v (.stmtOpK _ _ done _ _ _), σ, _) =>
      s!"machine spill operands: vs = {(toString (repr ((v :: done).reverse))).take 300} na={σ.nextAddr}"
  | _ => "?"
#eval s!"post-window = {nStop - w1.1 - 1} steps"
