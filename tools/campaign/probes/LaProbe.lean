import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.BfEquation

/-! # A4-U10 deliverable 4: handleAppendEntries PROBE CENSUS (U9
style — static read + dynamic run; no equation). Fixture family:
the LOG-APPEND family: ONE entry (index 2, term 1) after matching prev (1,1); m.Commit = 1. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def laMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)),
    ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := some (.base ⟨57⟩), offset := 0, len := 1, cap := 1 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def laHeap : GoCore.Heap :=
  ((uHeap 7 2 0 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), laMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨56⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
      .array #[.addr (.base ⟨58⟩)]⟩),
   (.base ⟨58⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩),
      .struct ⟨"raftpb.Entry"⟩ #[
        ("Term", .addr (.base ⟨59⟩)), ("Index", .addr (.base ⟨60⟩)),
        ("Type", .nil), ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨60⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def laσ0 : ExecState := { wBase with heap := laHeap, nextAddr := 61 }

def laC0 : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def bigStream : Choices := List.replicate 60 0

partial def findStop (n : Nat) : Nat :=
  if n > 8000 then 0
  else match stepFnIter n laσ0 laC0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | _ => findStop (n + 1)
def nStop := findStop 1
#eval s!"completion at step {nStop}"

#eval match stepFnIter nStop laσ0 laC0 bigStream with
  | .ok (_, σ', ch) =>
      let msgsStr : String := "msgs"
      let ob := absOutbox σ' ⟨31⟩ msgsStr
      let cm := (absRaftLog σ' ⟨32⟩).map AbsLog.committed
      let full := (toString (repr (absRaftLog σ' ⟨32⟩))).take 300
      s!"choices={60 - ch.length} na={σ'.nextAddr} outbox={(toString (repr ob)).take 300}\nabsRaftLog={full}"
  | .error e => s!"ERROR {e.status}: {e.message}"

-- where do the choices go? find each stream-pop step
partial def findPops (n : Nat) (last : Nat) (acc : List Nat) : List Nat :=
  if n > nStop then acc.reverse
  else match stepFnIter n laσ0 laC0 bigStream with
    | .ok (_, _, ch) =>
        if 60 - ch.length > last then findPops (n+1) (60 - ch.length) ((n-1) :: acc)
        else findPops (n+1) last acc
    | _ => acc.reverse
#eval s!"choice-consumption step indices: {toString (repr (findPops 1 0 []))}"

-- the mirror window schedule: run symEvalWindowTB to each quit
def laS0sym : SymState :=
  { heap := laHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value))),
    nextAddr := 61 }
def laC0sym : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def w1 := symEvalWindowTB bfTB 8000 laS0sym laC0sym
#eval s!"mirror window 1: {w1.1} steps"
#eval match stepFnSTB bfTB w1.2.1 w1.2.2 with
  | .ok _ => "w1 end: steps on (budget exhausted?)"
  | .error q => s!"w1 quit: {toString (repr q)}"
def cfgHead : SymConfig → String
  | .exec _ _ _ => "exec" | .evalE _ _ _ => "evalE"
  | .retV _ (.stmtOpK op _ _ _ _ _) => s!"retV/stmtOpK({(toString (repr op)).take 60})"
  | .retV _ (.callArgsK f _ _ _ _ _) => s!"retV/callArgsK({f.key})"
  | .retV _ _ => "retV/other" | .next _ => "next" | _ => "other"
#eval s!"w1 quit config: {cfgHead w1.2.2}"

#eval match stepFnIter nStop laσ0 laC0 bigStream with
  | .ok (_, σ', _) =>
      let maaStr : String := "msgsAfterAppend"
      s!"msgsAfterAppend = {(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 420}"
  | .error e => s!"ERROR {e.message}"
#eval s!"post-window = {nStop - 2798 - 1} steps"
-- spill operands at 2798
#eval match stepFnIter 2798 laσ0 laC0 bigStream with
  | .ok (.retV v (.stmtOpK _ _ done _ _ _), σ, _) =>
      s!"vs = {(toString (repr ((v :: done).reverse))).take 300} na={σ.nextAddr}"
  | _ => "?"

-- classify: does the machine ERROR, and where?
partial def findErr (n : Nat) : String :=
  if n > 4000 then "no error through 4000"
  else match stepFnIter n laσ0 laC0 bigStream with
    | .ok _ => findErr (n + 1)
    | .error e => s!"machine ERROR at step {n}: {e.status} : {(e.message.take 200)}"
#eval findErr 2600
#eval match stepFnIter 2688 laσ0 laC0 bigStream with
  | .ok (c, σ, _) => s!"machine @2688 ok, na={σ.nextAddr}"
  | .error e => s!"@2688 err {e.message.take 120}"
