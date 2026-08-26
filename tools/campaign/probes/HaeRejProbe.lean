import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.BfEquation

/-! # A4-U14 census: the handleAppendEntries REJECT family (charter
item 1, census FIRST). Fixture: born re-sited, two-entry stable log
with a TERM-DIVERGENT tip — ents (1,1),(2,2), committed = 1
(≤ lastIndex = 2, consistent), unstable empty at offset 3; message
From=2, LogTerm=1, Index=2, Commit=1, Entries empty. Path:
prev.index 2 ≥ committed 1 (not stale); matchTerm{term 1, index 2}
fails (term(2) = 2 ≠ 1) → REJECT: Debugf args (zeroTermOnOutOfBounds
∘ term — err=nil early arm), hintIndex = min(2, lastIndex 2) = 2,
findConflictByTerm(2, 1) = TWO live iterations (term(2)=2>1 → dec;
term(1)=1≤1 → return (1,1)), resp ⟨4, To=2, Index=2, Reject=true,
RejectHint=1, LogTerm=1⟩ → msgsAfterAppend appendSlice spill.
Census questions: total steps / choices / static-cell reads
([20,31) — expected NONE: every term() here returns err=nil) /
window schedule / anything outside the landed quit classes. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def ifaceHarness36 : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))

/-- The two-entry raftLog cell (at 32): committed/applying/applied 1. -/
def rejLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", uEmptySlice), ("offset", uU64 3),
      ("snapshotInProgress", .bool false), ("offsetInProgress", uU64 3),
      ("logger", ifaceHarness36)]),
    ("committed", uU64 1), ("applying", uU64 1), ("applied", uU64 1),
    ("logger", ifaceHarness36), ("maxApplyingEntsSize", uU64 1048576),
    ("applyingEntsSize", uU64 0), ("applyingEntsPaused", .bool false)]

/-- MemoryStorage with the 2-entry ents slice (at 37). -/
def rejMsVal : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨46⟩), offset := 0, len := 2, cap := 2 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", uI64 0), ("firstIndex", uI64 0), ("lastIndex", uI64 0),
      ("entries", uI64 0), ("term", uI64 0), ("snapshot", uI64 0)])]

def rejMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)), ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- Entry 2 with TERM 2 (the divergent tip; 58 = Term, 59 = Index). -/
def rejEntry2 : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨58⟩)), ("Index", .addr (.base ⟨59⟩)),
    ("Type", .nil), ("Data", uEmptySlice)]

def rejBase : GoCore.Heap :=
  (uHeap 7 2 0 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))

def rejReplace : Loc × HeapCell → Loc × HeapCell := fun (l, c) =>
  if l == .base ⟨32⟩ then (l, ⟨c.declaredTy, rejLogVal⟩)
  else if l == .base ⟨37⟩ then (l, ⟨c.declaredTy, rejMsVal⟩)
  else if l == .base ⟨46⟩ then
    (l, ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
         .array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)]⟩)
  else (l, c)

def rejHeap : GoCore.Heap :=
  (rejBase.map rejReplace) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), rejMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨56⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), rejEntry2⟩),
   (.base ⟨58⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def rejσ0 : ExecState := { wBase with heap := rejHeap, nextAddr := 60 }

def rejC0 : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def bigStream : Choices := List.replicate 60 0

/-- ONE-PASS walker: returns (stopStep, choicesConsumed, na, pop step
indices, static [20,31) deref step indices, err?). -/
partial def walkAll (n : Nat) (σ : ExecState) (c : Machine.Config)
    (ch : Choices) (pops : List Nat) (statics : List (Nat × Nat))
    (fuel : Nat) : (Nat × Nat × Nat × List Nat × List (Nat × Nat) × String) :=
  if fuel = 0 then (n, 60 - ch.length, σ.nextAddr, pops.reverse, statics.reverse, "OUT OF FUEL")
  else
    let statics' := match c with
      | .evalE (Expr.deref (Expr.locLit (.base b)) _) _ _ =>
          if 20 ≤ b.id && b.id < 31 then (n, b.id) :: statics else statics
      | _ => statics
    match stepFn σ c ch with
    | .ok (Machine.Config.next .stop, σ2, ch2) =>
        (n+1, 60 - ch2.length, σ2.nextAddr, pops.reverse, statics'.reverse, "STOP")
    | .ok (c2, σ2, ch2) =>
        let pops' := if ch2.length < ch.length then n :: pops else pops
        walkAll (n+1) σ2 c2 ch2 pops' statics' (fuel - 1)
    | .error e => (n+1, 60 - ch.length, σ.nextAddr, pops.reverse, statics'.reverse,
        s!"ERROR {e.status}: {e.message.take 150}")

def wres := walkAll 0 rejσ0 rejC0 bigStream [] [] 15000
#eval s!"stop/steps={wres.1} choices={wres.2.1} na={wres.2.2.1} verdict={wres.2.2.2.2.2}"
#eval s!"choice-consumption step indices: {toString (repr wres.2.2.2.1)}"
#eval s!"static [20,31) derefs (step, cell): {toString (repr wres.2.2.2.2.1)}"
def nStop := wres.1

#eval match stepFnIter nStop rejσ0 rejC0 bigStream with
  | .ok (_, σ', ch) =>
      let maaStr : String := "msgsAfterAppend"
      let msgsStr : String := "msgs"
      s!"choices={60 - ch.length} na={σ'.nextAddr}\n" ++
      s!"msgsAfterAppend={(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 500}\n" ++
      s!"msgs={(toString (repr (absOutbox σ' ⟨31⟩ msgsStr))).take 120}\n" ++
      s!"absRaftLog post={(toString (repr (absRaftLog σ' ⟨32⟩))).take 300}"
  | .error e => s!"ERROR {e.status}: {e.message.take 200}"

#eval s!"absRaftLog pre={(toString (repr (absRaftLog rejσ0 ⟨32⟩))).take 300}"
#eval s!"absMessage pre={(toString (repr (absMessage rejσ0 (.addr (.base ⟨52⟩))))).take 260}"

-- mirror window schedule
def rejSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  rejHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value)))
def rejS0 : SymState := { heap := rejSymHeap, nextAddr := 60 }
def rejC0sym : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def w1 := symEvalWindowTB bfTB 12000 rejS0 rejC0sym
#eval s!"mirror window 1: {w1.1} steps"
def cfgHead : SymConfig → String
  | .exec _ _ _ => "exec" | .evalE _ _ _ => "evalE"
  | .retV _ (.stmtOpK op nt _ _ _ _) =>
      s!"retV/stmtOpK({(toString (repr op)).take 80}) nt={nt}"
  | .retV _ (.callArgsK f _ _ _ _ _) => s!"retV/callArgsK({f.key})"
  | .retV _ _ => "retV/other" | .next .stop => "next STOP" | .next _ => "next"
  | _ => "other"
#eval s!"w1 quit config: {cfgHead w1.2.2}"
#eval s!"w1 out na: {w1.2.1.nextAddr}"
#eval match stepFnSTB bfTB w1.2.1 w1.2.2 with
  | .ok _ => "w1 end: steps on (budget exhausted?)"
  | .error q => s!"w1 quit: {toString (repr q)}"
-- spill operands at the machine quit step
#eval match stepFnIter w1.1 rejσ0 rejC0 bigStream with
  | .ok (.retV v (.stmtOpK _ _ done _ _ _), σ, _) =>
      s!"machine spill operands: vs = {(toString (repr ((v :: done).reverse))).take 300} na={σ.nextAddr}"
  | _ => "?"
#eval s!"post-window = {nStop - w1.1 - 1} steps"
