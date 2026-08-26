import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.BfEquation
import GoLeanProofs.Specs.Raft.StaticCells

/-! # A4-U12 slice 2b: the LOG-APPEND RE-CENSUS with the static-cell
complement. Fixture = the U11 LaProbe fixture (one entry (index 2,
term 1) after matching prev (1,1); m.Commit = 1) ++ the
staticComplement block at its true addresses; nextAddr = 98
(staticComplementNa). U11's run stuck at step 2689 on static cell 25
(ErrUnavailable); expectation: the stuck clears and the run proceeds
into the unstable-overlay territory (GAP-V1-1b) for the first time. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

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
   (.base ⟨60⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)] ++
  staticComplement

def laσ0 : ExecState := { wBase with heap := laHeap, nextAddr := staticComplementNa }

def laC0 : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def bigStream : Choices := List.replicate 60 0

-- single-pass walker: first error / stop
partial def walk (n : Nat) (σ : ExecState) (c : Machine.Config) (ch : Choices)
    (fuel : Nat) : String :=
  if fuel = 0 then
    s!"NO TERMINATION by step {n}; na={σ.nextAddr} ch={ch.length}"
  else match stepFn σ c ch with
    | .ok (Machine.Config.next .stop, σ2, ch2) =>
        s!"STOP at step {n+1}; na={σ2.nextAddr} choices={60 - ch2.length}"
    | .ok (c2, σ2, ch2) => walk (n+1) σ2 c2 ch2 (fuel - 1)
    | .error e =>
        s!"ERROR at step {n+1}: {e.status} : {e.message.take 300}"
#eval walk 0 laσ0 laC0 bigStream 20000

partial def findStop (n : Nat) : Nat :=
  if n > 20000 then 0
  else match stepFnIter n laσ0 laC0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | .error _ => n + 1000000
    | _ => findStop (n + 1)
def nStop := findStop 2600
#eval s!"completion at step {nStop}"

#eval match stepFnIter nStop laσ0 laC0 bigStream with
  | .ok (_, σ', ch) =>
      let maaStr : String := "msgsAfterAppend"
      let msgsStr : String := "msgs"
      s!"choices={60 - ch.length} na={σ'.nextAddr}\n" ++
      s!"msgsAfterAppend={(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 450}\n" ++
      s!"msgs={(toString (repr (absOutbox σ' ⟨31⟩ msgsStr))).take 120}\n" ++
      s!"absRaftLog post={(toString (repr (absRaftLog σ' ⟨32⟩))).take 350}\n" ++
      s!"absRaftLog pre={(toString (repr (absRaftLog laσ0 ⟨32⟩))).take 350}"
  | .error e => s!"ERROR {e.status}: {e.message.take 200}"

partial def findPops (n : Nat) (last : Nat) (acc : List Nat) : List Nat :=
  if n > nStop then acc.reverse
  else match stepFnIter n laσ0 laC0 bigStream with
    | .ok (_, _, ch) =>
        if 60 - ch.length > last then findPops (n+1) (60 - ch.length) ((n-1) :: acc)
        else findPops (n+1) last acc
    | _ => acc.reverse
#eval s!"choice-consumption step indices: {toString (repr (findPops 2600 0 []))}"

-- the derived log VIEW (the overlay actually read)
#eval match stepFnIter nStop laσ0 laC0 bigStream with
  | .ok (_, σ', _) =>
      match absRaftLog σ' ⟨32⟩ with
      | some al => s!"AbsLog.view post = {toString (repr (AbsLog.view al))} lastIndex = {toString (repr (AbsLog.lastIndex al))}"
      | none => "absRaftLog post = none (!)"
  | .error e => s!"ERROR {e.message.take 100}"

-- mirror window schedule with the sym block
def laS0sym : SymState :=
  { heap := laHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value))),
    nextAddr := staticComplementNa }
def laC0sym : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

partial def mirrorSchedule (S : SymState) (C : SymConfig) (acc : List Nat)
    (rounds : Nat) : String :=
  if rounds = 0 then s!"schedule (unfinished): {toString (repr acc.reverse)}"
  else
    let (n, S', C') := symEvalWindowTB bfTB 20000 S C
    match C' with
    | .next .stop => s!"schedule: {toString (repr (acc.reverse ++ [n]))} → .next .stop"
    | _ =>
      match stepFnSTB bfTB S' C' with
      | .ok _ => s!"schedule: {toString (repr (acc.reverse ++ [n]))} → budget?"
      | .error q =>
          s!"window {acc.length}: {n} steps, quit {toString (repr q)}; " ++
          mirrorSchedule S' C' (n :: acc) 0  -- stop at first quit for detail
#eval mirrorSchedule laS0sym laC0sym [] 1

def cfgHead : SymConfig → String
  | .exec _ _ _ => "exec" | .evalE _ _ _ => "evalE"
  | .retV _ (.stmtOpK op nt _ _ _ _) =>
      s!"retV/stmtOpK({(toString (repr op)).take 90}) nt={nt}"
  | .retV _ (.callArgsK f _ _ _ _ _) => s!"retV/callArgsK({f.key})"
  | .retV _ _ => "retV/other" | .next _ => "next" | _ => "other"
def w1 := symEvalWindowTB bfTB 20000 laS0sym laC0sym
#eval s!"w1: {w1.1} steps; quit config: {cfgHead w1.2.2}; na={w1.2.1.nextAddr}"
