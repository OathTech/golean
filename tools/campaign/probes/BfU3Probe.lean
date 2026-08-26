/- A4-U3 phase-1 probe: the POPULATED fixture (probe2's cell-dump
recipe, re-addressed small), machine-run end-to-end from the drained
becomeFollower call. Validates twin shape (fail closed), counts steps
+ choices, locates the dispatch sites, checks the projection. -/
import GoLean.GoCore.MachineEqb
import GoLeanProofs.Specs.Raft.HandlerEqSym
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam
open GoLean.Examples.RaftTwin (twinLowered)

/-! Fixture cell values (concrete GoValue level), parameterized over
the five later-symbolic scalars. Address map:
0 raft, 1 raftLog, 2 Progress mapData, 3 Votes mapData, 4 readOnly,
5 harnessLogger, 6 MemoryStorage, 7-9 Progress cells, 10-12 Inflights,
13 acks mapData, 14 Voters[0] mapData, 15 ents array, 16 Entry,
17 Entry.Term target, 18 static *lockedRand, 19 lockedRand,
20 Entry.Index target; nextAddr 21. -/

def emptySlice : GoValue := .slice { base := none, offset := 0, len := 0, cap := 0 }
def u64 (n : Int) : GoValue := .int n .uint64
def i64 (n : Int) : GoValue := .int n .int
def loggerIface : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨5⟩))

def fxRaftVal (vote lead state ldT : Int) : GoValue :=
  .struct ⟨"raft.raft"⟩ #[
    ("id", u64 1), ("Term", u64 0), ("Vote", u64 vote),
    ("readStates", emptySlice), ("raftLog", .addr (.base ⟨1⟩)),
    ("maxMsgSize", u64 1048576), ("maxUncommittedSize", u64 18446744073709551615),
    ("trk", .struct ⟨"tracker.ProgressTracker"⟩ #[
      ("Config", .struct ⟨"tracker.Config"⟩ #[
        ("Voters", .array #[.map { base := some (.base ⟨14⟩) }, .map { base := none }]),
        ("AutoLeave", .bool false), ("Learners", .map { base := none }),
        ("LearnersNext", .map { base := none })]),
      ("Progress", .map { base := some (.base ⟨2⟩) }),
      ("Votes", .map { base := some (.base ⟨3⟩) }),
      ("MaxInflight", i64 256), ("MaxInflightBytes", u64 18446744073709551615)]),
    ("state", u64 state), ("isLearner", .bool false),
    ("msgs", emptySlice), ("msgsAfterAppend", emptySlice),
    ("lead", u64 lead), ("leadTransferee", u64 ldT),
    ("pendingConfIndex", u64 0), ("disableConfChangeValidation", .bool false),
    ("uncommittedSize", u64 0), ("readOnly", .addr (.base ⟨4⟩)),
    ("electionElapsed", i64 0), ("heartbeatElapsed", i64 0),
    ("checkQuorum", .bool false), ("preVote", .bool false),
    ("heartbeatTimeout", i64 1), ("electionTimeout", i64 10),
    ("randomizedElectionTimeout", i64 0),
    ("disableProposalForwarding", .bool false), ("stepDownOnRemoval", .bool false),
    ("tick", .nil), ("step", .nil), ("logger", loggerIface),
    ("pendingReadIndexMessages", emptySlice), ("traceLogger", .nil)]

def fxLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨6⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", emptySlice), ("offset", u64 2),
      ("snapshotInProgress", .bool false), ("offsetInProgress", u64 2),
      ("logger", loggerIface)]),
    ("committed", u64 1), ("applying", u64 1), ("applied", u64 1),
    ("logger", loggerIface), ("maxApplyingEntsSize", u64 1048576),
    ("applyingEntsSize", u64 0), ("applyingEntsPaused", .bool false)]

def fxMsVal : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨15⟩), offset := 0, len := 1, cap := 1 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", i64 0), ("firstIndex", i64 0), ("lastIndex", i64 0),
      ("entries", i64 0), ("term", i64 0), ("snapshot", i64 0)])]

def fxProgressVal (infl : Nat) : GoValue :=
  .struct ⟨"tracker.Progress"⟩ #[
    ("Match", u64 0), ("Next", u64 1), ("sentCommit", u64 0),
    ("State", u64 0), ("PendingSnapshot", u64 0), ("RecentActive", .bool true),
    ("MsgAppFlowPaused", .bool false), ("Inflights", .addr (.base ⟨infl⟩)),
    ("IsLearner", .bool false)]

def fxInflightsVal : GoValue :=
  .struct ⟨"tracker.Inflights"⟩ #[
    ("start", i64 0), ("count", i64 0), ("bytes", u64 0),
    ("size", i64 256), ("maxBytes", u64 18446744073709551615),
    ("buffer", emptySlice)]

def fxReadOnlyVal : GoValue :=
  .struct ⟨"raft.readOnly"⟩ #[
    ("option", i64 0), ("acks", .map { base := some (.base ⟨13⟩) }),
    ("unconfirmedReads", emptySlice), ("confirmedReads", u64 0)]

def fxEntryVal : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨17⟩)), ("Index", .addr (.base ⟨20⟩)),
    ("Type", .nil), ("Data", emptySlice)]

def stEmpty : GoValue := .struct ⟨"struct{}"⟩ #[]

def fxHeap (vote lead state ldT : Int) : GoCore.Heap :=
  [(.base ⟨0⟩, ⟨some (.defined ⟨"raft.raft"⟩), fxRaftVal vote lead state ldT⟩),
   (.base ⟨1⟩, ⟨some (.defined ⟨"raft.raftLog"⟩), fxLogVal⟩),
   (.base ⟨2⟩, ⟨none, .mapData #[(u64 1, .addr (.base ⟨7⟩)), (u64 2, .addr (.base ⟨8⟩)), (u64 3, .addr (.base ⟨9⟩))]⟩),
   (.base ⟨3⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨4⟩, ⟨some (.defined ⟨"raft.readOnly"⟩), fxReadOnlyVal⟩),
   (.base ⟨5⟩, ⟨some (.defined ⟨"main.harnessLogger"⟩), .struct ⟨"main.harnessLogger"⟩ #[]⟩),
   (.base ⟨6⟩, ⟨some (.defined ⟨"raft.MemoryStorage"⟩), fxMsVal⟩),
   (.base ⟨7⟩, ⟨some (.defined ⟨"tracker.Progress"⟩), fxProgressVal 10⟩),
   (.base ⟨8⟩, ⟨some (.defined ⟨"tracker.Progress"⟩), fxProgressVal 11⟩),
   (.base ⟨9⟩, ⟨some (.defined ⟨"tracker.Progress"⟩), fxProgressVal 12⟩),
   (.base ⟨10⟩, ⟨some (.defined ⟨"tracker.Inflights"⟩), fxInflightsVal⟩),
   (.base ⟨11⟩, ⟨some (.defined ⟨"tracker.Inflights"⟩), fxInflightsVal⟩),
   (.base ⟨12⟩, ⟨some (.defined ⟨"tracker.Inflights"⟩), fxInflightsVal⟩),
   (.base ⟨13⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨14⟩, ⟨none, .mapData #[(u64 1, stEmpty), (u64 2, stEmpty), (u64 3, stEmpty)]⟩),
   (.base ⟨15⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))), .array #[.addr (.base ⟨16⟩)]⟩),
   (.base ⟨16⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), fxEntryVal⟩),
   (.base ⟨17⟩, ⟨some (.int .uint64), u64 1⟩),
   (.base ⟨18⟩, ⟨some (.pointer (.defined ⟨"raft.lockedRand"⟩)), .addr (.base ⟨19⟩)⟩),
   (.base ⟨19⟩, ⟨some (.defined ⟨"raft.lockedRand"⟩),
      .struct ⟨"raft.lockedRand"⟩ #[("mu", .syncData (.mutex false))]⟩),
   (.base ⟨20⟩, ⟨some (.int .uint64), u64 1⟩)]

def fxσ (vote lead state ldT : Int) : ExecState :=
  { wBase with heap := fxHeap vote lead state ldT, nextAddr := 21 }

def fxC (leadArg : Int) : Machine.Config :=
  .retV (u64 leadArg)
    (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
      [.addr (.base ⟨0⟩), .int 0 .uint64] [] [] .stop)

partial def framesInK : Machine.Cont → Nat
  | .frame (k := k) .. => 1 + framesInK k
  | .stop => 0
  | k => framesInK (kTail k)
where kTail : Machine.Cont → Machine.Cont
  | .seq (k := k) .. | .loop (k := k) .. | .frame (k := k) ..
  | .deferCalleeK (k := k) .. | .deferArgsK (k := k) ..
  | .breakableK (k := k) .. | .labelK (k := k) ..
  | .callValCalleeK (k := k) .. | .callValArgsK (k := k) ..
  | .strictK (k := k) .. | .andK (k := k) .. | .orK (k := k) ..
  | .boolK (k := k) .. | .ifK (k := k) .. | .whileK (k := k) ..
  | .callArgsK (k := k) .. | .stmtOpK (k := k) ..
  | .mapRangeK (k := k) .. | .mapIterK (k := k) ..
  | .panicArgK (k := k) .. | .panicResumeK (k := k) ..
  | .chanStK (k := k) .. | .selectOpsK (k := k) ..
  | .tgtOpK (k := k) .. | .rhsK (k := k) ..
  | .storeK (k := k) .. | .goCalleeK (k := k) ..
  | .goArgsK (k := k) .. | .syncStK (k := k) ..
  | .stop => .stop

def mainPhase1 : IO Unit := do
  let σ0 := fxσ 7 2 1 5
  let c0 := fxC 4
  let ch0 : Choices := [3, 1, 0, 0]
  let mut s := σ0
  let mut c := c0
  let mut ch := ch0
  let mut i : Nat := 0
  let mut done := false
  let mut chLen := ch0.length
  while i < 20000 && !done do
    -- log interface-fid drained calls (dispatch sites)
    match c with
    | .retV _ (.callArgsK fid _ _ [] _ _) =>
        if fid.key == "raft.Storage.LastIndex" || fid.key == "raft.Logger.Infof" then
          IO.println s!"step {i}: DISPATCH site {fid.key}"
    | .next .stop => done := true
    | _ => pure ()
    unless done do
      match stepFn s c ch with
      | .ok (c', s', ch') =>
          if ch'.length != chLen then
            IO.println s!"step {i}: CHOICE consumed (left {ch'.length})"
            chLen := ch'.length
          c := c'; s := s'; ch := ch'; i := i + 1
      | .error e =>
          IO.println s!"ERROR at step {i}: {repr e}"
          match c with
          | .exec st _ _ => IO.println s!"  at exec {((repr st).pretty 80).replace "\n" " "}"
          | .evalE e2 _ _ => IO.println s!"  at evalE {((repr e2).pretty 80).replace "\n" " "}"
          | .retV _ _ => IO.println "  at retV"
          | .next _ => IO.println "  at next"
          | _ => IO.println "  at other"
          return
  if done then
    IO.println s!"COMPLETED: .next .stop at step {i}; choices left {ch.length} (consumed {ch0.length - ch.length})"
    IO.println s!"projection pre  = {repr (absRaftNode σ0 ⟨0⟩)}"
    IO.println s!"projection post = {repr (absRaftNode s ⟨0⟩)}"
    IO.println s!"spec            = {repr ((absRaftNode σ0 ⟨0⟩).map (fun n => specBecomeFollower n 0 4))}"
    IO.println s!"nextAddr {σ0.nextAddr} -> {s.nextAddr}"
  else
    IO.println s!"NOT DONE after {i} steps"

/-! ## Phase 2: the mirror walk with hand-crossings.
Symbolic fixture: vars 1=Vote 2=lead 3=state 4=leadTransferee 9=leadArg;
picks land as 5 (Intn), 6,7,8 (Visit keys). Crossings mirror the
machine's step effects exactly (pick / range-stop / sort / dispatch). -/

def symRaft : SymValue :=
  setSymField (setSymField (setSymField (setSymField
    (embedGo (fxRaftVal 0 0 0 0))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "state" (.int (.var 3) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def fxSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (fxHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy symRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def fxS₀ : SymState := { heap := fxSymHeap, nextAddr := 21 }

def fxC₀ : SymConfig :=
  .retV (.int (.var 9) .uint64)
    (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
      [.addr (.base ⟨0⟩), .int (.lit 0) .uint64] [] [] .stop)

def fxTB : SymTables := bfTB

/-- Crossing 1: a map-range pick with the key entering as var `v`. -/
def crossPick (v : Nat) (S : SymState) (C : SymConfig) (kind : IntKind) :
    Option (SymState × SymConfig) :=
  match C with
  | .next (.mapIterK ko vo kt vt body base produced start env k) =>
      let keyv : SymValue := .int (.var v) kind
      let (loc, S') := S.alloc keyv (some kt)
      some (S', .exec body ((env.pushScope).declare (ko.getD "?") loc)
        (.mapIterK ko vo kt vt body base (produced.push keyv) start env k))
  | _ => none

/-- Crossing 2: the range-STOP step (empty candidates): state unchanged. -/
def crossStop (S : SymState) (C : SymConfig) : Option (SymState × SymConfig) :=
  match C with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => some (S, .next k)
  | _ => none

/-- Crossing 3: the sortSlice apply — the COLLAPSE: elements 0..2 of the
backing array become the sorted concrete keys [1,2,3]. -/
def crossSort (S : SymState) (C : SymConfig) : Option (SymState × SymConfig) :=
  match C with
  | .retV (.slice sv) (.stmtOpK (.sortSlice _) _ _ [] _ k) =>
      match sv.base with
      | some l =>
          match S.heap.lookup l with
          | some (.mk dty (.array vs)) =>
              let sorted := (vs.set! 0 (.int (.lit 1) .uint64)
                |>.set! 1 (.int (.lit 2) .uint64)
                |>.set! 2 (.int (.lit 3) .uint64))
              some ({ S with heap := GoLean.Sym.Heap.set S.heap l (.mk dty (.array sorted)) },
                .next k)
          | _ => none
      | none => none
  | _ => none

/-- Crossing 4: interface dispatch — enterFrameT at the RESOLVED fid
with the unwrapped receiver, frame cont built as the machine builds it. -/
def crossDispatch (S : SymState) (C : SymConfig) : Option (SymState × SymConfig) :=
  match C with
  | .retV v (.callArgsK fid plans vals [] env k) =>
      let resolved : Option (FuncId × SymValue) :=
        if fid.key == "raft.Storage.LastIndex" then
          match vals ++ [v] with
          | [.interface _ inner] => some (⟨"raft.MemoryStorage.LastIndex"⟩, inner)
          | _ => none
        else if fid.key == "raft.Logger.Infof" then
          match vals ++ [v] with
          | (.interface _ inner) :: _ => some (⟨"main.harnessLogger.Infof"⟩, inner)
          | _ => none
        else none
      match resolved with
      | some (rfid, recv) =>
          let args := recv :: (vals ++ [v]).tail
          match enterFrameT (D := symDom) fxTB S rfid args with
          | .ok (func, frameEnv, resultLocs, S') =>
              some (S', .exec func.body frameEnv
                (.frame plans env resultLocs [] k func.wrapper))
          | .error _ => none
      | none => none
  | _ => none

def describeC : SymConfig → String
  | .exec st _ _ => s!"exec {((repr st).pretty 70).replace "\n" " "}"
  | .evalE e _ _ => s!"evalE {((repr e).pretty 70).replace "\n" " "}"
  | .retV _ (.callArgsK fid _ _ p _ _) => s!"retV callArgsK {fid.key} pending={p.length}"
  | .retV _ (.stmtOpK op _ _ _ _ _) => s!"retV stmtOpK {((repr op).pretty 40).replace "\n" " "}"
  | .retV _ (.deferArgsK ..) => "retV deferArgsK"
  | .retV _ (.strictK op _ _ _ _) => s!"retV strictK {((repr op).pretty 40).replace "\n" " "}"
  | .retV _ (.callValArgsK ..) => "retV callValArgsK"
  | .retV _ (.syncStK ..) => "retV syncStK"
  | .retV _ _ => "retV other"
  | .next (.mapIterK ..) => "next mapIterK"
  | .next _ => "next other"
  | _ => "other"

def mainWalk : IO Unit := do
  let mut S := fxS₀
  let mut C := fxC₀
  let mut total : Nat := 0
  let mut windows : List Nat := []
  let mut crossings : List String := []
  let mut pickVar : Nat := 5
  let mut sortSeen := false
  for _ in [0:40] do
    if let .next .stop := C then break
    let (n, S1, C1) := symEvalWindowTB fxTB 4000 S C
    windows := windows ++ [n]
    total := total + n
    S := S1; C := C1
    if let .next .stop := C then break
    -- decide the crossing from the quit config
    let cross :=
      match C with
      | .next (.mapIterK _ _ _ _ _ _ produced _ _ _) =>
          if produced.size == 3 && sortSeen == false && pickVar > 8 then
            (crossStop S C, "stop")
          else if pickVar == 5 || produced.size < 3 then
            -- Intn pick (var 5) or Visit picks (6,7,8)
            (crossPick pickVar S C (if pickVar == 5 then .int else .uint64), s!"pick x{pickVar}")
          else (crossStop S C, "stop")
      | .retV _ (.stmtOpK (.sortSlice _) _ _ [] _ _) => (crossSort S C, "sort")
      | .retV _ (.callArgsK _ _ _ [] _ _) => (crossDispatch S C, "dispatch")
      | _ => (none, "?")
    match cross with
    | (some (S2, C2), tag) =>
        crossings := crossings ++ [tag]
        if tag == s!"pick x{pickVar}" then pickVar := pickVar + 1
        if tag == "sort" then sortSeen := true
        total := total + 1
        S := S2; C := C2
    | (none, tag) =>
        IO.println s!"STUCK after {total} steps (windows {windows}) wanted {tag} at: {describeC C}"
        match stepFnSTB fxTB S C with
        | .error q => IO.println s!"  quit: {repr q}"
        | .ok _ => IO.println "  (steps fine?)"
        return
  IO.println s!"mirror total steps: {total}"
  IO.println s!"windows: {windows}"
  IO.println s!"crossings: {crossings}"
  match C with
  | .next .stop =>
      -- end-to-end γ check against the machine's phase-1 run
      let ρfin : Valuation :=
        { ints := fun i => [0, 7, 2, 1, 5, 3, 2, 1, 3, 4].getD i 0
          bools := fun _ => false, vals := fun _ => .nil
          cells := fun _ => ⟨none, .nil⟩ }
      let σ0 := fxσ 7 2 1 5
      let mut ms := σ0
      let mut mc := fxC 4
      let mut mch : Choices := [3, 1, 0, 0]
      for _ in [0:3234] do
        match stepFn ms mc mch with
        | .ok (c', s', ch') => mc := c'; ms := s'; mch := ch'
        | .error _ => pure ()
      let img := γS ρfin σ0 S
      IO.println s!"γ-image heap == machine heap: {img.heap == ms.heap}"
      IO.println s!"nextAddr: γ {img.nextAddr} vs machine {ms.nextAddr}"
      IO.println s!"machine final config is stop: {match mc with | .next .stop => true | _ => false}"
      if img.heap != ms.heap then
        for ((l1, c1), (l2, c2)) in img.heap.zip ms.heap do
          if l1 != l2 || c1 != c2 then
            IO.println s!"first diff at {(repr l1).pretty 40}/{(repr l2).pretty 40}"
            IO.println s!"  γ: {((repr c1).pretty 200).replace "\n" " "}"
            IO.println s!"  m: {((repr c2).pretty 200).replace "\n" " "}"
            break
  | _ => IO.println s!"final config not stop: {describeC C}"

/-! ## Component dump for the 4 pick sites + stop + sort (BfEquation's
literal fields; body/env/k stay projection-defs). -/
def ρm : Valuation :=
  { ints := fun i => 1000 + i
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }
def main : IO Unit := do
  let mut S := fxS₀
  let mut C := fxC₀
  let mut pickVar : Nat := 5
  let mut sortSeen := false
  let mut site : Nat := 0
  for _ in [0:40] do
    if let .next .stop := C then break
    let (n, S1, C1) := symEvalWindowTB fxTB 4000 S C
    S := S1; C := C1
    if let .next .stop := C then break
    site := site + 1
    match C with
    | .next (.mapIterK ko vo kt vt _ base produced start env _) =>
        IO.println s!"=== SITE {site} (window {n}) mapIterK"
        IO.println s!"ko={repr ko} vo={repr vo}"
        IO.println s!"kt={(repr kt).pretty 1000} vt={(repr vt).pretty 1000}"
        IO.println s!"base={(repr base).pretty 1000}"
        IO.println s!"producedγ(var i ↦ 1000+i)={(repr (produced.map (concV (symInterp ρm)))).pretty 100000}"
        IO.println s!"startγ={(repr (start.map (concV (symInterp ρm)))).pretty 100000}"
        IO.println s!"env scopes names={env.map (fun sc => sc.map (fun p => p.1))}"
    | .retV v (.stmtOpK op nt done pending _ _) =>
        IO.println s!"=== SITE {site} (window {n}) stmtOpK {(repr op).pretty 200}"
        IO.println s!"retvγ={(repr (concV (symInterp ρm) v)).pretty 2000}"
        IO.println s!"nt={repr nt} doneγ={(repr (done.map (concV (symInterp ρm)))).pretty 2000} pending={pending.length}"
    | _ => IO.println s!"=== SITE {site} (window {n}) other"
    -- cross
    let cross :=
      match C with
      | .next (.mapIterK _ _ _ _ _ _ produced _ _ _) =>
          if produced.size == 3 && sortSeen == false && pickVar > 8 then
            (crossStop S C, "stop")
          else if pickVar == 5 || produced.size < 3 then
            (crossPick pickVar S C (if pickVar == 5 then .int else .uint64), s!"pick x{pickVar}")
          else (crossStop S C, "stop")
      | .retV _ (.stmtOpK (.sortSlice _) _ _ [] _ _) => (crossSort S C, "sort")
      | .retV _ (.callArgsK _ _ _ [] _ _) => (crossDispatch S C, "dispatch")
      | _ => (none, "?")
    match cross with
    | (some (S2, C2), tag) =>
        if tag == s!"pick x{pickVar}" then pickVar := pickVar + 1
        if tag == "sort" then sortSeen := true
        S := S2; C := C2
    | (none, _) => return
