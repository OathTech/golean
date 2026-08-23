import GoLeanProofs.Specs.Raft.HandlerEqSym

/-!
# A4-U3: the POPULATED becomeFollower fixture and its 12-window chain

The populated-tracker fixture (checklist item 1) — recipe = the A4-U1
instrumentation probe's cell dump (`artifacts/probe/probe2.out`, arc
log 2026-08-22), re-addressed small: 21 cells covering the raft cell
with a populated `trk` (Progress mapData + three `tracker.Progress`
cells + their Inflights), the `raftLog → MemoryStorage` chain with a
1-entry plainpb ents array, readOnly/acks, the harness logger, the
static `globalRand` chain at its pinned addresses 18/19, and
`r.id = 1` (the real trace's value — it makes the closure's
`id == r.id` Match branch real, so `Storage.LastIndex` dispatches 4×,
not the dispatch note's 3×; census correction in the arc log).

Symbolic scalars (design §4(ii) + §5: value-symbolic,
address-concrete): `x₁`=Vote, `x₂`=lead, `x₃`=state,
`x₄`=leadTransferee, `x₉`=the lead ARGUMENT; the four picked keys
enter as `x₅` (Intn, kind int) and `x₆ x₇ x₈` (Visit, kind uint64) —
the valuation absorbs every pick. `Term` is CONCRETE 0 (= the term
argument), so reset's term-equal branch is decided; the term-change
branch is a recorded U3 residual, not attempted.

**Probe provenance (the #eval-before-rfl rule):** every number below
was machine-checked first by `artifacts/probe/BfU3Probe.lean`:
phase 1 (machine, concrete valuation) runs the drained call
end-to-end in 3,234 steps consuming exactly 4 choices and lands
`absRaftNode post = specBecomeFollower n 0 leadArg`; phase 2 (mirror)
reproduces it as the 12 windows below + 11 hand crossings, and the
γ-image of the final mirror state EQUALS the machine's final heap
(nextAddr 188 both). The window-count theorems at the bottom are the
transcription re-check: a drifted fixture fails them loudly.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
open GoLean.Examples.RaftTwin (twinLowered)

/-! ## The concrete cell values (probe2's shapes) -/

def uEmptySlice : GoValue := .slice { base := none, offset := 0, len := 0, cap := 0 }
def uU64 (n : Int) : GoValue := .int n .uint64
def uI64 (n : Int) : GoValue := .int n .int
def uLoggerIface : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨5⟩))

/-- The raft cell (32 fields, probe2's order), the four
later-symbolic scalars as parameters. -/
def uRaftVal (vote lead state ldT : Int) : GoValue :=
  .struct ⟨"raft.raft"⟩ #[
    ("id", uU64 1), ("Term", uU64 0), ("Vote", uU64 vote),
    ("readStates", uEmptySlice), ("raftLog", .addr (.base ⟨1⟩)),
    ("maxMsgSize", uU64 1048576), ("maxUncommittedSize", uU64 18446744073709551615),
    ("trk", .struct ⟨"tracker.ProgressTracker"⟩ #[
      ("Config", .struct ⟨"tracker.Config"⟩ #[
        ("Voters", .array #[.map { base := some (.base ⟨14⟩) }, .map { base := none }]),
        ("AutoLeave", .bool false), ("Learners", .map { base := none }),
        ("LearnersNext", .map { base := none })]),
      ("Progress", .map { base := some (.base ⟨2⟩) }),
      ("Votes", .map { base := some (.base ⟨3⟩) }),
      ("MaxInflight", uI64 256), ("MaxInflightBytes", uU64 18446744073709551615)]),
    ("state", uU64 state), ("isLearner", .bool false),
    ("msgs", uEmptySlice), ("msgsAfterAppend", uEmptySlice),
    ("lead", uU64 lead), ("leadTransferee", uU64 ldT),
    ("pendingConfIndex", uU64 0), ("disableConfChangeValidation", .bool false),
    ("uncommittedSize", uU64 0), ("readOnly", .addr (.base ⟨4⟩)),
    ("electionElapsed", uI64 0), ("heartbeatElapsed", uI64 0),
    ("checkQuorum", .bool false), ("preVote", .bool false),
    ("heartbeatTimeout", uI64 1), ("electionTimeout", uI64 10),
    ("randomizedElectionTimeout", uI64 0),
    ("disableProposalForwarding", .bool false), ("stepDownOnRemoval", .bool false),
    ("tick", .nil), ("step", .nil), ("logger", uLoggerIface),
    ("pendingReadIndexMessages", uEmptySlice), ("traceLogger", .nil)]

def uLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨6⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", uEmptySlice), ("offset", uU64 2),
      ("snapshotInProgress", .bool false), ("offsetInProgress", uU64 2),
      ("logger", uLoggerIface)]),
    ("committed", uU64 1), ("applying", uU64 1), ("applied", uU64 1),
    ("logger", uLoggerIface), ("maxApplyingEntsSize", uU64 1048576),
    ("applyingEntsSize", uU64 0), ("applyingEntsPaused", .bool false)]

def uMsVal : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨15⟩), offset := 0, len := 1, cap := 1 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", uI64 0), ("firstIndex", uI64 0), ("lastIndex", uI64 0),
      ("entries", uI64 0), ("term", uI64 0), ("snapshot", uI64 0)])]

def uProgressVal (infl : Nat) : GoValue :=
  .struct ⟨"tracker.Progress"⟩ #[
    ("Match", uU64 0), ("Next", uU64 1), ("sentCommit", uU64 0),
    ("State", uU64 0), ("PendingSnapshot", uU64 0), ("RecentActive", .bool true),
    ("MsgAppFlowPaused", .bool false), ("Inflights", .addr (.base ⟨infl⟩)),
    ("IsLearner", .bool false)]

def uInflightsVal : GoValue :=
  .struct ⟨"tracker.Inflights"⟩ #[
    ("start", uI64 0), ("count", uI64 0), ("bytes", uU64 0),
    ("size", uI64 256), ("maxBytes", uU64 18446744073709551615),
    ("buffer", uEmptySlice)]

def uReadOnlyVal : GoValue :=
  .struct ⟨"raft.readOnly"⟩ #[
    ("option", uI64 0), ("acks", .map { base := some (.base ⟨13⟩) }),
    ("unconfirmedReads", uEmptySlice), ("confirmedReads", uU64 0)]

def uEntryVal : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨17⟩)), ("Index", .addr (.base ⟨20⟩)),
    ("Type", .nil), ("Data", uEmptySlice)]

def uStEmpty : GoValue := .struct ⟨"struct{}"⟩ #[]

/-- The concrete fixture heap (phase-1 probe's `fxHeap`). -/
def uHeap (vote lead state ldT : Int) : GoCore.Heap :=
  [(.base ⟨0⟩, ⟨some (.defined ⟨"raft.raft"⟩), uRaftVal vote lead state ldT⟩),
   (.base ⟨1⟩, ⟨some (.defined ⟨"raft.raftLog"⟩), uLogVal⟩),
   (.base ⟨2⟩, ⟨none, .mapData #[(uU64 1, .addr (.base ⟨7⟩)), (uU64 2, .addr (.base ⟨8⟩)), (uU64 3, .addr (.base ⟨9⟩))]⟩),
   (.base ⟨3⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨4⟩, ⟨some (.defined ⟨"raft.readOnly"⟩), uReadOnlyVal⟩),
   (.base ⟨5⟩, ⟨some (.defined ⟨"main.harnessLogger"⟩), .struct ⟨"main.harnessLogger"⟩ #[]⟩),
   (.base ⟨6⟩, ⟨some (.defined ⟨"raft.MemoryStorage"⟩), uMsVal⟩),
   (.base ⟨7⟩, ⟨some (.defined ⟨"tracker.Progress"⟩), uProgressVal 10⟩),
   (.base ⟨8⟩, ⟨some (.defined ⟨"tracker.Progress"⟩), uProgressVal 11⟩),
   (.base ⟨9⟩, ⟨some (.defined ⟨"tracker.Progress"⟩), uProgressVal 12⟩),
   (.base ⟨10⟩, ⟨some (.defined ⟨"tracker.Inflights"⟩), uInflightsVal⟩),
   (.base ⟨11⟩, ⟨some (.defined ⟨"tracker.Inflights"⟩), uInflightsVal⟩),
   (.base ⟨12⟩, ⟨some (.defined ⟨"tracker.Inflights"⟩), uInflightsVal⟩),
   (.base ⟨13⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨14⟩, ⟨none, .mapData #[(uU64 1, uStEmpty), (uU64 2, uStEmpty), (uU64 3, uStEmpty)]⟩),
   (.base ⟨15⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))), .array #[.addr (.base ⟨16⟩)]⟩),
   (.base ⟨16⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), uEntryVal⟩),
   (.base ⟨17⟩, ⟨some (.int .uint64), uU64 1⟩),
   (.base ⟨18⟩, ⟨some (.pointer (.defined ⟨"raft.lockedRand"⟩)), .addr (.base ⟨19⟩)⟩),
   (.base ⟨19⟩, ⟨some (.defined ⟨"raft.lockedRand"⟩),
      .struct ⟨"raft.lockedRand"⟩ #[("mu", .syncData (.mutex false))]⟩),
   (.base ⟨20⟩, ⟨some (.int .uint64), uU64 1⟩)]

/-- The concrete machine pre-state at scalar values (the witness
family instantiates here). -/
def uσ (vote lead state ldT : Int) : ExecState :=
  { wBase with heap := uHeap vote lead state ldT, nextAddr := 21 }

/-! ## The symbolic fixture -/

/-- The raft cell with the four scalars symbolic. -/
def uSymRaft : SymValue :=
  setSymField (setSymField (setSymField (setSymField
    (embedGo (uRaftVal 0 0 0 0))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "state" (.int (.var 3) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def uSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy uSymRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def uS0 : SymState := { heap := uSymHeap, nextAddr := 21 }

/-- The drained call configuration of `becomeFollower(0, x₉)`. -/
def uC0 : SymConfig :=
  .retV (.int (.var 9) .uint64)
    (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
      [.addr (.base ⟨0⟩), .int (.lit 0) .uint64] [] [] .stop)

/-! ## The crossing constructions (mirroring the machine's step
effects exactly; fail closed on any shape drift) -/

/-- A map-range pick with the key entering as var `v` (the valuation
absorbs the pick; design §4(ii)). Mirrors `bindIterVars` +
`produced.push` for a key-only binder. -/
def uCrossPick (v : Nat) (kind : IntKind) (S : SymState) (C : SymConfig) :
    SymState × SymConfig :=
  match C with
  | .next (.mapIterK ko vo kt vt body base produced start env k) =>
      let keyv : SymValue := .int (.var v) kind
      let (loc, S') := S.alloc keyv (some kt)
      (S', .exec body ((env.pushScope).declare (ko.getD "?") loc)
        (.mapIterK ko vo kt vt body base (produced.push keyv) start env k))
  | _ => (S, .panicked "uCrossPick: shape drift")

/-- The range-STOP step (candidates exhausted): state unchanged. -/
def uCrossStop (S : SymState) (C : SymConfig) : SymState × SymConfig :=
  match C with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => (S, .next k)
  | _ => (S, .panicked "uCrossStop: shape drift")

/-- The sortSlice apply — THE COLLAPSE (design §4(ii)): elements 0..2
of the ids backing array become the sorted concrete keys [1,2,3],
identically for every pick order; the dead key cells stay symbolic. -/
def uCrossSort (S : SymState) (C : SymConfig) : SymState × SymConfig :=
  match C with
  | .retV (.slice sv) (.stmtOpK (.sortSlice _) _ _ [] _ k) =>
      match sv.base with
      | some l =>
          match GoLean.Sym.Heap.lookup S.heap l with
          | some (.mk dty (.array vs)) =>
              let sorted := ((vs.set! 0 (.int (.lit 1) .uint64)).set! 1
                (.int (.lit 2) .uint64)).set! 2 (.int (.lit 3) .uint64)
              ({ S with heap := GoLean.Sym.Heap.set S.heap l (.mk dty (.array sorted)) },
                .next k)
          | _ => (S, .panicked "uCrossSort: no backing array")
      | none => (S, .panicked "uCrossSort: nil base")
  | _ => (S, .panicked "uCrossSort: shape drift")

/-! ## The chain: 7 windows, 6 crossings (probe-validated counts;
interface dispatch crosses IN-window since the class-2b completion —
the five former dispatch splits merged into the final window) -/

def uP1 : SymState × SymConfig := ((symEvalWindowTB bfTB 642 uS0 uC0).2.1, (symEvalWindowTB bfTB 642 uS0 uC0).2.2)
def uS1 : SymState := uP1.1
def uC1 : SymConfig := uP1.2
def uP2 : SymState × SymConfig := uCrossPick 5 .int uS1 uC1
def uS2 : SymState := uP2.1
def uC2 : SymConfig := uP2.2
def uP3 : SymState × SymConfig := ((symEvalWindowTB bfTB 183 uS2 uC2).2.1, (symEvalWindowTB bfTB 183 uS2 uC2).2.2)
def uS3 : SymState := uP3.1
def uC3 : SymConfig := uP3.2
def uP4 : SymState × SymConfig := uCrossPick 6 .uint64 uS3 uC3
def uS4 : SymState := uP4.1
def uC4 : SymConfig := uP4.2
def uP5 : SymState × SymConfig := ((symEvalWindowTB bfTB 28 uS4 uC4).2.1, (symEvalWindowTB bfTB 28 uS4 uC4).2.2)
def uS5 : SymState := uP5.1
def uC5 : SymConfig := uP5.2
def uP6 : SymState × SymConfig := uCrossPick 7 .uint64 uS5 uC5
def uS6 : SymState := uP6.1
def uC6 : SymConfig := uP6.2
def uP7 : SymState × SymConfig := ((symEvalWindowTB bfTB 28 uS6 uC6).2.1, (symEvalWindowTB bfTB 28 uS6 uC6).2.2)
def uS7 : SymState := uP7.1
def uC7 : SymConfig := uP7.2
def uP8 : SymState × SymConfig := uCrossPick 8 .uint64 uS7 uC7
def uS8 : SymState := uP8.1
def uC8 : SymConfig := uP8.2
def uP9 : SymState × SymConfig := ((symEvalWindowTB bfTB 28 uS8 uC8).2.1, (symEvalWindowTB bfTB 28 uS8 uC8).2.2)
def uS9 : SymState := uP9.1
def uC9 : SymConfig := uP9.2
def uP10 : SymState × SymConfig := uCrossStop uS9 uC9
def uS10 : SymState := uP10.1
def uC10 : SymConfig := uP10.2
def uP11 : SymState × SymConfig := ((symEvalWindowTB bfTB 3 uS10 uC10).2.1, (symEvalWindowTB bfTB 3 uS10 uC10).2.2)
def uS11 : SymState := uP11.1
def uC11 : SymConfig := uP11.2
def uP12 : SymState × SymConfig := uCrossSort uS11 uC11
def uS12 : SymState := uP12.1
def uC12 : SymConfig := uP12.2
def uP13 : SymState × SymConfig := ((symEvalWindowTB bfTB 2316 uS12 uC12).2.1, (symEvalWindowTB bfTB 2316 uS12 uC12).2.2)
def uS13 : SymState := uP13.1
def uC13 : SymConfig := uP13.2

set_option maxRecDepth 4000000
set_option maxHeartbeats 16000000
set_option smartUnfolding false

/-! ## The window-count theorems (each `#eval`-checked by the probe
before elaboration; a fixture-transcription drift fails here). -/

theorem uW1_n : (symEvalWindowTB bfTB 642 uS0 uC0).1 = 642 := by
  with_unfolding_all rfl
theorem uW2_n : (symEvalWindowTB bfTB 183 uS2 uC2).1 = 183 := by
  with_unfolding_all rfl
theorem uW3_n : (symEvalWindowTB bfTB 28 uS4 uC4).1 = 28 := by
  with_unfolding_all rfl
theorem uW4_n : (symEvalWindowTB bfTB 28 uS6 uC6).1 = 28 := by
  with_unfolding_all rfl
theorem uW5_n : (symEvalWindowTB bfTB 28 uS8 uC8).1 = 28 := by
  with_unfolding_all rfl
theorem uW6_n : (symEvalWindowTB bfTB 3 uS10 uC10).1 = 3 := by
  with_unfolding_all rfl
theorem uW7_n : (symEvalWindowTB bfTB 2316 uS12 uC12).1 = 2316 := by
  with_unfolding_all rfl

/-- The chain lands at the function's return: `.next .stop`. -/
theorem uC13_stop : uC13 = .next .stop := by
  with_unfolding_all rfl

end GoLean.RaftSeam
