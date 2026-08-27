import GoLeanProofs.Specs.RaftPilot.SymBase
import GoLeanProofs.SpecJudgment
import GoLeanProofs.Sym.KernelRfl
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# W3 U3.1-A — the INIT CLUSTER CallSpecs (Wave A: the zero-draw members)

The init-cluster partition unit (charter Amendment 1: census §2.5, §0,
E1-E4; consumed by U3.2f — init stage B). This module holds the
LANDED Wave-A members: the init-chain functions whose spans consume
NO choices (no map ranges, no reallocating appends — the draw census
in `docs/w3-init-log.md`). The pick-bearing members (the confchange
Restore/Simple chain's clone/invariant walks, switchToConfig,
becomeFollower-at-init, newRaft, NewRawNode) are PARKED with records
in the same log — park-not-weaken; nothing here narrows a conclusion.

**QUANTIFIER AUDIT (the charter's opening requirement):** each
CallSpec/CallSpecR/CallSpecRN here is a RULE discharging ∀-state at
its call site inside `newTwin` (∀ σ over the member's footprint
family; ∀ plans/env/k — target- and continuation-parametric; ∀ ch
demonic; ∃ n) — consumed by U3.2f via `.consume`. No end-theorem
quantifier closes here.

**The pattern** (the U3.1-F recipe): canonical placement — footprint
cells from `.base ⟨31⟩` up (the W2 layout-compliance rule), EXCEPT
`raft.SetLogger`, whose footprint is the TRUE static cells
`raftLoggerMu ⟨13⟩` / `raftLogger ⟨14⟩` (globals live in the forced-
identity region, so the true placement IS the canonical one). The
init cluster runs at CONCRETE reflected shapes (the harness config
literal, twin-lib.go:207-215, is reflected-program text — the
charter's sanctioned carve-out), so read positions are pinned to the
harness values and genuinely-unread positions ride as free
parameters. Whole spans close by `kernel_rfl` at OPEN
`plans`/`env`/`k`/`ch` — the open `ch` is the ZERO-DRAW CERTIFICATE:
reduction would be stuck on any consultation of the stream.

**Statement hygiene:** step counts appear only in the PRIVATE span
lemmas (proof-body scaffolding, the W1 convention); the exports are
count-free (∃ n). Addresses 31+ are canonical-placement constants;
the field censuses are the pinned wire's typeDefs.

**Parked axes, labeled at birth (records in docs/w3-init-log.md):**
* `ApplySnapshot`'s snap-argument Voters slice is pinned at the
  slot-0-realized backing (cap 4, `[1,2,3,0]`): the harness builds
  that slice by three reallocating appends whose capacities are
  DRAWN, so the ∀-cap family needs the data-branch crossing kit
  (symbolic-cap `validateSlice`). Precondition narrowed and labeled;
  no conclusion weakened.
* `Config.validate` is stated ∀ id over the harness's id set
  {1,2,3} (a case analysis over a reflected-program-text constant
  set — `newTwin(3,2)`'s loop bounds — not a subject-run census).

LINEAGE: Hoare procedure specs by computational reflection (the
W1/U3.1-F route); `CallSpecRN` is the same rule at the machine's
nullary entry shape. No new mechanism class.
-/

namespace GoLean.RaftSeam.InitA

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Spec
open GoLean.Surface (stepFnIter_chain stepFnIter_one)
open GoLean.RaftSeam (wBase)

set_option maxRecDepth 8000000
set_option maxHeartbeats 256000000
set_option smartUnfolding false

/-! ## Shared value formers (field censuses from the pinned wire's
typeDefs; values from the harness literals) -/

def u64v (n : Int) : GoValue := .int n .uint64
def intv (n : Int) : GoValue := .int n .int
def nilSlice : GoValue := .slice ⟨none, 0, 0, 0⟩

/-! ## `raft.SetLogger` (census E1; harness `installLogger`,
twin-lib.go:130) — TRUE static footprint -/

/-- The SetLogger footprint: the two logger globals at their TRUE
static addresses (`raftLoggerMu` ⟨13⟩ unlocked, `raftLogger` ⟨14⟩
holding ANY prior logger value `w` — overwritten unread). -/
def SLPre (w : GoValue) (σm : ExecState) : Prop :=
  σm = { wBase with
          heap := [(Loc.base ⟨13⟩,
                     { declaredTy := some (.sync .mutex)
                       value := .syncData (.mutex false) }),
                   (Loc.base ⟨14⟩,
                     { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                       value := w })]
          nextAddr := 31 }

/-- The SetLogger span (PRIVATE count-bearing scaffolding — 25
machine steps, zero choices, open `env`/`k`/`ch`): frame entry (the
`l` param cell at ⟨31⟩), `raftLoggerMu.Lock()`, the `raftLogger`
global store, `Unlock()`, frame exit to `.next k`. The argument is
pinned to the interface SHAPE (`.interface tL pv` — the store-time
interface check inspects the constructor) with the dynamic type and
payload free. -/
private theorem sl_span (w : GoValue) (tL : Ty) (pv : GoValue)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFnIter 25
      { wBase with
          heap := [(Loc.base ⟨13⟩,
                     { declaredTy := some (.sync .mutex)
                       value := .syncData (.mutex false) }),
                   (Loc.base ⟨14⟩,
                     { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                       value := w })]
          nextAddr := 31 }
      (.retV (.interface tL pv)
        (.callArgsK ⟨"raft.SetLogger"⟩ [] [] [] env k)) ch
      = .ok (.next k,
          { wBase with
              heap := [(Loc.base ⟨13⟩,
                         { declaredTy := some (.sync .mutex)
                           value := .syncData (.mutex false) }),
                       (Loc.base ⟨14⟩,
                         { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                           value := .interface tL pv }),
                       (Loc.base ⟨31⟩,
                         { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                           value := .interface tL pv })]
              nextAddr := 32 }, ch) := by
  kernel_rfl

/-- **THE `SetLogger` CallSpec** (resultless): at the true static
footprint, installing any interface-shaped logger stores it into
`raftLogger` ⟨14⟩ and leaves the mutex unlocked. ∀-state over the
family (prior logger value free), ∀ env/k, ∀ ch, ∃ n; count-free.
Serves U3.2f's `installLogger` prefix: post-state fact
`raftLogger = the installed logger`. -/
theorem setLogger_callSpec (w : GoValue) (tL : Ty) (pv : GoValue) :
    CallSpec (SLPre w) ⟨"raft.SetLogger"⟩ [] (.interface tL pv)
      (fun σ' =>
        Heap.lookup σ'.heap (Loc.base ⟨14⟩)
          = some { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                   value := .interface tL pv } ∧
        Heap.lookup σ'.heap (Loc.base ⟨13⟩)
          = some { declaredTy := some (.sync .mutex)
                   value := .syncData (.mutex false) }) := by
  intro σ hP env k ch
  refine ⟨25,
    { wBase with
        heap := [(Loc.base ⟨13⟩,
                   { declaredTy := some (.sync .mutex)
                     value := .syncData (.mutex false) }),
                 (Loc.base ⟨14⟩,
                   { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                     value := .interface tL pv }),
                 (Loc.base ⟨31⟩,
                   { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                     value := .interface tL pv })]
        nextAddr := 32 },
    ch, ?_, ⟨?_, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]; exact sl_span w tL pv env k ch
  · rfl
  · rfl

/-- Non-vacuity: the family's ∃-discharge at the machine's own
default-logger value (the real pre-`installLogger` static). -/
theorem slPre_inhabited :
    SLPre (.interface (.pointer (.defined ⟨"raft.DefaultLogger"⟩))
            (.addr (.base ⟨53⟩)))
      { wBase with
          heap := [(Loc.base ⟨13⟩,
                     { declaredTy := some (.sync .mutex)
                       value := .syncData (.mutex false) }),
                   (Loc.base ⟨14⟩,
                     { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                       value := .interface
                         (.pointer (.defined ⟨"raft.DefaultLogger"⟩))
                         (.addr (.base ⟨53⟩)) })]
          nextAddr := 31 } := rfl

/-! ## `raft.Config.validate` (census §0/§2.2; called by `newRaft`
at the harness config literal, twin-lib.go:207-215) -/

/-- The harness config value at voter id `idv` (field census/order
from the pinned wire's `raft.Config` typeDef; values from the
reflected literal; the two interface payloads `lS`/`lL` free — the
span nil-checks the interfaces without dereferencing them). -/
def cfgV (idv : Int) (lS lL : Loc) : GoValue :=
  .struct ⟨"raft.Config"⟩
    #[("ID", u64v idv), ("ElectionTick", intv 10), ("HeartbeatTick", intv 1),
      ("Storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩))
        (.addr lS)),
      ("Applied", u64v 0), ("AsyncStorageWrites", .bool false),
      ("MaxSizePerMsg", u64v 1048576), ("MaxCommittedSizePerReady", u64v 0),
      ("MaxUncommittedEntriesSize", u64v 0), ("MaxInflightMsgs", intv 256),
      ("MaxInflightBytes", u64v 0), ("CheckQuorum", .bool false),
      ("PreVote", .bool false), ("ReadOnlyOption", intv 0),
      ("Logger", .interface (.pointer (.defined ⟨"main.harnessLogger"⟩))
        (.addr lL)),
      ("DisableProposalForwarding", .bool false),
      ("DisableConfChangeValidation", .bool false),
      ("StepDownOnRemoval", .bool false), ("TraceLogger", .nil)]

/-- The DEFAULTED config value `validate` leaves behind (`noLimit`
= 2^64-1 into MaxUncommittedEntriesSize and MaxInflightBytes;
MaxSizePerMsg into MaxCommittedSizePerReady — census §0's rows). -/
def cfgV' (idv : Int) (lS lL : Loc) : GoValue :=
  .struct ⟨"raft.Config"⟩
    #[("ID", u64v idv), ("ElectionTick", intv 10), ("HeartbeatTick", intv 1),
      ("Storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩))
        (.addr lS)),
      ("Applied", u64v 0), ("AsyncStorageWrites", .bool false),
      ("MaxSizePerMsg", u64v 1048576),
      ("MaxCommittedSizePerReady", u64v 1048576),
      ("MaxUncommittedEntriesSize", u64v 18446744073709551615),
      ("MaxInflightMsgs", intv 256),
      ("MaxInflightBytes", u64v 18446744073709551615),
      ("CheckQuorum", .bool false),
      ("PreVote", .bool false), ("ReadOnlyOption", intv 0),
      ("Logger", .interface (.pointer (.defined ⟨"main.harnessLogger"⟩))
        (.addr lL)),
      ("DisableProposalForwarding", .bool false),
      ("DisableConfChangeValidation", .bool false),
      ("StepDownOnRemoval", .bool false), ("TraceLogger", .nil)]

/-- The validate footprint: the config cell alone at the canonical
anchor. -/
def VPre (idv : Int) (lS lL : Loc) (σm : ExecState) : Prop :=
  σm = { wBase with
          heap := [(Loc.base ⟨31⟩,
            { declaredTy := some (.defined ⟨"raft.Config"⟩)
              value := cfgV idv lS lL })]
          nextAddr := 32 }

/-- The validate terminal state (defaults written; the temps are the
machine's own frame cells: receiver copy, error result, two branch
temps, the `IsLocalMsgTarget` param). -/
def vPost (idv : Int) (lS lL : Loc) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
                 { declaredTy := some (.defined ⟨"raft.Config"⟩)
                   value := cfgV' idv lS lL }),
               (Loc.base ⟨32⟩,
                 { declaredTy := some (.pointer (.defined ⟨"raft.Config"⟩))
                   value := .addr (.base ⟨31⟩) }),
               (Loc.base ⟨33⟩,
                 { declaredTy := some (.interface ⟨"error"⟩)
                   value := .nil }),
               (Loc.base ⟨34⟩,
                 { declaredTy := some .bool, value := .bool false }),
               (Loc.base ⟨35⟩,
                 { declaredTy := some (.int .uint64), value := u64v idv }),
               (Loc.base ⟨36⟩,
                 { declaredTy := some .bool, value := .bool false })]
      nextAddr := 37 }

/-- The validate span at id 1 (PRIVATE count-bearing scaffolding —
242 machine steps, zero choices, open `plans`/`env`/`k`/`ch`). -/
private theorem v_span1 (lS lL : Loc)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 242
      { wBase with
          heap := [(Loc.base ⟨31⟩,
            { declaredTy := some (.defined ⟨"raft.Config"⟩)
              value := cfgV 1 lS lL })]
          nextAddr := 32 }
      (.retV (.addr (.base ⟨31⟩))
        (.callArgsK ⟨"raft.Config.validate"⟩ plans [] [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩] [] k false),
        vPost 1 lS lL, ch) := by
  kernel_rfl

private theorem v_span2 (lS lL : Loc)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 242
      { wBase with
          heap := [(Loc.base ⟨31⟩,
            { declaredTy := some (.defined ⟨"raft.Config"⟩)
              value := cfgV 2 lS lL })]
          nextAddr := 32 }
      (.retV (.addr (.base ⟨31⟩))
        (.callArgsK ⟨"raft.Config.validate"⟩ plans [] [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩] [] k false),
        vPost 2 lS lL, ch) := by
  kernel_rfl

private theorem v_span3 (lS lL : Loc)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 242
      { wBase with
          heap := [(Loc.base ⟨31⟩,
            { declaredTy := some (.defined ⟨"raft.Config"⟩)
              value := cfgV 3 lS lL })]
          nextAddr := 32 }
      (.retV (.addr (.base ⟨31⟩))
        (.callArgsK ⟨"raft.Config.validate"⟩ plans [] [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩] [] k false),
        vPost 3 lS lL, ch) := by
  kernel_rfl

/-- **THE `Config.validate` CallSpecR** at the harness ids (the id
set {1,2,3} is a reflected-program-text constant — `newTwin(3,2)`'s
loop bounds; a case analysis over that set, never a run census): the
call succeeds (`nil` error) and writes exactly the three §0 defaults
into the config cell, everything else unchanged; the terminal state
is pinned in full for the newRaft-composition consumer. -/
theorem config_validate_callSpecR (idv : Int)
    (hid : idv = 1 ∨ idv = 2 ∨ idv = 3) (lS lL : Loc) :
    CallSpecR (VPre idv lS lL) ⟨"raft.Config.validate"⟩ []
      (.addr (.base ⟨31⟩))
      (fun σ' vs =>
        vs = [.nil] ∧ σ' = vPost idv lS lL ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := some (.defined ⟨"raft.Config"⟩)
                   value := cfgV' idv lS lL }) := by
  intro σ hP plans env k ch
  refine ⟨242, vPost idv lS lL, [Loc.base ⟨33⟩], [.nil], ch, ?_, ?_,
    ⟨rfl, rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]
    rcases hid with h | h | h <;> subst h
    · exact v_span1 lS lL plans env k ch
    · exact v_span2 lS lL plans env k ch
    · exact v_span3 lS lL plans env k ch
  · rcases hid with h | h | h <;> subst h <;> rfl
  · rcases hid with h | h | h <;> subst h <;> rfl

/-- Non-vacuity: the id-1 family member is inhabited. -/
theorem vPre_inhabited :
    VPre 1 (.base ⟨100⟩) (.base ⟨101⟩)
      { wBase with
          heap := [(Loc.base ⟨31⟩,
            { declaredTy := some (.defined ⟨"raft.Config"⟩)
              value := cfgV 1 (.base ⟨100⟩) (.base ⟨101⟩) })]
          nextAddr := 32 } := rfl

/-! ## `tracker.MakeProgressTracker` (census §2.6; called by
`newRaft` at `(256, noLimit)` — the post-validate values) -/

/-- The MakeProgressTracker footprint: tables only (the function
allocates everything it touches). -/
def MPTPre (σm : ExecState) : Prop :=
  σm = { wBase with heap := [], nextAddr := 31 }

/-- The empty tracker value the call returns (three fresh empty maps
at the canonical allocation addresses; wire field order). -/
def mptV : GoValue :=
  .struct ⟨"tracker.ProgressTracker"⟩
    #[("Config",
       .struct ⟨"tracker.Config"⟩
         #[("Voters", .array #[.map ⟨some (.base ⟨35⟩)⟩, .map ⟨none⟩]),
           ("AutoLeave", .bool false), ("Learners", .map ⟨none⟩),
           ("LearnersNext", .map ⟨none⟩)]),
      ("Progress", .map ⟨some (.base ⟨37⟩)⟩),
      ("Votes", .map ⟨some (.base ⟨39⟩)⟩),
      ("MaxInflight", intv 256),
      ("MaxInflightBytes", u64v 18446744073709551615)]

/-- The MakeProgressTracker terminal state. -/
def mptPost : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
                 { declaredTy := some (.int .int), value := intv 256 }),
               (Loc.base ⟨32⟩,
                 { declaredTy := some (.int .uint64)
                   value := u64v 18446744073709551615 }),
               (Loc.base ⟨33⟩,
                 { declaredTy := some (.defined ⟨"tracker.ProgressTracker"⟩)
                   value := mptV }),
               (Loc.base ⟨34⟩,
                 { declaredTy := some (.map (.int .uint64)
                     (.defined ⟨"struct{}"⟩))
                   value := .map ⟨some (.base ⟨35⟩)⟩ }),
               (Loc.base ⟨35⟩,
                 { declaredTy := none, value := .mapData #[] }),
               (Loc.base ⟨36⟩,
                 { declaredTy := some (.map (.int .uint64)
                     (.pointer (.defined ⟨"tracker.Progress"⟩)))
                   value := .map ⟨some (.base ⟨37⟩)⟩ }),
               (Loc.base ⟨37⟩,
                 { declaredTy := none, value := .mapData #[] }),
               (Loc.base ⟨38⟩,
                 { declaredTy := some (.map (.int .uint64) .bool)
                   value := .map ⟨some (.base ⟨39⟩)⟩ }),
               (Loc.base ⟨39⟩,
                 { declaredTy := none, value := .mapData #[] }),
               (Loc.base ⟨40⟩,
                 { declaredTy := some (.defined ⟨"tracker.ProgressTracker"⟩)
                   value := mptV })]
      nextAddr := 41 }

/-- The MakeProgressTracker span (PRIVATE count-bearing scaffolding —
75 machine steps, zero choices, open `plans`/`env`/`k`/`ch`). -/
private theorem mpt_span
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 75
      { wBase with heap := [], nextAddr := 31 }
      (.retV (u64v 18446744073709551615)
        (.callArgsK ⟨"tracker.MakeProgressTracker"⟩ plans [intv 256]
          [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨33⟩] [] k false),
        mptPost, ch) := by
  kernel_rfl

/-- **THE `MakeProgressTracker` CallSpecR** at the harness arguments
`(256, noLimit)`: returns the empty tracker (empty Voters[0] map,
nil Voters[1]/Learners/LearnersNext, empty Progress and Votes maps,
the inflight limits) — the empty-configuration input
`confchange.Restore` requires. Terminal state pinned in full. -/
theorem makeProgressTracker_callSpecR :
    CallSpecR MPTPre ⟨"tracker.MakeProgressTracker"⟩ [intv 256]
      (u64v 18446744073709551615)
      (fun σ' vs =>
        vs = [mptV] ∧ σ' = mptPost ∧
        Heap.lookup σ'.heap (Loc.base ⟨35⟩)
          = some { declaredTy := none, value := .mapData #[] } ∧
        Heap.lookup σ'.heap (Loc.base ⟨37⟩)
          = some { declaredTy := none, value := .mapData #[] } ∧
        Heap.lookup σ'.heap (Loc.base ⟨39⟩)
          = some { declaredTy := none, value := .mapData #[] }) := by
  intro σ hP plans env k ch
  refine ⟨75, mptPost, [Loc.base ⟨33⟩], [mptV], ch, ?_, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, List.suffix_refl ch⟩
  rw [hP]; exact mpt_span plans env k ch

/-- Non-vacuity: the (unique) family member. -/
theorem mptPre_inhabited :
    MPTPre { wBase with heap := [], nextAddr := 31 } := rfl

/-! ## `raft.NewMemoryStorage` (census E2; harness `newTwin`,
twin-lib.go:197) — the NULLARY member (the `CallSpecRN` form's first
consumer) -/

open GoLean.Examples.RaftTwin (twinLowered) in
/-- The `NewMemoryStorage` Func from the pinned wire's table (the
lookup `enterFrame` itself performs; fail-closed default is a
never-taken dead value — a wrong table would fail every kernel span
below, loudly). -/
def nmsFunc : Func :=
  (findFunctionIn? twinLowered.funcs ⟨"raft.NewMemoryStorage"⟩).getD
    { id := ⟨"raft.NewMemoryStorage$MISSING"⟩, args := #[],
      results := #[], body := .seqn #[], wrapper := false }

/-- The NewMemoryStorage footprint: tables only. -/
def NMSPre (σm : ExecState) : Prop :=
  σm = { wBase with heap := [], nextAddr := 31 }

/-- Shared cell formers for the fresh-storage chain. -/
def freshEntryV : GoValue :=
  .struct ⟨"raftpb.Entry"⟩
    #[("Term", .nil), ("Index", .nil), ("Type", .nil),
      ("Data", nilSlice)]
def zeroCallStatsV : GoValue :=
  .struct ⟨"raft.inMemStorageCallStats"⟩
    #[("initialState", intv 0), ("firstIndex", intv 0),
      ("lastIndex", intv 0), ("entries", intv 0), ("term", intv 0),
      ("snapshot", intv 0)]
def msV (fiv liv : Int) (hv sv ev : GoValue) : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩
    #[("Mutex", .syncData (.mutex false)), ("hardState", hv),
      ("snapshot", sv), ("ents", ev),
      ("callStats",
       .struct ⟨"raft.inMemStorageCallStats"⟩
         #[("initialState", intv 0), ("firstIndex", intv fiv),
           ("lastIndex", intv liv), ("entries", intv 0),
           ("term", intv 0), ("snapshot", intv 0)])]
def csAllNilV (al : GoValue) : GoValue :=
  .struct ⟨"raftpb.ConfState"⟩
    #[("Voters", nilSlice), ("Learners", nilSlice),
      ("VotersOutgoing", nilSlice), ("LearnersNext", nilSlice),
      ("AutoLeave", al)]
def metaV (cs idx tm : GoValue) : GoValue :=
  .struct ⟨"raftpb.SnapshotMetadata"⟩
    #[("ConfState", cs), ("Index", idx), ("Term", tm)]
def snapV (mv : GoValue) : GoValue :=
  .struct ⟨"raftpb.Snapshot"⟩ #[("Data", nilSlice), ("Metadata", mv)]
def cP (a : Nat) (t : Ty) (l : Nat) : Loc × HeapCell :=
  (Loc.base ⟨a⟩, { declaredTy := some (.pointer t), value := .addr (.base ⟨l⟩) })
def tyMS : Ty := .defined ⟨"raft.MemoryStorage"⟩
def tySnap : Ty := .defined ⟨"raftpb.Snapshot"⟩
def tyMeta : Ty := .defined ⟨"raftpb.SnapshotMetadata"⟩
def tyCS : Ty := .defined ⟨"raftpb.ConfState"⟩
def tyEnt : Ty := .defined ⟨"raftpb.Entry"⟩

/-- The NewMemoryStorage terminal state (the fresh storage chain the
census §0 storage row starts from: dummy entry at (0,0)-absent
pointers, snapshot chain fully Ensure'd, everything zero). -/
def nmsPost : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
                 { declaredTy := some (.pointer tyMS)
                   value := .addr (.base ⟨37⟩) }),
               cP 32 tyEnt 33,
               (Loc.base ⟨33⟩,
                 { declaredTy := some tyEnt, value := freshEntryV }),
               (Loc.base ⟨34⟩,
                 { declaredTy := some (.slice (.pointer tyEnt))
                   value := .slice ⟨some (.base ⟨35⟩), 0, 1, 1⟩ }),
               (Loc.base ⟨35⟩,
                 { declaredTy := some (.array 1 (.pointer tyEnt))
                   value := .array #[.addr (.base ⟨33⟩)] }),
               cP 36 tyMS 37,
               (Loc.base ⟨37⟩,
                 { declaredTy := some tyMS
                   value := msV 0 0 .nil (.addr (.base ⟨43⟩))
                     (.slice ⟨some (.base ⟨35⟩), 0, 1, 1⟩) }),
               cP 38 tyMS 37,
               cP 39 tySnap 43, cP 40 tySnap 43, cP 41 tySnap 43,
               cP 42 tySnap 43,
               (Loc.base ⟨43⟩,
                 { declaredTy := some tySnap
                   value := snapV (.addr (.base ⟨48⟩)) }),
               cP 44 tyMeta 48, cP 45 tyMeta 48, cP 46 tyMeta 48,
               cP 47 tyMeta 48,
               (Loc.base ⟨48⟩,
                 { declaredTy := some tyMeta
                   value := metaV (.addr (.base ⟨53⟩))
                     (.addr (.base ⟨57⟩)) (.addr (.base ⟨59⟩)) }),
               cP 49 tyCS 53, cP 50 tyCS 53, cP 51 tyCS 53,
               cP 52 tyCS 53,
               (Loc.base ⟨53⟩,
                 { declaredTy := some tyCS
                   value := csAllNilV (.addr (.base ⟨55⟩)) }),
               cP 54 .bool 55,
               (Loc.base ⟨55⟩,
                 { declaredTy := some .bool, value := .bool false }),
               cP 56 (.int .uint64) 57,
               (Loc.base ⟨57⟩,
                 { declaredTy := some (.int .uint64), value := u64v 0 }),
               cP 58 (.int .uint64) 59,
               (Loc.base ⟨59⟩,
                 { declaredTy := some (.int .uint64), value := u64v 0 })]
      nextAddr := 60 }

/-- The entry step at the machine's own nullary route (the statement
arm enters the frame directly): with the caller's `targets` symbolic
under the encoding premise, one step lands at the body over the
result frame, the result cell nil-initialized at ⟨31⟩. -/
private theorem nms_step1 (targets : Array Assignee)
    (plans : List (TargetShape × List Expr))
    (henc : targetsPlan targets.toList = some plans)
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFn { wBase with heap := [], nextAddr := 31 }
      (.exec (.call targets ⟨"raft.NewMemoryStorage"⟩ #[]) env k) ch
      = .ok (.exec nmsFunc.body [[("$res0", Loc.base ⟨31⟩)]]
          (.frame plans env [Loc.base ⟨31⟩] [] k false),
        { wBase with
            heap := [(Loc.base ⟨31⟩,
              { declaredTy := some (.pointer tyMS), value := .nil })]
            nextAddr := 32 }, ch) := by
  unfold stepFn
  dsimp only
  rw [henc]
  kernel_rfl

/-- The NewMemoryStorage body span from the entered frame (PRIVATE
count-bearing scaffolding — 447 further machine steps, zero choices,
open `plans`/`env`/`k`/`ch`). -/
private theorem nms_body_span
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 447
      { wBase with
          heap := [(Loc.base ⟨31⟩,
            { declaredTy := some (.pointer tyMS), value := .nil })]
          nextAddr := 32 }
      (.exec nmsFunc.body [[("$res0", Loc.base ⟨31⟩)]]
        (.frame plans env [Loc.base ⟨31⟩] [] k false)) ch
      = .ok (.returning (.frame plans env [Loc.base ⟨31⟩] [] k false),
        nmsPost, ch) := by
  kernel_rfl

/-- **THE `NewMemoryStorage` CallSpecRN** (the nullary form's first
honest instance): from the bare tables, the call allocates and
returns the fresh storage — dummy entry, `Ensure`'d zero snapshot
chain, unlocked mutex — the state `ApplySnapshot` consumes. Terminal
state pinned in full. -/
theorem newMemoryStorage_callSpecRN :
    CallSpecRN NMSPre ⟨"raft.NewMemoryStorage"⟩
      (fun σ' vs =>
        vs = [.addr (.base ⟨37⟩)] ∧ σ' = nmsPost ∧
        Heap.lookup σ'.heap (Loc.base ⟨37⟩)
          = some { declaredTy := some tyMS
                   value := msV 0 0 .nil (.addr (.base ⟨43⟩))
                     (.slice ⟨some (.base ⟨35⟩), 0, 1, 1⟩) }) := by
  intro σ hP targets plans henc env k ch
  refine ⟨448, nmsPost, [Loc.base ⟨31⟩], [.addr (.base ⟨37⟩)], ch,
    ?_, rfl, ⟨rfl, rfl, rfl⟩, List.suffix_refl ch⟩
  rw [hP]
  exact stepFnIter_chain (stepFnIter_one (nms_step1 targets plans henc env k ch))
    (nms_body_span plans env k ch)

/-- Non-vacuity: the (unique) family member, plus the encoding
premise discharged at the harness's own single-target shape. -/
theorem nmsPre_inhabited :
    NMSPre { wBase with heap := [], nextAddr := 31 } ∧
    targetsPlan ([Assignee.var "$c2270"])
      = some [(.chain [], [Expr.ref "$c2270"])] :=
  ⟨rfl, rfl⟩

/-! ## `raft.newLogWithSize` (census log.go:75; called by `newRaft`
at the post-`ApplySnapshot` storage — the Base-clause log-offsets
member: committed = applying = applied = 1, unstable.offset = 2) -/

/-- The post-`ApplySnapshot` storage footprint the span reads: the
ms cell (snapshot pointer rides FREE — the span provably never reads
it), the one-entry backing, the (1,1) entry, its Term/Index cells.
The logger interface payload enters through the ARGUMENT (`lL` in
the spec), not the pre-state. -/
def NLPre (sv hv : GoValue) (σm : ExecState) : Prop :=
  σm = { wBase with
          heap := [(Loc.base ⟨31⟩,
                     { declaredTy := some tyMS
                       value := msV 0 0 hv sv
                         (.slice ⟨some (.base ⟨37⟩), 0, 1, 1⟩) }),
                   (Loc.base ⟨37⟩,
                     { declaredTy := some (.array 1 (.pointer tyEnt))
                       value := .array #[.addr (.base ⟨38⟩)] }),
                   (Loc.base ⟨38⟩,
                     { declaredTy := some tyEnt
                       value := .struct ⟨"raftpb.Entry"⟩
                         #[("Term", .addr (.base ⟨39⟩)),
                           ("Index", .addr (.base ⟨40⟩)),
                           ("Type", .nil), ("Data", nilSlice)] }),
                   (Loc.base ⟨39⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨40⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 })]
          nextAddr := 41 }

def storageIfaceV : GoValue :=
  .interface (.pointer tyMS) (.addr (.base ⟨31⟩))
def loggerIfaceV (lL : Loc) : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr lL)

/-- The raftLog value `newLogWithSize` builds — THE BASE-CLAUSE FACT
CARRIER: committed = applying = applied = firstIndex−1 = 1,
unstable.offset = offsetInProgress = lastIndex+1 = 2 (census §0
storage row). -/
def newLogV (lL : Loc) : GoValue :=
  .struct ⟨"raft.raftLog"⟩
    #[("storage", storageIfaceV),
      ("unstable",
       .struct ⟨"raft.unstable"⟩
         #[("snapshot", .nil), ("entries", nilSlice),
           ("offset", u64v 2), ("snapshotInProgress", .bool false),
           ("offsetInProgress", u64v 2),
           ("logger", loggerIfaceV lL)]),
      ("committed", u64v 1), ("applying", u64v 1), ("applied", u64v 1),
      ("logger", loggerIfaceV lL),
      ("maxApplyingEntsSize", u64v 1048576),
      ("applyingEntsSize", u64v 0), ("applyingEntsPaused", .bool false)]

def cU (a : Nat) (n : Int) : Loc × HeapCell :=
  (Loc.base ⟨a⟩, { declaredTy := some (.int .uint64), value := u64v n })
def cErr (a : Nat) : Loc × HeapCell :=
  (Loc.base ⟨a⟩, { declaredTy := some (.interface ⟨"error"⟩), value := .nil })
def cMuP (a : Nat) : Loc × HeapCell :=
  (Loc.base ⟨a⟩,
   { declaredTy := some (.pointer (.sync .mutex))
     value := .addr (.field (.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩ "Mutex") })

/-- The newLogWithSize terminal state: footprint read back (callStats
firstIndex/lastIndex bumped to 1 — the two interface dispatches), the
new raftLog cell at ⟨69⟩, the machine's frame/temp cells. -/
def nlPost (sv hv : GoValue) (lL : Loc) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
                 { declaredTy := some tyMS
                   value := msV 1 1 hv sv
                     (.slice ⟨some (.base ⟨37⟩), 0, 1, 1⟩) }),
               (Loc.base ⟨37⟩,
                 { declaredTy := some (.array 1 (.pointer tyEnt))
                   value := .array #[.addr (.base ⟨38⟩)] }),
               (Loc.base ⟨38⟩,
                 { declaredTy := some tyEnt
                   value := .struct ⟨"raftpb.Entry"⟩
                     #[("Term", .addr (.base ⟨39⟩)),
                       ("Index", .addr (.base ⟨40⟩)),
                       ("Type", .nil), ("Data", nilSlice)] }),
               cU 39 1, cU 40 1,
               (Loc.base ⟨41⟩,
                 { declaredTy := some (.interface ⟨"raft.Storage"⟩)
                   value := storageIfaceV }),
               (Loc.base ⟨42⟩,
                 { declaredTy := some (.interface ⟨"raft.Logger"⟩)
                   value := loggerIfaceV lL }),
               (Loc.base ⟨43⟩,
                 { declaredTy := some (.defined ⟨"raft.entryEncodingSize"⟩)
                   value := u64v 1048576 }),
               (Loc.base ⟨44⟩,
                 { declaredTy := some (.pointer (.defined ⟨"raft.raftLog"⟩))
                   value := .addr (.base ⟨69⟩) }),
               cU 45 2, cErr 46, cP 47 tyMS 31, cU 48 2, cErr 49,
               cU 50 2, cP 51 tyMS 31, cU 52 2, cU 53 1,
               cP 54 tyEnt 38, cU 55 1, cMuP 56, cU 57 1,
               cP 58 tyMS 31, cU 59 1, cErr 60, cU 61 1,
               cP 62 tyMS 31, cU 63 1, cU 64 1, cP 65 tyEnt 38,
               cU 66 1, cMuP 67,
               (Loc.base ⟨68⟩,
                 { declaredTy := some (.pointer (.defined ⟨"raft.raftLog"⟩))
                   value := .addr (.base ⟨69⟩) }),
               (Loc.base ⟨69⟩,
                 { declaredTy := some (.defined ⟨"raft.raftLog"⟩)
                   value := newLogV lL })]
      nextAddr := 70 }

/-- The newLogWithSize span (PRIVATE count-bearing scaffolding — 472
machine steps incl. the two `Storage`-interface dispatches with their
lock/defer walks, zero choices, open `plans`/`env`/`k`/`ch` and free
`sv`/`hv`/`lL`). -/
private theorem nl_span (sv hv : GoValue) (lL : Loc)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 472
      { wBase with
          heap := [(Loc.base ⟨31⟩,
                     { declaredTy := some tyMS
                       value := msV 0 0 hv sv
                         (.slice ⟨some (.base ⟨37⟩), 0, 1, 1⟩) }),
                   (Loc.base ⟨37⟩,
                     { declaredTy := some (.array 1 (.pointer tyEnt))
                       value := .array #[.addr (.base ⟨38⟩)] }),
                   (Loc.base ⟨38⟩,
                     { declaredTy := some tyEnt
                       value := .struct ⟨"raftpb.Entry"⟩
                         #[("Term", .addr (.base ⟨39⟩)),
                           ("Index", .addr (.base ⟨40⟩)),
                           ("Type", .nil), ("Data", nilSlice)] }),
                   (Loc.base ⟨39⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨40⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 })]
          nextAddr := 41 }
      (.retV (u64v 1048576)
        (.callArgsK ⟨"raft.newLogWithSize"⟩ plans
          [storageIfaceV, loggerIfaceV lL] [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨44⟩] [] k false),
        nlPost sv hv lL, ch) := by
  kernel_rfl

/-- **THE `newLogWithSize` CallSpecR** at the post-`ApplySnapshot`
storage family: returns a pointer to the fresh raftLog with the
census §0 storage-row facts — committed = applying = applied = 1,
unstable.offset = offsetInProgress = 2, empty unstable, storage
wired back to the footprint — stated BOTH as the exact cell readback
and in the invariant's reader vocabulary (`absRaftLog`). The
snapshot/hardState fields and the logger payload ride free. -/
theorem newLogWithSize_callSpecR (sv hv : GoValue) (lL : Loc) :
    CallSpecR (NLPre sv hv) ⟨"raft.newLogWithSize"⟩
      [storageIfaceV, loggerIfaceV lL] (u64v 1048576)
      (fun σ' vs =>
        vs = [.addr (.base ⟨69⟩)] ∧ σ' = nlPost sv hv lL ∧
        Heap.lookup σ'.heap (Loc.base ⟨69⟩)
          = some { declaredTy := some (.defined ⟨"raft.raftLog"⟩)
                   value := newLogV lL } ∧
        GoLean.RaftSeam.absRaftLog σ' ⟨69⟩
          = some { stable := [(1, 1)], unstableEnts := [],
                   offset := 2, committed := 1, applying := 1,
                   applied := 1 }) := by
  intro σ hP plans env k ch
  refine ⟨472, nlPost sv hv lL, [Loc.base ⟨44⟩], [.addr (.base ⟨69⟩)],
    ch, ?_, rfl, ⟨rfl, rfl, rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]; exact nl_span sv hv lL plans env k ch
  · rfl

/-- Non-vacuity: the family at the real fresh-chain values. -/
theorem nlPre_inhabited :
    NLPre (.addr (.base ⟨32⟩)) .nil
      { wBase with
          heap := [(Loc.base ⟨31⟩,
                     { declaredTy := some tyMS
                       value := msV 0 0 .nil (.addr (.base ⟨32⟩))
                         (.slice ⟨some (.base ⟨37⟩), 0, 1, 1⟩) }),
                   (Loc.base ⟨37⟩,
                     { declaredTy := some (.array 1 (.pointer tyEnt))
                       value := .array #[.addr (.base ⟨38⟩)] }),
                   (Loc.base ⟨38⟩,
                     { declaredTy := some tyEnt
                       value := .struct ⟨"raftpb.Entry"⟩
                         #[("Term", .addr (.base ⟨39⟩)),
                           ("Index", .addr (.base ⟨40⟩)),
                           ("Type", .nil), ("Data", nilSlice)] }),
                   (Loc.base ⟨39⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨40⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 })]
          nextAddr := 41 } := rfl

/-! ## `raft.MemoryStorage.ApplySnapshot` (census E3; harness
`newTwin`, twin-lib.go:198) — the first `CallSpecRD` (defer-tail)
member -/

/-- The snap-ARGUMENT ConfState (pre-`Ensure`: `AutoLeave` nil; the
Voters backing pinned at the slot-0-realized shape — the labeled
parked axis: cap 4, `[1,2,3,0]`). -/
def argCSV : GoValue :=
  .struct ⟨"raftpb.ConfState"⟩
    #[("Voters", .slice ⟨some (.base ⟨50⟩), 0, 3, 4⟩),
      ("Learners", nilSlice), ("VotersOutgoing", nilSlice),
      ("LearnersNext", nilSlice), ("AutoLeave", .nil)]

/-- The ApplySnapshot footprint: the fresh-storage chain (the
`NewMemoryStorage` result shape at canonical addresses 31..40) + the
harness-built snapshot-argument chain (45..50). -/
def ASPre (σm : ExecState) : Prop :=
  σm = { wBase with
          heap := [(Loc.base ⟨31⟩,
                     { declaredTy := some tyMS
                       value := msV 0 0 .nil (.addr (.base ⟨32⟩))
                         (.slice ⟨some (.base ⟨37⟩), 0, 1, 1⟩) }),
                   (Loc.base ⟨32⟩,
                     { declaredTy := some tySnap
                       value := snapV (.addr (.base ⟨33⟩)) }),
                   (Loc.base ⟨33⟩,
                     { declaredTy := some tyMeta
                       value := metaV (.addr (.base ⟨34⟩))
                         (.addr (.base ⟨35⟩)) (.addr (.base ⟨36⟩)) }),
                   (Loc.base ⟨34⟩,
                     { declaredTy := some tyCS
                       value := csAllNilV (.addr (.base ⟨40⟩)) }),
                   (Loc.base ⟨35⟩,
                     { declaredTy := some (.int .uint64), value := u64v 0 }),
                   (Loc.base ⟨36⟩,
                     { declaredTy := some (.int .uint64), value := u64v 0 }),
                   (Loc.base ⟨37⟩,
                     { declaredTy := some (.array 1 (.pointer tyEnt))
                       value := .array #[.addr (.base ⟨38⟩)] }),
                   (Loc.base ⟨38⟩,
                     { declaredTy := some tyEnt, value := freshEntryV }),
                   (Loc.base ⟨40⟩,
                     { declaredTy := some .bool, value := .bool false }),
                   (Loc.base ⟨45⟩,
                     { declaredTy := some tySnap
                       value := snapV (.addr (.base ⟨46⟩)) }),
                   (Loc.base ⟨46⟩,
                     { declaredTy := some tyMeta
                       value := metaV (.addr (.base ⟨47⟩))
                         (.addr (.base ⟨48⟩)) (.addr (.base ⟨49⟩)) }),
                   (Loc.base ⟨47⟩,
                     { declaredTy := some tyCS, value := argCSV }),
                   (Loc.base ⟨48⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨49⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨50⟩,
                     { declaredTy := some (.array 4 (.int .uint64))
                       value := .array #[u64v 1, u64v 2, u64v 3, u64v 0] })]
          nextAddr := 51 }

/-- The ApplySnapshot terminal state (defer drained: mutex UNLOCKED
again; the storage rewritten — snapshot := the CLONED chain at ⟨91⟩
(canonical cap-3 Voters at ⟨106⟩), ents := the one-entry (1,1) slice
at ⟨133⟩/⟨131⟩; the ARGUMENT chain `Ensure`-mutated in place
(AutoLeave filled at ⟨63⟩); the machine's frame/temp cells).
Transcribed from the probe run and re-checked symbolically by the
span lemma's `kernel_rfl`. -/
def asPost : ExecState :=
  { wBase with
      heap :=
      [(Loc.base ⟨31⟩,
        { declaredTy := some (Ty.defined ⟨"raft.MemoryStorage"⟩),
          value := GoValue.struct
                     ⟨"raft.MemoryStorage"⟩
                     #[("Mutex", GoValue.syncData (SyncPrim.mutex false)), ("hardState", GoValue.nil),
                       ("snapshot", GoValue.addr (Loc.base ⟨91⟩)),
                       ("ents",
                        GoValue.slice
                          ⟨some (Loc.base ⟨133⟩), 0, 1, 1⟩),
                       ("callStats",
                        GoValue.struct
                          ⟨"raft.inMemStorageCallStats"⟩
                          #[("initialState", GoValue.int 0 (IntKind.int)),
                            ("firstIndex", GoValue.int 0 (IntKind.int)),
                            ("lastIndex", GoValue.int 0 (IntKind.int)),
                            ("entries", GoValue.int 0 (IntKind.int)),
                            ("term", GoValue.int 0 (IntKind.int)),
                            ("snapshot", GoValue.int 0 (IntKind.int))])] }),
       (Loc.base ⟨32⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.Snapshot"⟩),
          value := GoValue.struct
                     ⟨"raftpb.Snapshot"⟩
                     #[("Data", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("Metadata", GoValue.addr (Loc.base ⟨33⟩))] }),
       (Loc.base ⟨33⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩),
          value := GoValue.struct
                     ⟨"raftpb.SnapshotMetadata"⟩
                     #[("ConfState", GoValue.addr (Loc.base ⟨34⟩)),
                       ("Index", GoValue.addr (Loc.base ⟨35⟩)),
                       ("Term", GoValue.addr (Loc.base ⟨36⟩))] }),
       (Loc.base ⟨34⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.ConfState"⟩),
          value := GoValue.struct
                     ⟨"raftpb.ConfState"⟩
                     #[("Voters", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("Learners", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("VotersOutgoing", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("LearnersNext", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("AutoLeave", GoValue.addr (Loc.base ⟨40⟩))] }),
       (Loc.base ⟨35⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 0 (IntKind.uint64) }),
       (Loc.base ⟨36⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 0 (IntKind.uint64) }),
       (Loc.base ⟨37⟩,
        { declaredTy := some (Ty.array
                          1
                          (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))),
          value := GoValue.array #[GoValue.addr (Loc.base ⟨38⟩)] }),
       (Loc.base ⟨38⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.Entry"⟩),
          value := GoValue.struct
                     ⟨"raftpb.Entry"⟩
                     #[("Term", GoValue.nil), ("Index", GoValue.nil), ("Type", GoValue.nil),
                       ("Data", GoValue.slice ⟨none, 0, 0, 0⟩)] }),
       (Loc.base ⟨40⟩, { declaredTy := some (Ty.bool), value := GoValue.bool false }),
       (Loc.base ⟨45⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.Snapshot"⟩),
          value := GoValue.struct
                     ⟨"raftpb.Snapshot"⟩
                     #[("Data", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("Metadata", GoValue.addr (Loc.base ⟨46⟩))] }),
       (Loc.base ⟨46⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩),
          value := GoValue.struct
                     ⟨"raftpb.SnapshotMetadata"⟩
                     #[("ConfState", GoValue.addr (Loc.base ⟨47⟩)),
                       ("Index", GoValue.addr (Loc.base ⟨48⟩)),
                       ("Term", GoValue.addr (Loc.base ⟨49⟩))] }),
       (Loc.base ⟨47⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.ConfState"⟩),
          value := GoValue.struct
                     ⟨"raftpb.ConfState"⟩
                     #[("Voters",
                        GoValue.slice
                          ⟨some (Loc.base ⟨50⟩), 0, 3, 4⟩),
                       ("Learners", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("VotersOutgoing", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("LearnersNext", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("AutoLeave", GoValue.addr (Loc.base ⟨63⟩))] }),
       (Loc.base ⟨48⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨49⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨50⟩,
        { declaredTy := some (Ty.array 4 (Ty.int (IntKind.uint64))),
          value := GoValue.array
                     #[GoValue.int 1 (IntKind.uint64),
                       GoValue.int 2 (IntKind.uint64),
                       GoValue.int 3 (IntKind.uint64),
                       GoValue.int 0 (IntKind.uint64)] }),
       (Loc.base ⟨51⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.MemoryStorage"⟩)),
          value := GoValue.addr (Loc.base ⟨31⟩) }),
       (Loc.base ⟨52⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨53⟩,
        { declaredTy := some (Ty.interface ⟨"error"⟩), value := GoValue.nil }),
       (Loc.base ⟨54⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨55⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨56⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨57⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨58⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨59⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨47⟩) }),
       (Loc.base ⟨60⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨47⟩) }),
       (Loc.base ⟨61⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨47⟩) }),
       (Loc.base ⟨62⟩,
        { declaredTy := some (Ty.pointer (Ty.bool)),
          value := GoValue.addr (Loc.base ⟨63⟩) }),
       (Loc.base ⟨63⟩, { declaredTy := some (Ty.bool), value := GoValue.bool false }),
       (Loc.base ⟨64⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨65⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨32⟩) }),
       (Loc.base ⟨66⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨67⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 0 (IntKind.uint64) }),
       (Loc.base ⟨68⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨33⟩) }),
       (Loc.base ⟨69⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 0 (IntKind.uint64) }),
       (Loc.base ⟨70⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨71⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨72⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨73⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨74⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨75⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨76⟩,
        { declaredTy := some (Ty.interface ⟨"proto.Message"⟩),
          value := GoValue.interface
                     (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩))
                     (GoValue.addr (Loc.base ⟨91⟩)) }),
       (Loc.base ⟨77⟩,
        { declaredTy := some (Ty.interface ⟨"proto.Message"⟩),
          value := GoValue.interface
                     (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩))
                     (GoValue.addr (Loc.base ⟨45⟩)) }),
       (Loc.base ⟨78⟩,
        { declaredTy := some (Ty.interface ⟨"proto.Message"⟩),
          value := GoValue.interface
                     (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩))
                     (GoValue.addr (Loc.base ⟨91⟩)) }),
       (Loc.base ⟨79⟩,
        { declaredTy := some (Ty.interface ⟨"proto.Message"⟩),
          value := GoValue.interface
                     (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩))
                     (GoValue.addr (Loc.base ⟨45⟩)) }),
       (Loc.base ⟨80⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩)),
          value := GoValue.nil }),
       (Loc.base ⟨81⟩, { declaredTy := some (Ty.bool), value := GoValue.bool false }),
       (Loc.base ⟨82⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.nil }),
       (Loc.base ⟨83⟩, { declaredTy := some (Ty.bool), value := GoValue.bool false }),
       (Loc.base ⟨84⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨85⟩, { declaredTy := some (Ty.bool), value := GoValue.bool true }),
       (Loc.base ⟨86⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨87⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨91⟩) }),
       (Loc.base ⟨88⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨89⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨91⟩) }),
       (Loc.base ⟨90⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨91⟩) }),
       (Loc.base ⟨91⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.Snapshot"⟩),
          value := GoValue.struct
                     ⟨"raftpb.Snapshot"⟩
                     #[("Data", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("Metadata", GoValue.addr (Loc.base ⟨97⟩))] }),
       (Loc.base ⟨92⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨91⟩) }),
       (Loc.base ⟨93⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨97⟩) }),
       (Loc.base ⟨94⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨95⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨97⟩) }),
       (Loc.base ⟨96⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨97⟩) }),
       (Loc.base ⟨97⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩),
          value := GoValue.struct
                     ⟨"raftpb.SnapshotMetadata"⟩
                     #[("ConfState", GoValue.addr (Loc.base ⟨103⟩)),
                       ("Index", GoValue.addr (Loc.base ⟨110⟩)),
                       ("Term", GoValue.addr (Loc.base ⟨111⟩))] }),
       (Loc.base ⟨98⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨97⟩) }),
       (Loc.base ⟨99⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨103⟩) }),
       (Loc.base ⟨100⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨47⟩) }),
       (Loc.base ⟨101⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨103⟩) }),
       (Loc.base ⟨102⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨103⟩) }),
       (Loc.base ⟨103⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.ConfState"⟩),
          value := GoValue.struct
                     ⟨"raftpb.ConfState"⟩
                     #[("Voters",
                        GoValue.slice
                          ⟨some (Loc.base ⟨106⟩), 0, 3, 3⟩),
                       ("Learners", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("VotersOutgoing", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("LearnersNext", GoValue.slice ⟨none, 0, 0, 0⟩),
                       ("AutoLeave", GoValue.addr (Loc.base ⟨109⟩))] }),
       (Loc.base ⟨104⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.ConfState"⟩)),
          value := GoValue.addr (Loc.base ⟨103⟩) }),
       (Loc.base ⟨105⟩,
        { declaredTy := some (Ty.slice (Ty.int (IntKind.uint64))),
          value := GoValue.slice ⟨some (Loc.base ⟨106⟩), 0, 3, 3⟩ }),
       (Loc.base ⟨106⟩,
        { declaredTy := some (Ty.array 3 (Ty.int (IntKind.uint64))),
          value := GoValue.array
                     #[GoValue.int 1 (IntKind.uint64),
                       GoValue.int 2 (IntKind.uint64),
                       GoValue.int 3 (IntKind.uint64)] }),
       (Loc.base ⟨107⟩,
        { declaredTy := some (Ty.int (IntKind.int)),
          value := GoValue.int 3 (IntKind.int) }),
       (Loc.base ⟨108⟩,
        { declaredTy := some (Ty.int (IntKind.int)),
          value := GoValue.int 3 (IntKind.int) }),
       (Loc.base ⟨109⟩, { declaredTy := some (Ty.bool), value := GoValue.bool false }),
       (Loc.base ⟨110⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨111⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨112⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨113⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨114⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨115⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨116⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨117⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨118⟩,
        { declaredTy := some (Ty.pointer (Ty.int (IntKind.uint64))),
          value := GoValue.addr (Loc.base ⟨119⟩) }),
       (Loc.base ⟨119⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨120⟩,
        { declaredTy := some (Ty.pointer (Ty.int (IntKind.uint64))),
          value := GoValue.addr (Loc.base ⟨119⟩) }),
       (Loc.base ⟨121⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨122⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Snapshot"⟩)),
          value := GoValue.addr (Loc.base ⟨45⟩) }),
       (Loc.base ⟨123⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨124⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨125⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.SnapshotMetadata"⟩)),
          value := GoValue.addr (Loc.base ⟨46⟩) }),
       (Loc.base ⟨126⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨127⟩,
        { declaredTy := some (Ty.pointer (Ty.int (IntKind.uint64))),
          value := GoValue.addr (Loc.base ⟨128⟩) }),
       (Loc.base ⟨128⟩,
        { declaredTy := some (Ty.int (IntKind.uint64)),
          value := GoValue.int 1 (IntKind.uint64) }),
       (Loc.base ⟨129⟩,
        { declaredTy := some (Ty.pointer (Ty.int (IntKind.uint64))),
          value := GoValue.addr (Loc.base ⟨128⟩) }),
       (Loc.base ⟨130⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩)),
          value := GoValue.addr (Loc.base ⟨131⟩) }),
       (Loc.base ⟨131⟩,
        { declaredTy := some (Ty.defined ⟨"raftpb.Entry"⟩),
          value := GoValue.struct
                     ⟨"raftpb.Entry"⟩
                     #[("Term", GoValue.addr (Loc.base ⟨119⟩)),
                       ("Index", GoValue.addr (Loc.base ⟨128⟩)), ("Type", GoValue.nil),
                       ("Data", GoValue.slice ⟨none, 0, 0, 0⟩)] }),
       (Loc.base ⟨132⟩,
        { declaredTy := some (Ty.slice
                          (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))),
          value := GoValue.slice ⟨some (Loc.base ⟨133⟩), 0, 1, 1⟩ }),
       (Loc.base ⟨133⟩,
        { declaredTy := some (Ty.array
                          1
                          (Ty.pointer (Ty.defined ⟨"raftpb.Entry"⟩))),
          value := GoValue.array #[GoValue.addr (Loc.base ⟨131⟩)] }),
       (Loc.base ⟨134⟩,
        { declaredTy := some (Ty.pointer (Ty.sync (SyncKind.mutex))),
          value := GoValue.addr
                     (Loc.field (Loc.base ⟨31⟩) ⟨"raft.MemoryStorage"⟩ "Mutex") })]
      nextAddr := 135 }

/-- The ApplySnapshot span (PRIVATE count-bearing scaffolding — 1420
machine steps incl. `EnsureSnapshot`'s in-place argument repair, the
plainpb deep clone, and the deferred `Unlock` drain; zero choices,
open `plans`/`env`/`k`/`ch`). -/
private theorem as_span (sh : TargetShape) (e : Expr)
    (ops : List Expr) (rest : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) (ch : Choices) :
    stepFnIter 1420
      { wBase with
          heap := [(Loc.base ⟨31⟩,
                     { declaredTy := some tyMS
                       value := msV 0 0 .nil (.addr (.base ⟨32⟩))
                         (.slice ⟨some (.base ⟨37⟩), 0, 1, 1⟩) }),
                   (Loc.base ⟨32⟩,
                     { declaredTy := some tySnap
                       value := snapV (.addr (.base ⟨33⟩)) }),
                   (Loc.base ⟨33⟩,
                     { declaredTy := some tyMeta
                       value := metaV (.addr (.base ⟨34⟩))
                         (.addr (.base ⟨35⟩)) (.addr (.base ⟨36⟩)) }),
                   (Loc.base ⟨34⟩,
                     { declaredTy := some tyCS
                       value := csAllNilV (.addr (.base ⟨40⟩)) }),
                   (Loc.base ⟨35⟩,
                     { declaredTy := some (.int .uint64), value := u64v 0 }),
                   (Loc.base ⟨36⟩,
                     { declaredTy := some (.int .uint64), value := u64v 0 }),
                   (Loc.base ⟨37⟩,
                     { declaredTy := some (.array 1 (.pointer tyEnt))
                       value := .array #[.addr (.base ⟨38⟩)] }),
                   (Loc.base ⟨38⟩,
                     { declaredTy := some tyEnt, value := freshEntryV }),
                   (Loc.base ⟨40⟩,
                     { declaredTy := some .bool, value := .bool false }),
                   (Loc.base ⟨45⟩,
                     { declaredTy := some tySnap
                       value := snapV (.addr (.base ⟨46⟩)) }),
                   (Loc.base ⟨46⟩,
                     { declaredTy := some tyMeta
                       value := metaV (.addr (.base ⟨47⟩))
                         (.addr (.base ⟨48⟩)) (.addr (.base ⟨49⟩)) }),
                   (Loc.base ⟨47⟩,
                     { declaredTy := some tyCS, value := argCSV }),
                   (Loc.base ⟨48⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨49⟩,
                     { declaredTy := some (.int .uint64), value := u64v 1 }),
                   (Loc.base ⟨50⟩,
                     { declaredTy := some (.array 4 (.int .uint64))
                       value := .array #[u64v 1, u64v 2, u64v 3, u64v 0] })]
          nextAddr := 51 }
      (.retV (.addr (.base ⟨45⟩))
        (.callArgsK ⟨"raft.MemoryStorage.ApplySnapshot"⟩
          ((sh, e :: ops) :: rest) [.addr (.base ⟨31⟩)] [] env k)) ch
      = .ok (.next (.frame ((sh, e :: ops) :: rest) env
            [Loc.base ⟨53⟩] [] k false),
        asPost, ch) := by
  kernel_rfl

/-- **THE `ApplySnapshot` CallSpecRD** (the defer-tail form's first
honest instance) at the harness snapshot `{Index:1, Term:1,
Voters:[1,2,3]}` over the fresh storage: succeeds (`nil` error), the
storage now holds the census §0 storage row — ents = one entry at
`(index 1, term 1)`, snapshot = the cloned canonical chain — with
the mutex unlocked (defer drained). Stated as the exact readback,
the full terminal state, and the invariant-reader fact
`absStorageEnts = [(1, 1)]`. -/
theorem applySnapshot_callSpecRD :
    CallSpecRD ASPre ⟨"raft.MemoryStorage.ApplySnapshot"⟩
      [.addr (.base ⟨31⟩)] (.addr (.base ⟨45⟩))
      (fun σ' vs =>
        vs = [.nil] ∧ σ' = asPost ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := some tyMS
                   value := msV 0 0 .nil (.addr (.base ⟨91⟩))
                     (.slice ⟨some (.base ⟨133⟩), 0, 1, 1⟩) } ∧
        GoLean.RaftSeam.absStorageEnts σ' ⟨31⟩ = some [(1, 1)]) := by
  intro σ hP sh e ops rest env k ch
  refine ⟨1420, asPost, [Loc.base ⟨53⟩], [.nil], ch, ?_, rfl,
    ⟨rfl, rfl, ?_, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]; exact as_span sh e ops rest env k ch
  · rfl
  · rfl

/-- Non-vacuity: the (unique) family member. -/
theorem asPre_inhabited : ∃ σm, ASPre σm := ⟨_, rfl⟩


end GoLean.RaftSeam.InitA
