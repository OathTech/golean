import GoLean.GoCore.Race

/-!
# The ThreadPool machine (channels arc slice 2, design of record D1/D2a)

`MultiConfig` is the executable multi-goroutine machine: an append-only
pool of per-goroutine `Config`s over ONE shared `ExecState`, plus the
index of the RUNNING goroutine. The sequential machine is untouched —
the pool is a purely additive layer (grow by extension, never revision),
and `execProg_single_eq_execStmt` (MultiSound.lean) is the theorem that
a one-thread pool IS the sequential machine.

Design points (docs/2026-08-06_channels-arc-design.md):

* **D1 — stable goroutine identity.** The pool is APPEND-ONLY: a spawn
  pushes at the end, and a finished goroutine keeps its terminal config
  as a tombstone (it is simply never runnable again) — so the array
  index IS the goroutine's stable identity for its whole life (main is
  goroutine 0). Nothing is removed, nothing shifts.

* **D2(a) — the scheduler consumption rule, WIDENED at W3.2 stage C
  (B1, G1 ruling 2026-08-20).** Context switches happen at registry
  ops (`Config.atBoundary`: channel-op/select/sync apply positions,
  spawn positions, goroutine exit, parked-blocked configs) AND at
  registry-op COMPLETIONS — the `.opDone` marker (generalizing
  BUG-040's post-spawn `.spawned`: every completing chan/sync/select
  op, pairing issuer, wake, and spawn now leaves the acting goroutine
  on a marker boundary, so "who runs after the op" is a scheduling
  point; envelope statement at `Config.opDone`, dossier-grounded);
  between boundaries the running goroutine steps without any scheduler
  involvement. The scheduling `Choices` sites (`ChoiceSite.l1Sched`,
  `ChoiceSite.postOp` — the site is the boundary shape's own,
  `Config.boundarySite`; the postOp slot menu is issuer-first,
  `schedSlots`) are consumed ONLY when the menu has ≥ 2 slots — their
  declared policy (`consumeAtOne := false`): a raw pop at bound 1
  would desynchronize every existing adversarial-stream run;
  sequential conservation depends on this.

* **D7 — pairing over waiter queues, WITH gc's waiter-queue
  PRIORITY** (re-designed at the S2 audit response — the original
  arrival intercept fired only when the op would BLOCK, so buffered
  ops bypassed parked waiters, gc's handoff observation was
  unreachable, and the invariant claimed below was FALSE for buffered
  channels). Blocked goroutines are the slice-1 blocked-Config shapes;
  channels hold NO waiter queues. Every channel/select op at its apply
  position consults PARKED PARTNERS FIRST (`arrivalPlan` — gc:
  `chansend` dequeues `recvq` BEFORE testing buffer room, `chanrecv`
  dequeues `sendq` before draining the buffer): a matched send-side
  arrival hands off directly; a matched receive-side arrival against a
  full buffer takes the HEAD and refills from the parked sender in the
  same step (gc's `recv()`). Only a partnerless op touches the cell.
  Parked goroutines are woken by CELL changes only (close; buffer
  data/room, both now unreachable beside a parked partner).

  **The hchan-invariant analogue, RESTORED and re-argued** (chan.go
  L17-18): (i) a parked receiver never coexists with a nonempty
  buffer — sends with parked receivers hand off and never enqueue
  (`applyPairing` asserts `.internal` on a breach rather than jumping
  the queue); (ii) a parked sender never coexists with buffer room —
  senders park only on full buffers and receives against parked
  senders refill the slot they drain; hence (iii) matched parked-
  parked pairs cannot coexist on ANY capacity (a parked receiver
  implies an empty buffer and a parked sender a full one — cap 0 —
  where both arrival directions pair before parking), so a close can
  never steal an already-pairable rendezvous; and (iv) every ARRIVAL
  checks closed BEFORE pairing — `chanArrivalPlan`'s two closed
  guards and `selectArrivalPlan`'s per-clause closed guard (S2
  convergence round: the select path first shipped WITHOUT it, so an
  arriving select could steal a rendezvous that close had already
  destroyed — a send-on-closed panic silently erased) — so a closed
  channel's ops always take the cell semantics (send panics, recv
  drains/zeroes, parked senders are left for their close-wake panic).
  Together (i)–(iv) rule out the too-wide close-window divergence in
  both directions: parked pairs cannot outlive a close unpaired, and
  no arrival pairs across a close.

* **FIFO through pressure.** A direct handoff happens only against an
  empty buffer (implied by invariant (i)); a receive meeting a parked
  sender over a nonempty buffer gets the buffer HEAD, the sender's
  value entering at the tail (spec: "Channels act as first-in-first-out
  queues"; probe p18's same-slot trick).

* **D6 — main-exit.** Main (goroutine 0) reaching a terminal ends the
  program with main's outcome; other goroutines are discarded mid-flight
  (spec §Program execution — probe p17: their defers never run). An
  unrecovered panic in ANY goroutine aborts the whole program.
  AMENDED (BUG-044, arc-final audit F2): the exit does not preempt
  runnable goroutines deterministically — the MAIN-EXIT WINDOW (L5, at
  `execProgLoop`) lets any finite number of runnable-goroutine steps
  precede the teardown, matching gc's racing of main's return against
  woken partners.

* **Deadlock.** ALL goroutines asleep — no thread runnable (tombstones
  excluded, parked threads unrunnable unless wake-ready) — is the
  `GoError.deadlock` terminal, generalizing slice 1's immediate
  single-thread classification and matching Go's detector state.

Fail closed (a visible `.unsupported`, never a silent approximation):
select-with-select rendezvous. `go` of a nil func value is gc's
"go of nil func value" runtime FATAL (probed 2026-08-07), MODELED via
`GoError.fatal` since the 19-red slice (triage L10, 2026-08-19; the
class itself landed at spec-parity slice 2). Multi-ready select went
LIVE at slice 4
(the L2 site — envelope statement at `applySelect`; arrival-path
`.multi` analysis here; wake-path head-commit at `resumeThread`).
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- The ThreadPool machine state (D1): the per-goroutine controls, the
ONE shared `ExecState` (heap, allocator, program context), and the
running goroutine. `threads` is append-only — index = stable goroutine
id, 0 = main; finished goroutines keep their terminal config as
tombstones. `cur` is the running goroutine: context switches happen
only when `threads[cur]` reaches a registry boundary
(`Config.atBoundary`). -/
structure MultiConfig where
  threads : Array Config
  shared : ExecState
  cur : Nat := 0

/-- The slice-1 blocked shapes — the parked goroutines — plus the
sync-parked shape (spec-parity slice 2). -/
def isBlockedConfig : Config → Bool
  | .blockedSend _ _ _ => true
  | .blockedRecv _ _ _ _ _ => true
  | .blockedSelect _ _ _ => true
  | .blockedSync _ _ _ _ => true
  | _ => false

/-- The completion marker's inner configuration, in the `spawnPlan`
extraction mold (what keeps the `stepThread` dispatch and its proofs
plan-shaped). W3.2 stage C: `.opDone` generalizes the old `.spawned`
marker (envelope statement at `Config.opDone`); its only step is the
strip to `inner`, and it is a registry boundary (`Config.atBoundary`)
and runnable — which is what makes "who runs after the op" a real
scheduling point. -/
def opDoneInner : Config → Option Config
  | .opDone _ c => some c
  | _ => none

/-- A goroutine with nothing left to do: the four unwound terminals
(only main can reach the non-`.next` ones — spawned goroutines run
under a barrier frame) and the program-aborting `.panicked`. Tombstones
in the append-only pool. -/
def threadDone : Config → Bool
  | .next .stop => true
  | .returning .stop => true
  | .breaking .stop => true
  | .continuing .stop => true
  | .panicked _ => true
  | _ => false

/-- The channel a chan-value points at (`none` for nil channels and
non-channel values). -/
def chanValueLoc : GoValue → Option Loc
  | .chan cv => cv.base
  | _ => none

/-- Cell-based wake-readiness of a parked goroutine: can its blocked
operation now proceed against the CHANNEL CELL alone? Parked partners
are deliberately not consulted — pairing happens at ARRIVAL (the
intercept), so matched parked-parked pairs never coexist and cell
readiness is the complete wake condition. Nil-channel blocks
(`ch = none`) are never ready (spec: "A nil channel is never ready for
communication"). A malformed cell yields `false` (the resume step, if
it were ever reached, fails closed with an explicit error; a parked
goroutine's cell cannot change shape — only channel ops touch
`chanData` cells). -/
def wakeReady (s : ExecState) : Config → Bool
  | .blockedSend (some loc) _ _ =>
      match loadLoc s loc with
      | .ok (.chanData buf capacity closed) => closed || buf.size < capacity
      | _ => false
  | .blockedRecv (some loc) _ _ _ _ =>
      match loadLoc s loc with
      | .ok (.chanData buf _ closed) => buf.size != 0 || closed
      | _ => false
  | .blockedSelect evs _ _ =>
      evs.any fun cl =>
        match clauseReady s cl with
        | .ok b => b
        | .error _ => false
  -- Sync parks (spec-parity slice 2, design note §6): CELL-based wake
  -- readiness — can the parked op now acquire against the primitive's
  -- state alone? WHICH ready contender proceeds is the L1 pick's
  -- latitude (the envelope statement at `applySyncOp`); no L4-analogue
  -- site exists for sync. A parked `rlock` stays unready while a
  -- writer is PENDING (`pendingW` — the documented exclusion of new
  -- readers); a parked `wgWait` stays unready on a NEGATIVE counter
  -- (probe p13: Wait unblocks only at exactly 0).
  | .blockedSync op loc _ _ =>
      match loadLoc s loc with
      | .ok (.syncData p) =>
          -- Op axis exhaustive (a new `SyncOp` head is a compile error);
          -- on the cell axis each parking head names its own primitive
          -- and the three OTHER primitives explicitly — an op/cell shape
          -- mismatch is "never ready" here (the resume path throws
          -- `.internal` on the same mismatch, `resumeThread`).
          match op with
          | .lock =>
              match p with
              | .mutex locked => !locked
              | .rwmutex .. | .waitGroup .. | .once .. => false
          | .wlock =>
              match p with
              | .rwmutex writer readers _ => !writer && readers == 0
              | .mutex .. | .waitGroup .. | .once .. => false
          | .rlock =>
              match p with
              | .rwmutex writer _ pendingW => !writer && pendingW == 0
              | .mutex .. | .waitGroup .. | .once .. => false
          | .wgWait =>
              match p with
              | .waitGroup counter _ => counter == 0
              | .mutex .. | .rwmutex .. | .once .. => false
          | .onceBegin _ =>
              match p with
              | .once _ done => done
              | .mutex .. | .rwmutex .. | .waitGroup .. => false
          -- The releasing heads are never parked (`applySyncOp` constructs
          -- `.blockedSync` only for the five above).
          | .unlock | .runlock | .wunlock | .wgAdd | .onceComplete => false
      -- ABSORBING DEFAULT, named: a load failure or a non-`syncData` cell
      -- at a parked sync op's `loc` reads "not ready" — the goroutine
      -- stays parked and the pool ends `.deadlock` if nothing else runs.
      | _ => false
  | _ => false

/-- Runnable = not a tombstone, and (if parked) wake-ready. -/
def threadRunnable (s : ExecState) (c : Config) : Bool :=
  !threadDone c && (!isBlockedConfig c || wakeReady s c)

/-- The runnable goroutine indices, in goroutine order. The SCHEDULER
envelope (L1, the pool's first live `Choices` site — consumed in
`stepMulti`): the Go spec says NOTHING about scheduling — no fairness,
no ordering between runnable goroutines (ground-truth note §1.2: pure
omission latitude bounded only by the blocking rules and the memory
model) — so the envelope is "ANY runnable goroutine may run next", and
the pick is drawn from the choice stream bounded by this list's length.
Width metadata for the enumerator/membership lane: the site's bound at
any consumption is `|runnable| ≤ |threads|`. -/
def runnableIdxs (s : ExecState) (threads : Array Config) : List Nat :=
  (List.range threads.size).filter fun j =>
    match threads[j]? with
    | some c => threadRunnable s c
    | none => false

/-- Registry boundaries (D2+D3): the configurations at which the
scheduler may switch goroutines — exactly the synchronization-op
registry (channel send/recv/close apply, select apply and the
no-operand select entry, `go` spawn positions, goroutine exit/abort)
plus the parked shapes (whose next step is their wake). Between
boundaries the running goroutine's steps are private to it. -/
def Config.atBoundary : Config → Bool
  | .retV _ (.chanStK _ _ [] _ _) => true
  | .retV _ (.selectOpsK _ _ _ [] _ _) => true
  | .retV _ (.goCalleeK [] _ _) => true
  | .retV _ (.goArgsK _ _ [] _ _) => true
  -- Registry-op COMPLETION (W3.2 stage C, B1 — generalizing BUG-040's
  -- post-spawn marker): the completion marker is a registry boundary
  -- of its own, so "who runs after the op" is a real scheduling
  -- point — the site the boundary consults is the marker's own tag
  -- (`Config.boundarySite`: `postOp` for op completions with slot 0 =
  -- issuer-continues; `l1Sched` for spawn completions, preserving
  -- BUG-040's shipped default). Envelope statement at `Config.opDone`.
  | .opDone _ _ => true
  | .exec (.selectStmt clauses _) _ _ => (selectOperands clauses.toList).isEmpty
  | .next .stop => true
  | .returning .stop => true
  | .breaking .stop => true
  | .continuing .stop => true
  | .panicked _ => true
  | .blockedSend _ _ _ => true
  | .blockedRecv _ _ _ _ _ => true
  | .blockedSelect _ _ _ => true
  -- Sync ops (spec-parity slice 2): the apply position is the
  -- registry's scheduling point — the EXISTING L1 site is consulted
  -- here (consumed only at |runnable| > 1); the op itself consumes
  -- nothing (`applySyncOp`'s envelope statement).
  | .retV _ (.syncStK _ _ [] _ _) => true
  | .blockedSync _ _ _ _ => true
  -- Loop BACK-EDGES (W3.2 stage D, B2 — G1 ruling 2026-08-20; THE
  -- ENVELOPE STATEMENT of `ChoiceSite.backEdge`): the loop re-entry
  -- shapes are scheduling points, so a goroutine inside a
  -- registry-free segment can be descheduled at an iteration edge.
  -- Spec argument (nondeterminism doctrine requirement 1): the spec is
  -- SILENT on scheduling — no text distinguishes a boundary-free
  -- segment from any other program point, so a switch at a back-edge
  -- is as conforming as one at a registry op (dossier §1.1:
  -- "The properties of the scheduler were never defined by the
  -- language"). Realizability: gc itself performs ASYNCHRONOUS
  -- preemption at arbitrary points, including inside registry-free
  -- loops, since Go 1.14 (the asyncpreemptoff GODEBUG knob documents
  -- the mechanism) — back-edge switches are a strict SUBSET of what
  -- one conforming implementation demonstrably does; mem#badsync's
  -- registry-free-spinner sentence ("The loop in main is not
  -- guaranteed to finish") is the normative-adjacent confirmation
  -- that implementations need not honor a spinner's monopoly, and
  -- dossier §3.1 (spec allows starvation) keeps the always-spin
  -- branches in the envelope BY RIGHT. Width bound: still
  -- goroutine-step-granularity interleavings respecting blocking/HB —
  -- inside C1's argued-maximal class. The site (`ChoiceSite.backEdge`,
  -- slot 0 = current-continues via `schedSlots`) is what makes the
  -- liveness tier's Fair non-vacuous (the site's policy docstring).
  -- `.next (.mapIterK …)` is the one iteration form with its own
  -- frame, and it was ALREADY a choice-consuming position (the
  -- mapIter pick) — making it a boundary aligns the two disciplines.
  | .next (.loop _ _ _ _) => true
  | .continuing (.loop _ _ _ _) => true
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ _) => true
  | _ => false

/-- The completed spawn positions: callee and argument values evaluated
(in the SPAWNING goroutine — spec §Go statements), ready to fork.
`some (callee, args, k)`; the per-goroutine `stepFn` fails closed on
these shapes (the pool owns the spawn). -/
def spawnPlan : Config → Option (GoValue × List GoValue × Cont)
  | .retV cv (.goCalleeK [] _ k) => some (cv, [], k)
  | .retV v (.goArgsK cv vals [] _ k) => some (cv, vals ++ [v], k)
  | _ => none

/-- The SPAWN (the registry's `go` entry): enter the callee's frame in
the shared state and fork the body as a fresh goroutine under a
targetless, resultless barrier frame (results are discarded — spec:
"they are discarded when the function completes"; the deferred-call
frame precedent). Returns (parent successor, child config, state).
A frame-ENTRY panic from the nil POINTER-BOX auto-deref class fires in
the CHILD — its first observable act is aborting on that panic (probed:
`go i.M()` with a nil *T box aborts in the spawned goroutine; pinned by
goroutines/spawn-edge/ptr-box-child-aborts). The OTHER `.panic` class
`enterFrame` can raise — dynamic dispatch on a NIL INTERFACE — fires in
the SPAWNER in gc, recoverably (probed; S2 audit): that class never
reaches this arm because the frontend hoists the nil-interface check
before the go statement (pinned by
goroutines/spawn-edge/nil-interface-recovered); the two classes are
indistinguishable from the panic message here, so any future lowering
that leaks the nil-interface class through a spawn would be misrouted
to a child abort by this arm — keep the hoist, or split the classes
upstream (recorded hazard, S2 audit response). A nil callee is gc's
"go of nil func value" runtime FATAL at the spawn (probed 2026-08-07,
refuting the older child-panic analysis): modeled as `GoError.fatal`
(triage L10). -/
def spawnStep (s : ExecState) (cv : GoValue) (args : List GoValue) (k : Cont) :
    Except GoError (Config × Config × ExecState) := do
  match cv with
  | .funcVal fid captured =>
      match enterFrame s fid (captured ++ args) with
      | .ok (func, frameEnv, _resultLocs, s') =>
          -- The parent lands on the completion marker (BUG-040, slice
          -- 4; stage C: `.spawned k` unified into `.opDone .l1Sched
          -- (.next k)`): a registry boundary of its own, so the next
          -- pool step reschedules among {parent, child, …} instead of
          -- running the parent privately to its next sync op. The
          -- `l1Sched` tag preserves the spawn boundary's exact shipped
          -- default (slot 0 = lowest-index runnable), NOT the postOp
          -- issuer-continues convention.
          return (.opDone .l1Sched (.next k),
            .exec func.body frameEnv (.frame [] [] [] [] .stop func.wrapper), s')
      | .error (.panic msg) =>
          return (.opDone .l1Sched (.next k),
            .panicking [⟨runtimeErrorValue msg, false⟩] .stop, s)
      | .error e => throw e
  -- A nil callee is gc's "go of nil func value" runtime FATAL, raised
  -- AT THE SPAWN in the spawning goroutine (probed 2026-08-07;
  -- unrecoverable, exit 2). Routed through the machine's own fatal
  -- class (triage L10, 2026-08-19) — the sync-misuse `GoError.fatal`
  -- convention, gc's fixed string after "fatal error: ". The old
  -- refusal's stated reason ("the fatal class is unmodeled this
  -- slice") expired when the class landed at spec-parity slice 2.
  | .nil => throw (.fatal "go of nil func value")
  | other => throw (.stuck s!"go callee is not a function value: {repr other}")

/-- Deliver a received value to a chan-recv STATEMENT's parked targets:
the zero-target form completes to `.next k`; targeted forms enter the
phase-1/phase-2 delivery frames (`enterRecvTargets` — targets evaluate
only AFTER the communication, spec §Assignments via BUG-022/BUG-029).
Shared verbatim by the wake step and the pairing steps. -/
def resumeRecvDelivery (s : ExecState) (v : GoValue) (ok : Bool)
    (targets : List Assignee) (env : LocalEnv) (k : Cont) :
    Except GoError (Config × ExecState) := do
  match targets with
  | [] => return (.next k, s)
  | _ :: _ =>
      enterRecvTargets s targets (recvStores v ok targets.length) (.seqn #[]) env k

/-- Deliver a received value to a parked SELECT's recv clause: commit
the clause — targets (spec step 4) then the clause body (step 5).
`commitClause`'s recv shape with the value handed off by a partner
instead of dequeued from the buffer. -/
def selectRecvDelivery (s : ExecState) (v : GoValue) (ok : Bool)
    (targets : List Assignee) (body : Stmt) (env : LocalEnv) (k : Cont) :
    Except GoError (Config × ExecState) := do
  match targets with
  | [] => return (.exec body env k, s)
  | _ :: _ =>
      enterRecvTargets s targets (recvStores v ok targets.length) body env k

/-- The WAKE step of a parked goroutine (scheduled only when
`wakeReady`): re-attempt the blocked operation against the channel
CELL. A close wakes a parked sender INTO the recoverable
"send on closed channel" panic in ITS OWN goroutine (probe p24;
`chan.go`'s wakeup path) and a parked receiver into the buffered
drain / closed-zero delivery (probe p06's rules). A parked select
wakes through `readyClauses`/`commitClause`, committing the FIRST
wake-ready clause in clause order — DETERMINISTICALLY, consuming
nothing: **no re-randomization on the blocked path** (the L2 envelope
statement at `applySelect`, slice 4; probe-pinned against gc, whose
woken select commits the case its waking event belongs to, never a
fresh shuffle). When a deferred wake finds SEVERAL clauses ready
(possible only because the wake's scheduling is itself L1 latitude —
gc would have woken at the first enabling event), the head-commit is
covered per-member: each gc first-event commit is realized here by
the prompt-wake schedule (every enabling op is a registry boundary),
and the later wake's head-commit is a spec-legal member of "any case
that can proceed". The wake-order latitude thus lives entirely at
L1/L4; the wake itself is not a choice site. Unready resumes are
`.internal` (the scheduler only picks wake-ready parked goroutines —
fail closed, never a silent no-op).

B1 (stage C): a parked op's completion is a completion — every
proceeding resume lands on `.opDone .postOp` (the select arm through
`commitClause`'s own wrap); the close-woken sender's panic is not
wrapped (B3 deferred). -/
def resumeThread (s : ExecState) : Config → Except GoError (Config × ExecState)
  | .blockedSend (some loc) v k => do
      let (buf, capacity, closed) ← chanCell s loc
      if closed then
        return (.panicking [⟨runtimeErrorValue "send on closed channel", false⟩] k, s)
      else if buf.size < capacity then do
        let s' ← storeLoc s loc (.chanData (buf.push v) capacity closed)
        return (.opDone .postOp (.next k), s')
      else throw (.internal "resume on an unready blocked send")
  | .blockedRecv (some loc) targets elem env k => do
      let (buf, capacity, closed) ← chanCell s loc
      match buf[0]? with
      | some v => do
          let s₁ ← storeLoc s loc (.chanData (buf.eraseIdx! 0) capacity closed)
          let (c', s₂) ← resumeRecvDelivery s₁ v true targets env k
          return (.opDone .postOp c', s₂)
      | none =>
          if closed then do
            let zero ← defaultValue s elem
            let (c', s₂) ← resumeRecvDelivery s zero false targets env k
            return (.opDone .postOp c', s₂)
          else throw (.internal "resume on an unready blocked receive")
  | .blockedSelect evs env k => do
      match ← readyClauses s evs with
      | [] => throw (.internal "resume on an unready blocked select")
      | cl :: _ => commitClause s env k cl
  -- Sync wakes (spec-parity slice 2): re-attempt the parked op against
  -- the CELL — scheduled only when `wakeReady`, and pick+resume happen
  -- in one pool step (no window), so the acquire must succeed; unready
  -- resumes are `.internal`, the channel arms' discipline. A woken
  -- `wlock` retires its `pendingW` registration; a woken `wgWait` its
  -- `waiters` one; a woken `onceBegin` delivers `false` (f already ran
  -- — the design note §4 Once rules).
  | .blockedSync op loc env k => do
      let p ← syncCell s loc
      match op, p with
      | .lock, .mutex locked =>
          if locked then throw (.internal "resume on an unready blocked Lock")
          else do
            let s' ← storeLoc s loc (.syncData (.mutex true))
            return (.opDone .postOp (.next k), s')
      | .wlock, .rwmutex writer readers pendingW =>
          if !writer && readers == 0 then do
            let s' ← storeLoc s loc (.syncData (.rwmutex true 0 (pendingW - 1)))
            return (.opDone .postOp (.next k), s')
          else throw (.internal "resume on an unready blocked write-Lock")
      | .rlock, .rwmutex writer readers pendingW =>
          if !writer && pendingW == 0 then do
            let s' ← storeLoc s loc (.syncData (.rwmutex writer (readers + 1) pendingW))
            return (.opDone .postOp (.next k), s')
          else throw (.internal "resume on an unready blocked RLock")
      | .wgWait, .waitGroup counter waiters =>
          if counter == 0 then do
            let s' ← storeLoc s loc (.syncData (.waitGroup counter (waiters - 1)))
            return (.opDone .postOp (.next k), s')
          else throw (.internal "resume on an unready blocked Wait")
      | .onceBegin targets, .once started done =>
          if started && done then do
            let (c', s₂) ← enterRecvTargets s targets [.bool false] (.seqn #[]) env k
            return (.opDone .postOp c', s₂)
          else throw (.internal "resume on an unready blocked Once.Do")
      | _, _ => throw (.internal "blocked sync op / cell shape mismatch")
  | _ => throw (.internal "resume on a non-blocked configuration")

/-- A pairing partner for the arrival intercept: a parked chan-op
goroutine, or a parked select's specific clause. -/
inductive PairTarget where
  | opWaiter (j : Nat)
  | selectWaiter (j : Nat) (ci : Nat)
  deriving Repr, BEq

/-- Parked RECEIVE-side waiters on channel `loc` (goroutine order,
clause order within a select): blocked chan-recv statements and parked
selects with a recv clause on `loc`. `i` (the arriving goroutine) is
excluded. -/
def recvSideWaiters (threads : Array Config) (i : Nat) (loc : Loc) :
    List (Nat × PairTarget) :=
  (List.range threads.size).flatMap fun (j : Nat) =>
    if j == i then [] else
    match threads[j]? with
    | some (.blockedRecv (some loc') _ _ _ _) =>
        if loc' == loc then [(0, .opWaiter j)] else []
    | some (.blockedSelect evs _ _) =>
        (List.range evs.length).filterMap fun (ci : Nat) =>
          (match evs[ci]? with
          | some (.recvEv chv _ _ _) =>
              if chanValueLoc chv == some loc then some (0, .selectWaiter j ci)
              else none
          | _ => none : Option (Nat × PairTarget))
    | _ => []

/-- Parked SEND-side waiters on channel `loc` (goroutine order, clause
order within a select). -/
def sendSideWaiters (threads : Array Config) (i : Nat) (loc : Loc) :
    List (Nat × PairTarget) :=
  (List.range threads.size).flatMap fun (j : Nat) =>
    if j == i then [] else
    match threads[j]? with
    | some (.blockedSend (some loc') _ _) =>
        if loc' == loc then [(0, .opWaiter j)] else []
    | some (.blockedSelect evs _ _) =>
        (List.range evs.length).filterMap fun (ci : Nat) =>
          (match evs[ci]? with
          | some (.sendEv chv _ _ _) =>
              if chanValueLoc chv == some loc then some (0, .selectWaiter j ci)
              else none
          | _ => none : Option (Nat × PairTarget))
    | _ => []

/-- Is this candidate a parked SELECT clause? (Select-with-select
rendezvous is refused this slice.) -/
def PairTarget.isSelect : PairTarget → Bool
  | .selectWaiter _ _ => true
  | _ => false

/-- The parked partner a pairing candidate names. -/
def PairTarget.partnerIdx : PairTarget → Nat
  | .opWaiter j => j
  | .selectWaiter j _ => j

/-- The completed select-apply positions (`spawnPlan`'s extraction
mold): operands evaluated, ready for the readiness/commit apply.
`stepThread`'s cell path intercepts exactly these (Q2: the apply's
emitted commit identity reaches the step event); every other shape
steps by `stepFn`. -/
def selectApplyPlan : Config →
    Option (GoValue × List (SelectClauseHead × Stmt) × Option Stmt
      × List GoValue × LocalEnv × Cont)
  | .retV v (.selectOpsK clauses default? done [] env k) =>
      some (v, clauses, default?, done, env, k)
  | _ => none

/-! ## The cross-goroutine delete-prune (E9 closure, 2026-09-02)

`mapDelete`/`clearMap` prune the deleted key(s) out of every in-flight
`mapIterK` frame over the same map (`contAfterStmtOp`, BUG-005 (L)) —
but `stepFn` sees ONE goroutine's continuation, so until this slice the
prune reached only the DELETING goroutine's frames. A DRF
cross-goroutine delete (goroutine B deletes-then-re-creates key `k`
mid-range, handshake-ordered against ranging goroutine A's picks) left
A's `produced`/`start` sets unpruned, so the spec-permitted
re-production of the re-created key (a NEW entry under I-1 / L-012) was
unrealizable: permitted ∉ modeled on a DRF program (fidelity finding
A1-20; inventory E9 REOPEN → CLOSED here). gc EXHIBITS the member:
with ONE fresh insert between the delete and the re-create, the
re-created key is produced twice in ~87% of runs on a 3-key map (a
slot-placement effect of gc's swiss map; evidence dir
`docs/evidence/2026-09-02_e9-cross-goroutine-prune/`).

The pool-level extension: at a `mapDelete`/`clearMap` APPLY that
PROCEEDS (successor `.next _`), `pruneForeign` walks every OTHER
goroutine's configuration and applies the same `contAfterStmtOp` prune
to its continuation. No new state, no new frame shape, no per-map
registry — the deleting goroutine's own continuation is pruned inside
`stepFn` exactly as before (`stepThread_single` still equates the
one-thread pool with `stepFn`). Fail-closed: the walk is
`Except`-monadic (an ill-formed key comparison in a FOREIGN frame
refuses the step, naming its cause AND its foreignness —
`foreignPruneError` prefixes the refusal with the goroutine index, so
it is never mistaken for the deleter's own prune refusing; same
constructor in, same constructor out, audit fix round F7),
`Config.mapContM` enumerates every configuration constructor (no
wildcard), and an apply successor of unexpected shape is an
`.internal` refusal, never a silent skip. Racy variants (no handshake)
are still refused by the detector (the pick-time load vs the delete's
write, HB-unordered) — the prune touches no memory and emits no event.

THREAD-LOCALITY (the argument NPDRF.lean's obstruction 7 cites): with
this walk a `thread` step is no longer thread-local — it rewrites every
other goroutine's continuation, and that rewrite appears in no
`stepAccesses` footprint (the prune reads and writes no heap cell). The
saving argument: the rewrite only changes a foreign `mapIterK` frame's
`produced`/`start` sets, which are consulted ONLY at that frame's next
pick — and every pick (including the final done-check) loads the live
map cell (`Race.lean`, the `.next (.mapIterK …)` arm of `stepAccesses`),
while the pruning op WRITES that cell. So any foreign step that could
observe the prune conflicts with the pruning step at the cell and is
either HB-ordered after it (the observation is then order-independent:
the prune is a function of the post-apply state and the frame, applied
before the frame's next pick on every schedule) or HB-unordered — a
data race, refused. On race-free programs the reordering window in
which the prune's timing could be observed is therefore empty; the
mover route must carry this as a side condition rather than read it
off the footprint table.

COST (recorded at the audit, F8; no before/after measurement taken): a
pruning-op apply is O(threads × continuation depth) — `Config.mapContM`
walks every other goroutine's whole continuation on every
`mapDelete`/`clearMap` apply that proceeded, pruning or not. A
2-goroutine TWO-ranger shape (both goroutines ranging while one
deletes) did not enumerate at `backedge=full` within 10 min at the
audit (it completes at `backedge=0` in ~1 min); the corpus rows are
single-ranger shapes. Whether the walk or the enumeration tree itself
is the cost is unmeasured.
-/

/-- The PRUNING-op apply shape: a `mapDelete`/`clearMap` statement op
with its last operand arriving (`pending = []`). Returns the op and
the operand list `stepFn`'s apply arm hands `applyStmtOp` and
`contAfterStmtOp`. Every other shape — including every other op's
apply — is `none`, so the foreign walk runs ONLY at pruning ops. -/
def mapPrunePlan : Config → Option (StmtOp × List GoValue)
  | .retV v (.stmtOpK op _ done [] _ _) =>
      match op with
      | .mapDelete keyTy => some (.mapDelete keyTy, (v :: done).reverse)
      | .clearMap => some (.clearMap, (v :: done).reverse)
      | _ => none
  | _ => none

/-- Apply a continuation rewrite to a configuration's continuation(s).
Every constructor is enumerated (a new `Config` shape must be placed
here explicitly); `.panicked` carries no continuation; `.opDone`
recurses into its inner configuration. -/
def Config.mapContM (f : Cont → Except GoError Cont) : Config → Except GoError Config
  | .exec stmt env k => do return .exec stmt env (← f k)
  | .evalE e env k => do return .evalE e env (← f k)
  | .retV v k => do return .retV v (← f k)
  | .next k => do return .next (← f k)
  | .breaking k => do return .breaking (← f k)
  | .continuing k => do return .continuing (← f k)
  | .returning k => do return .returning (← f k)
  | .breakingTo label k => do return .breakingTo label (← f k)
  | .continuingTo label k => do return .continuingTo label (← f k)
  | .panicking chain k => do return .panicking chain (← f k)
  | .panicked msg => return .panicked msg
  | .blockedSend ch v k => do return .blockedSend ch v (← f k)
  | .blockedRecv ch targets elem env k => do return .blockedRecv ch targets elem env (← f k)
  | .blockedSelect clauses env k => do return .blockedSelect clauses env (← f k)
  | .opDone sched inner => do return .opDone sched (← Config.mapContM f inner)
  | .blockedSync op loc env k => do return .blockedSync op loc env (← f k)

/-- Name a foreign-frame refusal's provenance (audit fix round F7). The
deleter's own prune inside `stepFn` and the foreign walk share
`contAfterStmtOp`, so without this a refusal raised while pruning
goroutine `j`'s frame would read exactly like one raised by the
deleter's own. Only the REFUSAL classes are prefixed (`.internal` /
`.stuck` / `.unsupported` — their message is diagnostic text); every
other constructor passes through UNCHANGED: a `.panic` message is
PROGRAM output (Go's `panic:` line) and is never rewritten, `.fatal`
likewise carries Go's own text, and the nullary classes have no message
to name. Same constructor in, same constructor out — no outcome
classification moves. Every constructor is enumerated (no wildcard). -/
def foreignPruneError (j : Nat) : GoError → GoError
  | .internal m => .internal (s!"foreign delete-prune: goroutine {j}'s frame refused: {m}")
  | .stuck m => .stuck (s!"foreign delete-prune: goroutine {j}'s frame refused: {m}")
  | .unsupported f => .unsupported (s!"foreign delete-prune: goroutine {j}'s frame refused: {f}")
  | .panic m => .panic m
  | .fatal m => .fatal m
  | .fuelOut => .fuelOut
  | .deadlock => .deadlock
  | .raceDetected => .raceDetected

/-- One thread of the foreign walk: thread `j` is left alone when it is
the deleter `i` (its own continuation was pruned inside `stepFn`),
otherwise its continuation is pruned; a refusal raised by `j`'s frame
is re-thrown naming `j` (`foreignPruneError`). -/
def pruneForeignOne (s : ExecState) (op : StmtOp) (vs : List GoValue) (i j : Nat)
    (c : Config) : Except GoError Config :=
  if j = i then pure c else
    match Config.mapContM (contAfterStmtOp s op vs) c with
    | .ok c' => .ok c'
    | .error e => .error (foreignPruneError j e)

/-- The foreign walk over a thread list; `j` is the index of the list
head. -/
def pruneForeignList (s : ExecState) (op : StmtOp) (vs : List GoValue) (i : Nat) :
    Nat → List Config → Except GoError (List Config)
  | _, [] => return []
  | j, c :: rest => do
      let c' ← pruneForeignOne s op vs i j c
      let rest' ← pruneForeignList s op vs i (j + 1) rest
      return c' :: rest'

/-- The cross-goroutine prune at one pool step: `c` is goroutine `i`'s
PRE-step configuration, `c'` its successor, `ts` the pool after `i`'s
own update. At a pruning-op apply that PROCEEDED (`.next _`) every
other goroutine's continuation is pruned with the POST-apply state `s`
(key comparison consults `types` only). A pruning-op apply that did
not proceed (`.panicking` — the delete never happened; e.g. an
unhashable interface key) leaves the pool untouched; any other
successor shape at a pruning-op apply is impossible by `stepFn`'s arm
and REFUSES (`.internal`) rather than silently skipping. Every
non-pruning shape is the identity. -/
def pruneForeign (s : ExecState) (i : Nat) (c c' : Config) (ts : Array Config) :
    Except GoError (Array Config) :=
  match mapPrunePlan c with
  | none => return ts
  | some (op, vs) =>
      match c' with
      | .next _ => do return (← pruneForeignList s op vs i 0 ts.toList).toArray
      | .panicking _ _ => return ts
      | _ => throw (.internal "foreign delete-prune: pruning-op apply with an unexpected successor shape")

/-- The foreign prune is the identity at every non-pruning shape. -/
theorem pruneForeign_of_plan_none {s : ExecState} {i : Nat} {c c' : Config}
    {ts : Array Config} (h : mapPrunePlan c = none) :
    pruneForeign s i c c' ts = .ok ts := by
  unfold pruneForeign
  rw [h]
  rfl

/-- A pruning-op apply shape, inverted. -/
theorem mapPrunePlan_some_shape {c : Config} {op : StmtOp} {vs : List GoValue}
    (h : mapPrunePlan c = some (op, vs)) :
    ∃ v nt done env k, c = .retV v (.stmtOpK op nt done [] env k)
      ∧ vs = (v :: done).reverse := by
  unfold mapPrunePlan at h
  split at h
  · rename_i v op₀ nt done env k
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v, nt, done, env, k, rfl, rfl⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v, nt, done, env, k, rfl, rfl⟩
    · cases h
  · cases h

/-- A spawn position is never a pruning-op apply. -/
theorem mapPrunePlan_of_spawnPlan {c : Config} {p : GoValue × List GoValue × Cont}
    (h : spawnPlan c = some p) : mapPrunePlan c = none := by
  unfold spawnPlan at h
  split at h <;> first | rfl | cases h

/-- The foreign walk over a ONE-thread pool is the identity (the only
thread is the deleter, skipped), provided the successor is one of the
two shapes `stepFn`'s apply arm produces. -/
theorem pruneForeign_singleton {s : ExecState} {c c' x : Config}
    (hc' : ∀ op vs, mapPrunePlan c = some (op, vs) →
      (∃ k, c' = .next k) ∨ (∃ chain k, c' = .panicking chain k)) :
    pruneForeign s 0 c c' #[x] = .ok #[x] := by
  unfold pruneForeign
  cases hmp : mapPrunePlan c with
  | none => rfl
  | some p =>
    obtain ⟨op, vs⟩ := p
    rcases hc' op vs hmp with ⟨k, rfl⟩ | ⟨chain, k, rfl⟩
    · simp [pruneForeignList, pruneForeignOne] <;> rfl
    · rfl

/-! ## The step-event channel (W3.2 slice 1 stage B — audit Q2)

What one pool step DID — EMITTED by the step, never reconstructed from
it. This is what deletes the detector's parallel classification: the
old `raceUpdate` recovered the pairing partner by DIFFING pre/post
pools (`wokenPartner`, deleted) and recovered the committed select
clause by REPLAYING the step's stream consumption (three consumption
re-derivations in lockstep by review alone — audit O-2/C-4); both now
arrive in the event.

Scope (stage B, recorded deviation from the boundary note §3): the
event channel lives at the POOL layer. `stepFn`'s signature is
UNCHANGED — the note's `stepFn : … × List PickRecord` reshape would
re-state the entire sequential correspondence + gallery surface
(hundreds of pinned 3-tuple equations in `MachineSound`, `StepKit`,
and ~40 example files), far beyond this stage's re-proof budget, and
no stage-B consumer needs the apply-layer picks: the detector gets
the select-commit identity from `applySelect`'s emitted 4th component
(the pool's select interception in `stepThread`), fairness quantifies
SCHEDULING picks (all pool-layer), and the enumerator's widths ride
`stepNeeds`. Consequently `StepEvent.picks` carries the POOL-layer
consumption (`l1Sched`, `l2Arrival`, `l4Waiter`); the apply-layer
data picks (`mapIter`, `appendSpill`, `l2Entry`) are not in the event
stream. Re-open trigger: a consumer that needs the full labeled
sequential trace (e.g. S6a's rule-label runtime counterpart) — then
the `stepFn` reshape lands with its own budget. Stages C/D add the
`postOp`/`backEdge` scheduling picks here when the boundary set
widens (G1). -/

/-- The action classification of one pool step (the note's
`StepAction`, instantiated at the machine's real types: the note's
`chanCell`/`syncEv` fine-grained arms are folded into `privateStep` —
the detector's chan/sync cell-path FOOTPRINT classification stays
derived from the pre-configuration per the footprint-table-not-
autologging decision (Race.lean:26-53); what the event kills is the
pool diffing and the stream replay, not the footprint table). -/
inductive StepAction where
  /-- `spawnStep` ran; `child` is the new goroutine's pool index. -/
  | spawned (child : Nat)
  /-- `resumeThread` ran: a parked goroutine's op completed (the
  woken shape is the pre-configuration at `who`). -/
  | woke
  /-- The arrival intercept paired the issuer with parked partner
  `partner` (kills `wokenPartner`). -/
  | paired (partner : Nat)
  /-- A select clause committed against the cell — the entry-path
  apply (singleton or L2-picked) or the arrival-path `.commit`; the
  clause is the apply's EMITTED commit identity (kills the
  detector's readiness/stream replay). -/
  | selectCommit (cl : EvClause)
  /-- A select apply that committed nothing: default taken or
  parked. -/
  | selectPass
  /-- The completion-marker strip (stage C, `.opDone` — generalizing
  BUG-040's post-spawn marker) — a pure control step, no footprint. -/
  | opDoneStrip
  /-- Any other `stepFn` step: chan/sync cell-path applies, parks,
  and private steps — the detector classifies the footprint from the
  pre-configuration as before. -/
  | privateStep

/-- One pool step's event (Q2): who ran, what the step did, and the
POOL-layer picks it consumed, in order (scope note above). -/
structure StepEvent where
  who : Nat
  action : StepAction
  picks : List PickRecord

/-- The per-clause channel of a select's evaluated entry operands,
extracted TOTALLY (no exceptions): `(isSend, loc)` per clause, `none`
for nil channels / non-channel garbage, and `none` OVERALL on an
arity mismatch (the fallible `evalClauses` path then reports the
authoritative error through `stepFn`). The pure waiter-existence
pre-scan runs on this, so a select with no parked partners — in
particular every single-goroutine select — never touches a fallible
helper before `stepFn` (what keeps `stepThread_single` literal). -/
def selectClauseChans : List (SelectClauseHead × Stmt) → List GoValue →
    Option (List (Option (Bool × Loc)))
  | [], [] => some []
  | (.send _ _ _, _) :: rest, chv :: _vv :: vs =>
      (selectClauseChans rest vs).map fun tl =>
        (match chanValueLoc chv with
          | some l => some (true, l)
          | none => none) :: tl
  | (.recv _ _ _, _) :: rest, chv :: vs =>
      (selectClauseChans rest vs).map fun tl =>
        (match chanValueLoc chv with
          | some l => some (false, l)
          | none => none) :: tl
  | _, _ => none

/-- **THE ARRIVAL PLAN — gc's waiter-queue-priority, modeled** (S2
audit response, major finding: `chansend` dequeues `recvq` BEFORE
testing buffer room, and `chanrecv` dequeues `sendq` before draining
the buffer — chan.go's L17-18 invariants). A channel/select op at its
apply position consults PARKED PARTNERS FIRST; only a partnerless op
falls through to the cell-based `stepFn` step. `none` = no pairing
(cell path); `some (bc, cands)` = pair the op (as its would-block
shape `bc`) with one of `cands`.

THE L4 ENVELOPE SITE (design D4; ground-truth §6 row L4): the spec has
NO text on which of several matching parked waiters pairs with an
arriving operation (gc's FIFO wakeup is one legal point, membership
territory), so the envelope is "ANY matching waiter"; when more than
one candidate matches, the pick is drawn from the choice stream,
bounded by the candidate count and consumed ONLY then (`stepThread`).
Width metadata for the enumerator/membership lane: the site's bound is
the number of matched parked waiters (select clauses counted
individually). Candidates are `(arriving-clause-index, target)`; for
chan-op arrivals the first component is 0 and unused.

Order of checks, per gc: a send on a CLOSED channel panics before any
dequeue (cell path); a receive on a closed channel drains/zeroes (cell
path — gc's close empties `sendq` synchronously; our transiently
still-parked senders wake into their panics separately, an equivalent
schedule). The pure waiter scans run FIRST and the cell/fallible
helpers only when a waiter matched, so a partnerless arrival — in
particular every single-goroutine op — is a pure no-op here
(`arrivalPlan_singleton`, the conservation theorem's hinge).

SELECT readiness is waiter-EXTENDED here (S2 audit, second major: a
select with `default` must see parked partners — gc's `selectgo`
consults the sudog queues): a clause is ready when cell-ready OR a
parked partner matches. No ready clause → `.cellPath` (`stepFn`:
default or park). Exactly one ready clause: waiter-matched →
`.single` pair (a clause both cell- and waiter-ready pairs, preserving
gc's dequeue-first refill semantics); cell-only → `.cellPath`
(`applySelect` commits the same single clause). Two or more ready
clauses (slice 4 — the L2 envelope LIVE; statement at `applySelect`):
with a waiter involved → `.multi`, one outcome per ready clause in
clause order — the L2 pick chooses the CLAUSE (drawn by
`arrivalPlan`, bound = ready count), and the chosen clause then
either pairs (its L4 waiter pick follows, in `stepThread`) or commits
against the cell (`.commit` — performed at the pool level, since
`applySelect`'s cell bound differs from the waiter-extended one);
with no waiter involved → `.cellPath` (`applySelect`'s own L2 pick,
same bound by construction). Select-with-select rendezvous stays
fail-closed.

Invariant asserts (fail closed, never a silent wrong order): a matched
recv-side waiter beside a NONEMPTY buffer is an hchan-invariant breach
(`applyPairing` refuses `.internal` rather than jumping the queue). -/
def chanArrivalPlan (s : ExecState) (threads : Array Config) (i : Nat)
    (op : ChanStOp) (vs : List GoValue) (env : LocalEnv) (k : Cont) :
    Except GoError (Option (Config × List (Nat × PairTarget))) := do
  match op, vs with
  | .send elem, [chv, vv] =>
      match chanValueLoc chv with
      | none => return none
      | some loc =>
          let ws := recvSideWaiters threads i loc
          if ws.isEmpty then return none
          else do
            let (_, _, closed) ← chanCell s loc
            if closed then return none  -- send on closed: panic (cell path)
            else do
              let v' ← normalizeValueForTy s elem vv
              return some (.blockedSend (some loc) v' k, ws)
  | .recv targets elem, [chv] =>
      match chanValueLoc chv with
      | none => return none
      | some loc =>
          let ws := sendSideWaiters threads i loc
          if ws.isEmpty then return none
          else do
            let (_, _, closed) ← chanCell s loc
            if closed then return none  -- drain/zero (cell path)
            else return some (.blockedRecv (some loc) targets elem env k, ws)
  | _, _ => return none

/-- Pure waiter-existence pre-scan over a select's clause channels
(the fallible readiness analysis runs only when this is true — which
keeps a partnerless select, in particular every single-goroutine
select, a pure no-op in the arrival plan). -/
def sidesHaveWaiters (threads : Array Config) (i : Nat) :
    List (Option (Bool × Loc)) → Bool
  | [] => false
  | none :: rest => sidesHaveWaiters threads i rest
  | some (isSend, loc) :: rest =>
      !(if isSend then recvSideWaiters threads i loc
        else sendSideWaiters threads i loc).isEmpty
      || sidesHaveWaiters threads i rest

/-- One resolved arrival outcome: PAIR the arriving op (as its
would-block shape `bc`) with one of the matched parked waiters
(`cands` — the L4 pick), or COMMIT a specific clause against the cell
(the select-arrival case where the L2-picked clause is cell-only
ready: `applySelect` cannot perform that commit, because its
cell-readiness bound differs from the waiter-extended ready set the
L2 pick was drawn over). -/
inductive ArrivalOutcome where
  | pair (bc : Config) (cands : List (Nat × PairTarget))
  | commit (cl : EvClause) (env : LocalEnv) (k : Cont)

/-- The PURE arrival analysis (stream-free — the relation's carrier;
`arrivalPlan` is its consuming wrapper):
* `.cellPath` — no waiter involvement: the op falls through to the
  sequential `stepFn`/`applySelect` semantics (including
  `applySelect`'s OWN L2 pick for a pure-cell multi-ready select —
  whose bound then equals the waiter-extended one by construction).
* `.single bc cands` — exactly one ready clause/op, waiter-matched: no
  L2 pick; the pairing is the only outcome (a singleton-ready
  cell-only clause is `.cellPath`, so `.single` is always a PAIR — the
  constructor carries it directly, making a single-commit
  unrepresentable).
* `.multi os` — a select arrival with ≥ 2 waiter-extended-ready
  clauses, at least one waiter-matched: **the L2 site on the arrival
  path** — one outcome per ready clause in clause order, the pick
  drawn by `arrivalPlan` (bound `os.length`, the envelope statement
  at `applySelect`). Chan-op arrivals never produce `.multi`. -/
inductive ArrivalAnalysis where
  | cellPath
  | single (bc : Config) (cands : List (Nat × PairTarget))
  | multi (os : List ArrivalOutcome)

@[inherit_doc chanArrivalPlan]
def selectArrivalCases (s : ExecState) (threads : Array Config) (i : Nat)
    (clauses : List (SelectClauseHead × Stmt)) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) :
    Except GoError ArrivalAnalysis := do
  match selectClauseChans clauses vs with
  | none => return .cellPath
  | some sides =>
      -- pure waiter-existence pre-scan
      if !sidesHaveWaiters threads i sides then return .cellPath
      else do
        let evs ← evalClauses clauses vs
        -- per-clause: cell readiness and waiter candidates
        let readiness : List (Nat × Bool × List (Nat × PairTarget)) ←
          (List.range evs.length).mapM fun (ci : Nat) => do
            match evs[ci]? with
            | some cl => do
                let cell ← clauseReady s cl
                -- A clause on a CLOSED channel never pairs (S2 convergence
                -- round, critical): gc checks closed BEFORE any waiter
                -- dequeue — chansend panics on closed unconditionally and
                -- chanrecv dequeues sendq only when open — so the clause's
                -- waiter list is zeroed and, being cell-ready (closed ⇒
                -- ready in both directions), it takes the cell-commit
                -- semantics (send panics, recv drains/zeroes, parked
                -- senders are left for their close-wake panic) whether it
                -- commits via `applySelect` or via an L2-picked
                -- `.commit`. Mirrors `chanArrivalPlan`'s closed guards.
                let ws ←
                  match cl with
                  | .recvEv chv _ _ _ =>
                      match chanValueLoc chv with
                      | some loc => do
                          let (_, _, closed) ← chanCell s loc
                          if closed then pure ([] : List (Nat × PairTarget))
                          else pure (sendSideWaiters threads i loc)
                      | none => pure []
                  | .sendEv chv _ _ _ =>
                      match chanValueLoc chv with
                      | some loc => do
                          let (_, _, closed) ← chanCell s loc
                          if closed then pure ([] : List (Nat × PairTarget))
                          else pure (recvSideWaiters threads i loc)
                      | none => pure []
                return (ci, cell, ws)
            | none => return (ci, false, [])
        -- One outcome per waiter-extended-ready clause, clause order.
        let mkOutcome : Nat × Bool × List (Nat × PairTarget) →
            Except GoError ArrivalOutcome := fun (ci, _, ws) =>
          if ws.isEmpty then
            match evs[ci]? with
            | some cl => return .commit cl env k
            | none => throw (.internal "select ready-clause index out of range")
          else if ws.any (fun w => w.2.isSelect) then
            throw (.unsupported
              "select-with-select rendezvous (unmodeled this slice)")
          else
            return .pair (.blockedSelect evs env k) (ws.map fun w => (ci, w.2))
        match readiness.filter (fun r => r.2.1 || !r.2.2.isEmpty) with
        | [] => return .cellPath
        | [(ci, _cell, ws)] =>
            if ws.isEmpty then return .cellPath  -- cell-only: applySelect commits it
            else if ws.any (fun w => w.2.isSelect) then
              throw (.unsupported
                "select-with-select rendezvous (unmodeled this slice)")
            else
              return .single (.blockedSelect evs env k) (ws.map fun w => (ci, w.2))
        | ready =>
            if ready.all (fun r => r.2.2.isEmpty) then
              -- Pure cell multi-ready: `applySelect`'s own L2 pick — and
              -- its bound (|cell-ready|) EQUALS |ready| here (every
              -- waiter-carrying clause is ready, so all-empty-ws means
              -- ready is exactly the cell-ready set): one consumption,
              -- one bound, either path.
              return .cellPath
            else do
              return .multi (← ready.mapM mkOutcome)

@[inherit_doc chanArrivalPlan]
def arrivalCases (s : ExecState) (threads : Array Config) (i : Nat) :
    Config → Except GoError ArrivalAnalysis
  | .retV v (.chanStK op done [] env k) => do
      match ← chanArrivalPlan s threads i op ((v :: done).reverse) env k with
      | none => return .cellPath
      | some (bc, cs) => return .single bc cs
  | .retV v (.selectOpsK clauses _default? done [] env k) =>
      selectArrivalCases s threads i clauses ((v :: done).reverse) env k
  | _ => return .cellPath

/-- The consuming wrapper over `arrivalCases`: draws the L2 clause pick
at a `.multi` analysis (bound = the ready count; consumed ONLY then —
`.cellPath`/`.single` return the stream untouched, which is what keeps
partnerless and singleton arrivals stream-transparent and sequential
conservation literal). Q2: the pick rides out as its `PickRecord`
(empty on the non-consuming analyses) for the step event. -/
def arrivalPlan (s : ExecState) (threads : Array Config) (i : Nat)
    (c : Config) (ch : Choices) :
    Except GoError (Option ArrivalOutcome × Choices × List PickRecord) := do
  match ← arrivalCases s threads i c with
  | .cellPath => return (none, ch, [])
  | .single bc cands => return (some (.pair bc cands), ch, [])
  | .multi os =>
      -- `ChoiceSite.l2Arrival` (the census row): bound = the ready
      -- count, ≥ 2 by construction of `.multi`.
      let (idx, ch', ps) := Choices.consumeAtE .l2Arrival os.length ch
      match os[idx]? with
      | some o => return (some o, ch', ps)
      | none => throw (.internal "select L2 ready pick out of range")

/-- Perform ONE pairing: the arriving goroutine `i` (whose op takes
its would-block shape `bc`) pairs with the chosen candidate. Two
shapes, both gc's:
- **direct handoff** (`send()`): buffer EMPTY — the value teleports,
  both goroutines proceed, the buffer untouched;
- **head-and-refill** (`recv()`): an arriving/committing RECEIVE
  against a parked SENDER with a NONEMPTY (necessarily full) buffer
  takes the buffer HEAD and enqueues the parked sender's value at the
  tail in the same step — FIFO through pressure, len unchanged (the
  S2 audit's too-narrow finding: without the refill, gc's
  len-preserving observation was unreachable).
A matched RECV-SIDE waiter beside a nonempty buffer is an
hchan-invariant breach: fail closed (`.internal`), never a
queue-jumping delivery. Shape mismatches are `.internal` (the
candidates were just scanned).

B1 (stage C): the pairing ISSUER's successor (index `i`) is wrapped
in `.opDone .postOp` — the issuer's op just completed. The passive
PARTNER (index `j`) is NOT wrapped: its delivery is part of the
issuer's step, and it becomes schedulable at the issuer's very next
boundary — the `.opDone` this rule just created — so wrapping it
would add a no-op step and no latitude (boundary-set note §2 B1). -/
def applyPairing (s : ExecState) (threads : Array Config) (i : Nat)
    (bc : Config) (cand : Nat × PairTarget) :
    Except GoError (Array Config × ExecState) := do
  match bc, cand.2 with
  | .blockedSend (some loc) v k, .opWaiter j =>
      match threads[j]? with
      | some (.blockedRecv _ targets _ envr kr) => do
          let (buf, _, _) ← chanCell s loc
          if buf.isEmpty then do
            let (cr, s') ← resumeRecvDelivery s v true targets envr kr
            return ((threads.setIfInBounds i (.opDone .postOp (.next k))).setIfInBounds j cr, s')
          else throw (.internal
            "parked receiver beside a nonempty buffer (hchan invariant breach)")
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedSend (some loc) v k, .selectWaiter j ci =>
      match threads[j]? with
      | some (.blockedSelect evs envs ks) =>
          match evs[ci]? with
          | some (.recvEv _ targets _ body) => do
              let (buf, _, _) ← chanCell s loc
              if buf.isEmpty then do
                let (cs', s') ← selectRecvDelivery s v true targets body envs ks
                return ((threads.setIfInBounds i (.opDone .postOp (.next k))).setIfInBounds j cs', s')
              else throw (.internal
                "parked select receiver beside a nonempty buffer (hchan invariant breach)")
          | _ => throw (.internal "pairing partner clause mismatch")
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedRecv (some loc) targets _ env k, .opWaiter j =>
      match threads[j]? with
      | some (.blockedSend _ vs ks) => do
          let (buf, capacity, closed) ← chanCell s loc
          match buf[0]? with
          | none => do
              -- empty (capacity 0): direct handoff
              let (cr, s') ← resumeRecvDelivery s vs true targets env k
              return ((threads.setIfInBounds i (.opDone .postOp cr)).setIfInBounds j (.next ks), s')
          | some hd => do
              -- gc recv(): head out, parked sender's value in at the tail
              let s₁ ← storeLoc s loc
                (.chanData ((buf.eraseIdx! 0).push vs) capacity closed)
              let (cr, s') ← resumeRecvDelivery s₁ hd true targets env k
              return ((threads.setIfInBounds i (.opDone .postOp cr)).setIfInBounds j (.next ks), s')
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedRecv (some loc) targets _ env k, .selectWaiter j ci =>
      match threads[j]? with
      | some (.blockedSelect evs envs ks) =>
          match evs[ci]? with
          | some (.sendEv _ vv selem body) => do
              -- the select's send value normalizes at the element type at
              -- COMMIT (commitClause's discipline)
              let v' ← normalizeValueForTy s selem vv
              let (buf, capacity, closed) ← chanCell s loc
              match buf[0]? with
              | none => do
                  let (cr, s') ← resumeRecvDelivery s v' true targets env k
                  return ((threads.setIfInBounds i (.opDone .postOp cr)).setIfInBounds j
                    (.exec body envs ks), s')
              | some hd => do
                  let s₁ ← storeLoc s loc
                    (.chanData ((buf.eraseIdx! 0).push v') capacity closed)
                  let (cr, s') ← resumeRecvDelivery s₁ hd true targets env k
                  return ((threads.setIfInBounds i (.opDone .postOp cr)).setIfInBounds j
                    (.exec body envs ks), s')
          | _ => throw (.internal "pairing partner clause mismatch")
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedSelect evs env k, tgt =>
      match evs[cand.1]? with
      | some (.recvEv chv targets _ body) =>
          match tgt with
          | .opWaiter j =>
              match threads[j]? with
              | some (.blockedSend _ vs ks) => do
                  match chanValueLoc chv with
                  | none => throw (.internal "pairing clause channel mismatch")
                  | some loc => do
                      let (buf, capacity, closed) ← chanCell s loc
                      match buf[0]? with
                      | none => do
                          let (ci', s') ← selectRecvDelivery s vs true targets body env k
                          return ((threads.setIfInBounds i (.opDone .postOp ci')).setIfInBounds j
                            (.next ks), s')
                      | some hd => do
                          let s₁ ← storeLoc s loc
                            (.chanData ((buf.eraseIdx! 0).push vs) capacity closed)
                          let (ci', s') ← selectRecvDelivery s₁ hd true targets body env k
                          return ((threads.setIfInBounds i (.opDone .postOp ci')).setIfInBounds j
                            (.next ks), s')
              | _ => throw (.internal "pairing partner shape mismatch")
          | .selectWaiter _ _ => throw (.internal
              "select-with-select pairing reached applyPairing (refused upstream)")
      | some (.sendEv chv vv selem body) =>
          match tgt with
          | .opWaiter j =>
              match threads[j]? with
              | some (.blockedRecv _ targetsr _ envr kr) => do
                  match chanValueLoc chv with
                  | none => throw (.internal "pairing clause channel mismatch")
                  | some loc => do
                      let (buf, _, _) ← chanCell s loc
                      if buf.isEmpty then do
                        let v' ← normalizeValueForTy s selem vv
                        let (cr, s') ← resumeRecvDelivery s v' true targetsr envr kr
                        return ((threads.setIfInBounds i (.opDone .postOp (.exec body env k))).setIfInBounds j cr, s')
                      else throw (.internal
                        "parked receiver beside a nonempty buffer (hchan invariant breach)")
              | _ => throw (.internal "pairing partner shape mismatch")
          | .selectWaiter _ _ => throw (.internal
              "select-with-select pairing reached applyPairing (refused upstream)")
      | none => throw (.internal "pairing arriving-clause index out of range")
  | _, _ => throw (.internal "pairing on a non-blocked configuration")

/-- One step of goroutine `i` in the pool: a parked goroutine WAKES
(`resumeThread`); the completion marker STRIPS to its inner
configuration (stage C, generalizing BUG-040's post-spawn strip — the
op's own boundary, where any runnable goroutine may have preempted);
a completed spawn position FORKS (`spawnStep`,
appending the child — stable ids); a channel/select apply position
consults PARKED PARTNERS FIRST (`arrivalPlan` — gc's waiter-queue
priority; the L4 pick is consumed ONLY when more than one candidate
matches); everything else — including every partnerless op — steps by
the sequential `stepFn`, a blocked outcome simply parking (partners
were already ruled out by the plan). -/
def stepThread (s : ExecState) (threads : Array Config) (i : Nat)
    (ch : Choices) :
    Except GoError (Array Config × ExecState × Choices × StepEvent) := do
  match threads[i]? with
  | none => throw (.internal "thread index out of range")
  | some c =>
    if isBlockedConfig c then do
      let (c', s') ← resumeThread s c
      return (threads.setIfInBounds i c', s', ch, ⟨i, .woke, []⟩)
    else
      match opDoneInner c with
      | some inner =>
          -- The completion-marker strip (stage C, generalizing
          -- BUG-040's spawn marker): one goroutine-step, consuming
          -- nothing (the scheduling decision the marker exists for was
          -- taken by `stepMulti`'s site consultation at this
          -- boundary). Identical to `stepFn`'s `.opDone` arm — the
          -- dedicated arm exists so the step event says
          -- `.opDoneStrip` and no waiter scan runs on a marker.
          return (threads.setIfInBounds i inner, s, ch,
            ⟨i, .opDoneStrip, []⟩)
      | none =>
      match spawnPlan c with
      | some (cv, args, k) => do
          let (parent', child, s') ← spawnStep s cv args k
          return ((threads.setIfInBounds i parent').push child, s', ch,
            ⟨i, .spawned threads.size, []⟩)
      | none => do
          match ← arrivalPlan s threads i c ch with
          | (some (.pair bc cs), ch₁, ps₁) =>
              match cs with
              | [] => throw (.internal "empty arrival pairing plan")
              | _ :: _ => do
                  -- L4 (`ChoiceSite.l4Waiter`): any matching waiter.
                  -- The singleton non-consumption that used to be a
                  -- caller-side special case here is now the site's
                  -- declared policy (`consumeAtOne := false`).
                  let (idx, ch₂, ps₂) := Choices.consumeAtE .l4Waiter cs.length ch₁
                  match cs[idx]? with
                  | some cand => do
                      let (ts', s'') ← applyPairing s threads i bc cand
                      return (ts', s'', ch₂,
                        ⟨i, .paired cand.2.partnerIdx, ps₁ ++ ps₂⟩)
                  | none => throw (.internal "waiter pick out of range")
          | (some (.commit cl env k), ch₁, ps₁) => do
              -- The L2-picked clause is cell-only ready: commit it
              -- against the cell at the pool level (`applySelect`'s
              -- cell bound differs from the waiter-extended one the
              -- pick was drawn over).
              let (c', s') ← commitClause s env k cl
              return (threads.setIfInBounds i c', s', ch₁,
                ⟨i, .selectCommit cl, ps₁⟩)
          | (none, ch₁, ps₁) =>
              match selectApplyPlan c with
              | some (v, clauses, default?, done, env, k') =>
                  -- THE SELECT INTERCEPTION (Q2): the cell-path select
                  -- apply runs HERE instead of through `stepFn`'s arm,
                  -- so the apply's emitted commit identity reaches the
                  -- event. Byte-identical to `stepFn`'s arm: the same
                  -- `applySelect` call (one consuming definition — the
                  -- sequential arm projects the identity away, this
                  -- path keeps it), the same defensive panic wrapping
                  -- with the pre-consumption stream.
                  match applySelect s clauses default?
                      ((v :: done).reverse) env k' ch₁ with
                  | .ok (c', s', ch₂, cl?) =>
                      return (threads.setIfInBounds i c', s', ch₂,
                        ⟨i, match cl? with
                            | some cl => .selectCommit cl
                            | none => .selectPass, ps₁⟩)
                  | .error (.panic msg) =>
                      return (threads.setIfInBounds i
                        (.panicking [⟨runtimeErrorValue msg, false⟩] k'),
                        s, ch₁, ⟨i, .selectPass, ps₁⟩)
                  | .error err => throw err
              | none => do
                  let (c', s', ch₂) ← stepFn s c ch₁
                  -- E9 closure: a mapDelete/clearMap apply that
                  -- proceeded prunes every OTHER goroutine's in-flight
                  -- map iterations too (`pruneForeign`; identity at
                  -- every non-pruning shape).
                  let ts' ← pruneForeign s' i c c' (threads.setIfInBounds i c')
                  return (ts', s', ch₂, ⟨i, .privateStep, ps₁⟩)

/-- `stepThread` lifted back into a `MultiConfig` (the stepped goroutine
becomes the running one). -/
def stepThreadInto (m : MultiConfig) (i : Nat) (ch : Choices) :
    Except GoError (MultiConfig × Choices × StepEvent) := do
  let (ts, s', ch', ev) ← stepThread m.shared m.threads i ch
  return ({ threads := ts, shared := s', cur := i }, ch', ev)

/-- The scheduling SITE a boundary configuration consults (stage C):
an `.opDone` marker carries its own tag (`postOp` for op completions,
`l1Sched` for spawn completions — BUG-040's shipped default preserved
bit-for-bit); every other boundary shape is the L1 site. The match is
CLAMPED: a marker hand-built with a non-scheduling tag (no emitter
produces one) consults the L1 site — the universal pre-widening
behavior — so the site's non-popping policy holds for ARBITRARY
configurations (`Config.boundarySite_consumeAtOne`), which the
sequential-conservation lemmas quantify over. Stage D adds the
back-edge shapes with their `backEdge` tag. -/
def Config.boundarySite : Config → ChoiceSite
  | .opDone .postOp _ => .postOp
  | .next (.loop _ _ _ _) => .backEdge
  | .continuing (.loop _ _ _ _) => .backEdge
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ _) => .backEdge
  | _ => .l1Sched

/-- The slot MENU of a scheduling consultation at a boundary (stage C).
For `l1Sched` (and every non-postOp site) the menu is `runnableIdxs`
in goroutine order — slot 0 = lowest-index runnable, today's exact
behavior. For `postOp` and (stage D) `backEdge` the menu is
ISSUER/CURRENT-FIRST: slot 0 = `cur` (the goroutine whose op just
completed / whose loop is re-entering — the old machine's schedule,
audit C-2's canonical-slot convention, which is what makes the
empty/default stream reproduce the pre-widening schedule literally),
slots 1.. = the other runnables in goroutine order. The current
goroutine at either site is neither done nor blocked (the marker and
the loop re-entry shapes), so it is always runnable and the menu is
never empty; the menu's SET equals the runnable set either way — the
relation's `schedPick` (membership in `runnableIdxs`) is unchanged by
the slot reordering. -/
def schedSlots (s : ExecState) (threads : Array Config) (cur : Nat) :
    ChoiceSite → List Nat
  | .postOp => cur :: (runnableIdxs s threads).filter (· != cur)
  | .backEdge => cur :: (runnableIdxs s threads).filter (· != cur)
  | _ => runnableIdxs s threads

/-- One pool step (D2a). If the running goroutine is at a registry
boundary, RESCHEDULE: the boundary's scheduling site
(`Config.boundarySite` — L1, or the marker's `postOp`) picks among the
runnable goroutines via its slot menu (`schedSlots`) — consumed ONLY
when the menu has ≥ 2 slots (`runnableIdxs` has the L1 envelope
statement; `Config.opDone` the postOp one) — and the picked goroutine
takes its step in the same call (so fuel counts exactly one
goroutine-step per pool step). No runnable goroutine at a boundary is
the DEADLOCK terminal (all goroutines are asleep; unreachable at a
postOp boundary, whose issuer is runnable). Between boundaries the
running goroutine steps privately. -/
def stepMulti (m : MultiConfig) (ch : Choices) :
    Except GoError (MultiConfig × Choices × StepEvent) := do
  match m.threads[m.cur]? with
  | none => throw (.internal "running goroutine out of range")
  | some c =>
    if c.atBoundary then
      match schedSlots m.shared m.threads m.cur c.boundarySite with
      | [] => throw .deadlock
      | rs => do
          -- The site consultation (`l1Sched`/`postOp`): the
          -- sole-runnable non-consumption that used to be a
          -- caller-side `[i]` special case is now each site's declared
          -- policy (`consumeAtOne := false`) — sequential
          -- conservation's hinge, as table rows. Q2: the pick record
          -- prefixes the picked goroutine's own event picks.
          let (pick, ch₁, ps) :=
            Choices.consumeAtE c.boundarySite rs.length ch
          match rs[pick]? with
          | some i => do
              let (m', ch₂, ev) ← stepThreadInto m i ch₁
              return (m', ch₂, { ev with picks := ps ++ ev.picks })
          | none => throw (.internal "scheduler pick out of range")
    else
      stepThreadInto m m.cur ch

/-! ## The registry's SECOND duty: segment-level happens-before race
detection (slice 3, D2+D3(b))

Execution between registry ops is a SEGMENT: a goroutine's vector
clock changes only at registry-op HB edges, so every private step in
between records its accesses (`stepAccesses`, Race.lean) under one
clock — the segment's. `raceUpdate` below is the event FOLD the
detecting loop (`execProgLoop`) runs after every pool step (stage B,
audit Q2/O-2): the step's classification — spawn / wake / pairing
(with its partner) / select commit (with its clause) / private step —
arrives IN the `StepEvent` the step emitted, so the old parallel
dispatch (partner recovery by pool diffing, committed-clause recovery
by replaying the stream consumption) is deleted rather than
maintained in lockstep by review. The fold either advances the clocks
(the go_mem channel rules, quoted at `ChanClocks`/`RaceState.spawn`
in Race.lean) or checks-and-records the step's footprint — the
FOOTPRINT classification of chan/sync cell-path applies stays derived
from the pre-configuration (the footprint-table-not-autologging
decision, Race.lean:26-53). A conflict is the terminal
`raceDetected`: races fail closed per run, on every run where the
conflicting accesses execute, deterministically given the stream.
One remaining textual mirror, recorded: the WAKE arm's head-commit
classification (`raceWakeEvent`'s `.blockedSelect` case) re-derives
`resumeThread`'s deterministic head-commit from the cell — shape-
derived and stream-free, so it is lockstep-by-construction, but a
future `resumeThread` commit-identity emission would fold it too.

The detector is EXTERNAL instrumentation in the `Choices`/fuel mold:
`stepMulti`, the `StepM` relation, and the whole correspondence kit
are untouched (grow by extension); the only influence on execution is
the refusal itself. It is inert (definitionally, `raceUpdate`'s first
branch) while the pool holds one goroutine — a single goroutine cannot
race with itself — which keeps sequential conservation literal and
the sequential corpus at zero detector overhead. -/

/-- Clock event of one `wgAdd` apply (spec-parity slice 2):
release-merge on a negative delta (gc waitgroup.go:81 — BEFORE the
panic checks, so a recovered negative-counter Done still released).
The sema-READ half of the misuse pair (an Add taking the counter off 0
upward, waitgroup.go:111-115) is no longer here: since BUG-080 it is
the `syncEntryKinds` row the sync arm records in the DATA shadow at the
primitive's `sema` word, ahead of this event — beside the state RMW's
go_mem kind (`.atomicWrite @state`, Q-U4RESIDUAL (A)). -/
def raceWgAddEvent (r : RaceState) (i : Nat) (loc : Loc) (delta : Int) :
    Except GoError RaceState :=
  if delta < 0 then return (r.syncRelease i loc) else return r

-- `wokenPartner` DELETED (stage B, audit O-2): the pairing partner
-- arrives in the step event (`StepAction.paired`) — emitted by the
-- step that paired, never recovered by diffing pre/post pools.

/-- The channel a chan-op apply position is about to operate on, with
its direction (`true` = send side). -/
def chanApplyChan : Config → Option (Bool × Loc)
  | .retV v (.chanStK op done [] _ _) =>
      match op, (v :: done).reverse with
      | .send _, chv :: _ => (chanValueLoc chv).map ((true, ·))
      | .recv _ _, [chv] => (chanValueLoc chv).map ((false, ·))
      | _, _ => none
  | _ => none

/-- Clock update for a committed select clause / woken select — the
cell-path channel op it performs: buffered send/receive through the
slot clocks, closed-empty receive through the close clock, panicking
or unready shapes no edge. -/
def raceCommitClauseEvent (s : ExecState) (i : Nat) (r : RaceState) :
    EvClause → Except GoError RaceState
  | .sendEv chv _ _ _ => do
      match chanValueLoc chv with
      | some loc => do
          let (buf, cap, closed) ← chanCell s loc
          if closed then return r  -- send-on-closed panic: no edge
          else if buf.size < cap then return (r.slotOp i loc cap true)
          else return r
      | none => return r
  | .recvEv chv _ _ _ => do
      match chanValueLoc chv with
      | some loc => do
          let (buf, cap, closed) ← chanCell s loc
          if buf.size > 0 then return (r.slotOp i loc cap false)
          else if closed then return (r.closeAcquire i loc)
          else return r
      | none => return r

/-- Clock update for the WAKE of a parked goroutine (classified from
the pre-step cell exactly as `resumeThread` classifies): a close-woken
sender panics with NO edge — deliberately STRONGER than gc's realized
HB here (S3 audit correction: gc's `closechan` DOES `raceacquireg` the
parked sender's g at chan.go's "release all writers" loop, exactly as
it does for receivers; the earlier claim that the woken `chansend`
path performs no raceacquire was true but irrelevant — the closer
installs the edge). CORRECTED at the arc-final audit (F1/BUG-045,
2026-08-08): this docstring used to claim "the refusal-set agreement
with `-race` holds anyway" via gc's channel-OBJECT instrumentation
"which we do not model" — asserting agreement through the very
mechanism whose absence broke it (three shipped confluent-green
subjects were TSan-red). The chan-object pair IS now modeled
(`RaceState.chanObjAccess`, U3 closed): every close beside a parked
plain sender refuses at the CLOSE, before this wake can run — so the
missing closer→woken-sender edge is moot on refused programs, and the
close-woken-sender panic arm is detector-unreachable in race-free
programs (no HB edge can order a close after a send entry that then
parks; the arm remains for the racy members' pre-refusal semantics).
A buffered send/receive completes through the slot clocks; a
closed-empty receive acquires the close clock. -/
def raceWakeEvent (s : ExecState) (i : Nat) (r : RaceState) :
    Config → Except GoError RaceState
  | .blockedSend (some loc) _ _ => do
      let (_, cap, closed) ← chanCell s loc
      if closed then return r
      else return (r.slotOp i loc cap true)
  | .blockedRecv (some loc) _ _ _ _ => do
      let (buf, cap, closed) ← chanCell s loc
      if buf.size > 0 then return (r.slotOp i loc cap false)
      else if closed then return (r.closeAcquire i loc)
      else return r
  | .blockedSelect evs _ _ => do
      -- Head-commit lockstep with `resumeThread` (slice 4): the wake
      -- commits the FIRST wake-ready clause, deterministically.
      match ← readyClauses s evs with
      | cl :: _ => raceCommitClauseEvent s i r cl
      | [] => return r
  -- Sync wakes (spec-parity slice 2): every successful resume is the
  -- op's ACQUIRE — Lock/RLock/write-Lock at their acquisition, Wait at
  -- its unblocked return ("a call to Done 'synchronizes before' the
  -- return of any Wait call that it unblocks"), a woken Do at its
  -- completion-observing return. `wlock` acquires BOTH clocks
  -- (rwmutex.go:159-160). No release happens at a wake, and no
  -- state-word access is recorded at one (BUG-080): the parked
  -- goroutine released nothing after its entry, so every conflict a
  -- wake-time access could find, the entry access (`syncEntryKinds`)
  -- already found — Race.lean's sync-words section.
  | .blockedSync op loc _ _ =>
      match op with
      | .lock => return (r.syncAcquire i loc)
      | .rlock => return (r.syncAcquire i loc)
      | .wlock => return (r.syncAcquire i loc (alsoB := true))
      | .wgWait => return (r.syncAcquire i loc)
      | .onceBegin _ => return (r.syncAcquire i loc)
      -- The five heads above are the ONLY ones `applySyncOp` parks
      -- (`.blockedSync` construction sites, Machine.lean); the releasing
      -- heads never sit in a parked Config. Enumerated so a new head is a
      -- compile error, not a silently edge-less wake.
      | .unlock | .runlock | .wunlock | .wgAdd | .onceComplete => return r
  | _ => return r

/-- Clock update for a PAIRING step (arriving goroutine `i`, woken
partner `j`): capacity 0 is the bidirectional rendezvous (`racesync`;
both unbuffered go_mem rules); a buffered direct handoff transits the
slot clocks — sender's slot-op, then receiver's, same slot (gc's
`send()` pretends the value crossed the buffer); a head-and-refill
receive takes the HEAD slot (the k-th send's clock) while the parked
sender releases into the tail slot. The channel comes from the parked
partner's shape, or from the arriving op when the partner is a parked
select clause (select-with-select pairing is refused upstream). -/
def racePairEvent (s : ExecState) (tsPre : Array Config) (i j : Nat)
    (cPre : Config) (r : RaceState) : Except GoError RaceState := do
  let viaSlots (loc : Loc) (cap : Nat) (senderFirst : Bool)
      (sender recv : Nat) : RaceState :=
    if senderFirst then (r.slotOp sender loc cap true).slotOp recv loc cap false
    else (r.slotOp recv loc cap false).slotOp sender loc cap true
  match tsPre[j]? with
  | some (.blockedSend (some loc) _ _) => do
      -- partner sends; arriving side receives
      let (buf, cap, _) ← chanCell s loc
      if cap == 0 then return (r.rendezvous i j)
      else if buf.size > 0 then
        -- head-and-refill: receiver takes the head first, sender refills
        return (viaSlots loc cap false j i)
      else return (r.rendezvous i j)
  | some (.blockedRecv (some loc) _ _ _ _) => do
      -- partner receives; arriving side sends
      let (buf, cap, _) ← chanCell s loc
      if cap == 0 then return (r.rendezvous i j)
      else if buf.isEmpty then
        -- buffered direct handoff through the (empty) slot
        return (viaSlots loc cap true i j)
      else return (r.rendezvous i j)
  | some (.blockedSelect _ _ _) => do
      match chanApplyChan cPre with
      | some (isSend, loc) => do
          let (buf, cap, _) ← chanCell s loc
          if cap == 0 then return (r.rendezvous i j)
          else if isSend then
            if buf.isEmpty then return (viaSlots loc cap true i j)
            else return (r.rendezvous i j)
          else
            if buf.size > 0 then return (viaSlots loc cap false j i)
            else return (r.rendezvous i j)
      | none => return r
  | _ => return r

/-- The per-shape ENTRY reads a channel/select apply records WHATEVER
its outcome (commit, park, pairing, panic) — BUG-045's plain-send
chan-object read (gc's `chansend` reads `c.raceaddr()` at entry) and
BUG-046's selectgo pass-1 read per polled SEND clause (recv cases are
acquire-only; nil-channel cases match the `none` skip; recording in
clause order is detection-equivalent — same pre-op clock, same-
goroutine re-records upsert). Factored out of `raceUpdate` so the
pairing / commit / pass arms share it. -/
def raceChanEntryReads (i : Nat) (cPre : Config)
    (r : RaceState) : Except GoError RaceState := do
  match cPre with
  | .retV v (.chanStK op done [] _ _) =>
      (match op, (v :: done).reverse with
      | .send _, chv :: _ =>
          (match chanValueLoc chv with
          | some loc => r.chanObjAccess i loc false
          | none => pure r)
      | _, _ => pure r)
  | .retV v (.selectOpsK clauses _ done [] _ _) =>
      (match selectClauseChans clauses ((v :: done).reverse) with
      | some sides =>
          sides.foldlM (fun r side =>
            match side with
            | some (true, loc) => r.chanObjAccess i loc false
            | _ => pure r) r
      | none => pure r)
  | _ => return r

/-- **The detector's event FOLD** (stage B — module docstring above):
run by the detecting loop after every successful pool step, over the
PRE-step pool (`sPre`/`tsPre`), the step's emitted `StepEvent`, and
the post-step pool `m'`. Inert while the pool holds ≤ 1 goroutine.
Dispatch is ON THE EVENT; per-shape footprints and entry reads are
derived from the pre-configuration (the footprint table's job); no
stream is consulted — `raceUpdate` no longer takes one. -/
def raceUpdate (sPre : ExecState) (tsPre : Array Config) (ev : StepEvent)
    (m' : MultiConfig)
    (r : RaceState) : Except GoError RaceState := do
  if m'.threads.size ≤ 1 then return r
  else
    let i := ev.who
    match tsPre[i]? with
    | none => return r
    | some cPre =>
      match ev.action with
      | .spawned child =>
          -- Spawn: the go_mem edge, PLUS the child frame entry's
          -- possible interface-dispatch receiver deref (recorded under
          -- the CHILD's id, after the edge — gc attributes the read to
          -- the spawned goroutine; S3 audit).
          let r₁ := r.spawn i child
          match spawnPlan cPre with
          | some (.funcVal fid captured, args, _) =>
              r₁.accesses child (dispatchAccesses sPre fid (captured ++ args))
          | _ => return r₁
      | .woke => raceWakeEvent sPre i r cPre
      | .paired j => do
          let r ← raceChanEntryReads i cPre r
          racePairEvent sPre tsPre i j cPre r
      | .selectCommit cl => do
          -- Entry-path commit (singleton or L2-picked, the apply's
          -- emitted identity) and the arrival-path `.commit` both land
          -- here. `raceCommitClauseEvent` reads the pre-cell, so a
          -- panicking commit (send on closed) correctly yields no
          -- edge.
          let r ← raceChanEntryReads i cPre r
          raceCommitClauseEvent sPre i r cl
      | .selectPass => raceChanEntryReads i cPre r
      | .opDoneStrip =>
          -- The marker strip is a pure control step: no accesses, no
          -- edges (`stepAccesses`'s catch-all recorded it as `[]`
          -- before; Race.lean's model-internal-loads inventory).
          return r
      | .privateStep =>
          -- Outcome-shape discrimination (stage C): a PROCEEDING
          -- chan/sync apply outcome is now the `.opDone` completion
          -- marker (B1) — the success checks match the marker, parked
          -- and panicking outcomes stay unwrapped.
          match cPre with
          | .retV v (.chanStK op done [] _ _) => do
              let r ← raceChanEntryReads i cPre r
              -- cell path: classify from the pre-cell + outcome shape
              match op, (v :: done).reverse with
              | .send _, chv :: _ =>
                  (match chanValueLoc chv with
                  | some loc =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => do
                          let (_, cap, _) ← chanCell sPre loc
                          return (r.slotOp i loc cap true)
                      | _ => return r)  -- parked / panicked: no edge yet
                  | none => return r)
              | .recv _ _, [chv] =>
                  (match chanValueLoc chv with
                  | some loc =>
                      (match m'.threads[i]? with
                      | some (.blockedRecv _ _ _ _ _) => return r
                      | _ => do
                          let (buf, cap, closed) ← chanCell sPre loc
                          if buf.size > 0 then return (r.slotOp i loc cap false)
                          else if closed then return (r.closeAcquire i loc)
                          else return r)
                  | none => return r)
              | .close, [chv] =>
                  (match chanValueLoc chv with
                  | some loc =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => do
                          -- BUG-045: closechan's racewritepc — on the
                          -- SUCCESS path only (gc panics on closed/nil
                          -- before instrumenting), checked under the
                          -- pre-release clock, then the release.
                          let r ← r.chanObjAccess i loc true
                          let (_, cap, _) ← chanCell sPre loc
                          return (r.closeOp i loc cap)
                      | _ => return r)  -- close panic: no edge, no write
                  | none => return r)
              | _, _ => return r
          | .retV v (.syncStK op done [] _ _) => do
              -- THE SYNC REGISTRY ENTRY'S SECOND DUTY (spec-parity
              -- slice 2, design note §5): classify the apply from the
              -- pre-step shape and the outcome, and advance the sync
              -- clocks per the package-doc HB sentences (quoted at
              -- `SyncClocks`). Fatal outcomes never reach here (the
              -- pool step errored); parked outcomes carry no edge (the
              -- wake does, above). AND ITS THIRD (BUG-080; Q-U4RESIDUAL
              -- (A)): the accesses on the primitive's OWN words —
              -- TSan's realized set ∪ go_mem's operation kind, each at
              -- its gc word (Race.lean `syncWord`) — `syncEntryKinds`
              -- under the pre-op clock BEFORE the hook (gc's instruction
              -- order: the state CAS / the `race.Read(&rw.w)` / the
              -- `wg.sema` pair precede the acquire/release; the go_mem
              -- kind of the op sits with them), `syncReleaseTailKinds`
              -- AFTER the release on a committed op (Unlock's state Add
              -- follows `race.Release`) — recorded in the DATA shadow
              -- under the sync cell's path, where a plain copy/overwrite
              -- of the primitive (or its enclosing struct) overlaps them.
              match (v :: done).reverse.head? with
              | some (.addr loc) =>
                  match syncCell sPre loc with
                  -- Unreachable by construction (the apply already took this
                  -- cell as a primitive, else it was stuck and never folded);
                  -- propagated, not absorbed — a fail-open `return r` here
                  -- would silently drop the entry access.
                  | .error e => throw e
                  | .ok pre => do
                  let delta : Int ←
                    match op, (v :: done).reverse[1]? with
                    | .wgAdd, some dv => valueAsInt dv  -- an error propagates (same reason)
                    | .wgAdd, none =>
                        throw (.internal "sync arm: wgAdd committed without its delta operand")
                    | _, _ => pure 0
                  let r ← r.accesses i (syncEntryKinds op pre delta loc)
                  let r ← (match op with
                  | .lock | .rlock =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncAcquire i loc)
                      | _ => return r)
                  | .wlock =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncAcquire i loc (alsoB := true))
                      | _ => return r)
                  | .unlock =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncRelease i loc)
                      | _ => return r)
                  | .wunlock =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncRelease i loc)
                      | _ => return r)
                  | .runlock =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncRelease i loc (toB := true))
                      | _ => return r)
                  | .wgAdd =>
                      -- gc's Add (waitgroup.go): ReleaseMerge when
                      -- delta < 0 (BEFORE the panic checks, so a Done
                      -- whose negative-counter panic is later recovered
                      -- still released — probed ordering, design note
                      -- §4). The sema READ of the misuse pair (counter
                      -- departing 0 upward; it too precedes the panics)
                      -- and the state RMW's write-like go_mem kind were
                      -- recorded above by `syncEntryKinds`.
                      raceWgAddEvent r i loc delta
                  | .wgWait =>
                      -- The first-waiter sema WRITE (waitgroup.go:184-190,
                      -- pre-park waiter count 0 — concurrent Waits must
                      -- not race each other) and the counter read's
                      -- read-like go_mem kind were recorded above by
                      -- `syncEntryKinds`; a park carries no edge.
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncAcquire i loc)
                      | _ => return r)
                  | .onceBegin _ =>
                      -- Acquire only when the apply OBSERVED completion
                      -- (pre-cell started ∧ done → the delivered false
                      -- acquires); a fresh begin or a park carries no
                      -- edge (the completion release is onceComplete's).
                      (match syncCell sPre loc with
                      | .ok (.once true true) => return (r.syncAcquire i loc)
                      | _ => return r)
                  | .onceComplete =>
                      (match m'.threads[i]? with
                      | some (.opDone _ _) => return (r.syncRelease i loc)
                      | _ => return r))
                  -- BUG-080: the state-word RMW that FOLLOWS the release
                  -- (Unlock's Add; Once's deferred Unlock), on a
                  -- committed op only — it also carries go_mem's
                  -- write-like unlock (Race.lean, the Mutex row).
                  match m'.threads[i]? with
                  | some (.opDone _ _) =>
                      r.accesses i (syncReleaseTailKinds op pre loc)
                  | _ => return r
              | _ => return r  -- nil/garbage receiver: the apply panicked
          | _ =>
              match m'.threads[i]? with
              | some (.panicking _ _) =>
                  match cPre with
                  | .panicking _ _ => r.accesses i (stepAccesses sPre cPre)
                  | _ => return r  -- the step panicked: the access never happened
              | _ => r.accesses i (stepAccesses sPre cPre)


/-- The first unrecovered-panic abort among the goroutines: an
unrecovered panic in ANY goroutine terminates the program (Go). -/
def MultiConfig.panicMsg? (m : MultiConfig) : Option String :=
  m.threads.toList.findSome? fun c =>
    match c with
    | .panicked msg => some msg
    | _ => none

/-- Main's terminal outcome, if main (goroutine 0) has reached one:
the program's outcome (D6 — the program exits with main; other
goroutines are discarded, their defers never run). The final state is
the SHARED state at main's exit — the "joined final state" of the
statement idiom. -/
def MultiConfig.mainOutcome? (m : MultiConfig) : Option ExecOutcome :=
  match (m.threads[0]? : Option Config) with
  | some (.next .stop) => some (.normal m.shared)
  | some (.returning .stop) => some (.returned m.shared)
  | some (.breaking .stop) => some (.broke m.shared)
  | some (.continuing .stop) => some (.continued m.shared)
  | _ => none

/-- Fuel-bounded pool execution to the program terminals, mirroring
`execStmtLoop`'s classification order (any-goroutine panic abort,
then main's terminal, then the deadlock state, all BEFORE the fuel
check — a WEDGED program never reports exhaustion, and a finished one
only through the L5 window below: at main's terminal with runnable
goroutines left, a continue pick at fuel 0 is `.fuelOut` — the
convergence check corrected this sentence's old unqualified
"a finished or wedged program never reports exhaustion", which
`execProgLoop_mono`'s window case explicitly contradicts),
with `stepMulti` in place of `stepFn`. Fuel counts goroutine-steps.
THE DETECTING LOOP (slice 3): a `RaceState` rides along, updated by
`raceUpdate` after every pool step — a conflict aborts the run with
the terminal `raceDetected` before anything else can be observed
(fail closed per run; deterministic given the stream; consumes no
choices and no fuel). Inert on one-goroutine pools, so sequential
conservation and the sequential corpus are untouched by construction.

**THE MAIN-EXIT WINDOW (L5; BUG-044, channels-arc final audit F2).**
Main's terminal does NOT tear the program down while another goroutine
is runnable: spec §Program execution ("It does not wait for other
(non-main) goroutines to complete") gives no ordering between main's
return and other goroutines' progress, so gc may run a woken partner
any finite amount before the exit — the verifier realized the excluded
member on the PLAIN oracle (dossier F2). Envelope: at `mainOutcome?`
with `runnableIdxs` nonempty, a bound-2 pick — 0 = exit now (the
default, so empty/default streams keep the old behavior), 1 = one more
ordinary pool step (`stepMulti`: at main's terminal boundary that is
exactly the L1 reschedule among the runnable others) — repeated at
every subsequent loop entry until exit is picked or nothing is
runnable. Too-wide is bounded by the same discipline as L1: the window
only reorders/extends registry-granularity schedules gc's scheduler
can realize; in a race-free program its only observable member beyond
the exit is a woken goroutine's own program-aborting panic (a
result-cell write from the window would conflict with main's readout
accesses and refuse — the detector rides along; window steps go
through `raceUpdate` like any other). A single-thread pool has no
runnable others at main's terminal, so the site never opens there and
sequential conservation stays literal (`execProgLoop_single`). The
relation needed NO widening: `StepM`/`schedPick` already allow
post-main-terminal steps of runnable goroutines — the driver was the
narrow side. -/
def execProgLoop : Nat → MultiConfig → RaceState → Choices →
    Except GoError (ExecOutcome × Choices)
  | fuel, m, r, choices =>
      if m.threads.isEmpty then
        throw (.internal "thread pool without a main goroutine")
      else
        match m.panicMsg? with
        | some msg => throw (.panic msg)
        | none =>
            match m.mainOutcome? with
            | some out =>
                (match runnableIdxs m.shared m.threads with
                | [] => return (out, choices)
                | _ :: _ =>
                    -- The main-exit window (L5, `ChoiceSite.l5ExitWindow`):
                    -- 0 = exit, 1 = step.
                    let (pick, choices₁) := Choices.consumeAt .l5ExitWindow 2 choices
                    if pick == 0 then return (out, choices₁)
                    else
                      match fuel with
                      | 0 => throw .fuelOut
                      | fuel + 1 => do
                          let (m', choices', ev) ← stepMulti m choices₁
                          let r' ← raceUpdate m.shared m.threads ev m' r
                          execProgLoop fuel m' r' choices')
            | none =>
                if (runnableIdxs m.shared m.threads).isEmpty then
                  throw .deadlock
                else
                  match fuel with
                  | 0 => throw .fuelOut
                  | fuel + 1 => do
                      let (m', choices', ev) ← stepMulti m choices
                      let r' ← raceUpdate m.shared m.threads ev m' r
                      execProgLoop fuel m' r' choices'

/-- **The `execStmt`-shaped POOL wrapper** (D8's carrier swap): run
`prog` as goroutine 0 of a fresh pool over `σ`, with the race detector
armed from an empty `RaceState`. On programs that never spawn this
agrees with `execStmt` on the TRANSFERABLE result classes (`.ok` at
any terminal, `.fuelOut`, `.panic`) by `execProg_single_eq_execStmt`
(MultiSound.lean — the sequential-conservation transfer lemma; the
detector is definitionally inert on one-goroutine pools); the
fail-closed diagnostic classes are covered by the full-corpus
bit-identity check, not the theorem (S2 audit response: citation
matched to the theorem's actual strength). -/
def execProg (fuel : Nat) (env : LocalEnv) (σ : ExecState) (choices : Choices)
    (prog : Stmt) : Except GoError (ExecOutcome × Choices) :=
  execProgLoop fuel ⟨#[.exec prog env .stop], σ, 0⟩ {} choices

/-- The whole-PROGRAM pool entry: `runProgramM`'s wiring (shared setup —
subject lookup, arity, global seeding, `StateWf` assert, the SEQUENTIAL
`$pkginit` phase, argument binding, result pinning) with the subject
run on the POOL. `go` during `$pkginit` stays fail-closed (the init
phase runs on the sequential driver — the decided slice scope). Result
readout: main's pinned result locations in the shared state at main's
exit, exactly the sequential driver's readout. -/
def runProgramPoolM (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (choices : Choices := []) : Except GoError Result := do
  let (c₀, s₀, resultLocs, choices₁) ← runProgramSetupM fuel program name args choices
  match ← execProgLoop fuel ⟨#[c₀], s₀, 0⟩ {} choices₁ with
  | (.normal sF, _) => return { values := (← loadMany sF resultLocs).toArray }
  | _ => throw (.internal "main terminal outside its barrier frame")

/-! ## The spawn-extended per-goroutine relation (the `Step` spawn
component, D1: the relation stays per-thread with a spawn component;
iris-lean's generic thread-pool `Language` consumes exactly this shape
— `Config × ExecState → Config × ExecState × List Config`). -/

/-- Per-goroutine step WITH spawn component: every sequential `Step`
lifts with no forked goroutines; the completed spawn positions (where
`Step` is deliberately silent) fork exactly one. Proof infrastructure
(statement-TCB: forbidden from designated statement closures, like
`Step`/`Steps`). -/
inductive StepE : Config → ExecState → Config → ExecState → List Config → Prop where
  | lift {c σ c' σ'} : Step c σ c' σ' → StepE c σ c' σ' []
  | spawn {c σ cv args k parent' child σ'} :
      spawnPlan c = some (cv, args, k) →
      spawnStep σ cv args k = .ok (parent', child, σ') →
      StepE c σ parent' σ' [child]

/-- Legal scheduler picks (D2a): between boundaries only the running
goroutine steps; at a boundary any RUNNABLE goroutine may be picked —
the L1 envelope (`runnableIdxs`). -/
def schedPick (m : MultiConfig) (i : Nat) : Prop :=
  match m.threads[m.cur]? with
  | some c => if c.atBoundary then i ∈ runnableIdxs m.shared m.threads else i = m.cur
  | none => False

/-- The POOL relation (proof infrastructure; `stepMulti` is its
executable instantiation — `stepMulti_sound`/`stepM_complete`). Five
rule classes: a partnerless goroutine step (`thread` — ordinary, spawn,
park, or the completion-marker strip via `Step.opDoneStrip`: the
arrival analysis found no waiter involvement, so a blocked outcome
simply parks; stage C retired the dedicated `spawned` rule into this
one — the marker strip is an ordinary lifted step now that the
sequential relation has its rule; since the E9 closure the rule
carries the cross-goroutine delete-prune `pruneForeign` of the
resulting pool — the identity at every non-pruning shape), the
singleton arrival pairing
(`pair` — gc's waiter-queue priority; the L4 waiter pick is the rule's
`idx`), the multi-ready select arrival's two L2-picked shapes
(`pickPair` / `pickCommit` — the rule's `sel` is the L2 clause pick
over the pure `.multi` analysis, slice 4), and the wake of a parked
goroutine (`wake` — head-commit, no re-randomization). Deadlock is
relation-SILENT (no rule from an all-asleep pool), mirroring the
sequential machine's silent blocked configs. -/
inductive StepM : MultiConfig → MultiConfig → Prop where
  | thread {m : MultiConfig} {i : Nat} {c : Config} {c' : Config} {σ' : ExecState}
      {efs : List Config} {ts' : Array Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      arrivalCases m.shared m.threads i c = .ok .cellPath →
      StepE c m.shared c' σ' efs →
      -- E9 closure: the cross-goroutine delete-prune (identity unless
      -- `c` is a pruning-op apply that proceeded).
      pruneForeign σ' i c c' ((m.threads.setIfInBounds i c') ++ efs.toArray) = .ok ts' →
      StepM m ⟨ts', σ', i⟩
  | pair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : ExecState}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases m.shared m.threads i c = .ok (.single bc cs) →
      (hidx : idx < cs.length) →
      applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'') →
      StepM m ⟨ts', σ'', i⟩
  | pickPair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : ExecState}
      {os : List ArrivalOutcome} {sel : Nat}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.pair bc cs) →
      (hidx : idx < cs.length) →
      applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'') →
      StepM m ⟨ts', σ'', i⟩
  | pickCommit {m : MultiConfig} {i : Nat} {c : Config} {cl : EvClause}
      {env : LocalEnv} {k : Cont} {os : List ArrivalOutcome} {sel : Nat}
      {c' : Config} {σ' : ExecState} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalCases m.shared m.threads i c = .ok (.multi os) →
      os[sel]? = some (.commit cl env k) →
      commitClause m.shared env k cl = .ok (c', σ') →
      StepM m ⟨m.threads.setIfInBounds i c', σ', i⟩
  | wake {m : MultiConfig} {i : Nat} {c c' : Config} {σ' : ExecState} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = true →
      resumeThread m.shared c = .ok (c', σ') →
      StepM m ⟨m.threads.setIfInBounds i c', σ', i⟩

/-! ## Well-formedness (the thread-indexed carrier) -/

/-- Pool well-formedness: the shared state is `StateWf`, the running
index is in range, and EVERY goroutine's configuration is loc-bounded
by the shared allocator with normalized in-flight snapshots — the
sequential `MachineWf`'s components, thread-indexed. Decidable, so
concrete pool seeds discharge it by `decide` like `MachineWf`.

PRESERVATION IS DISCHARGED (slice 5, by the slice-3 build log's
recorded route): `stepMulti_wf` (`MultiWfSound.lean`) proves one
executable pool step keeps this invariant. The sequential `*_wf`
conclusions (`applyChanOp_wf`, `applySelect_wf`,
`step_preserves_wf_loc`) were extended with the step-level
`σ.nextAddr ≤ σ'.nextAddr` conjunct — the monotonicity the
FOREIGN-thread frame argument needed — and the pool helpers gained
their own preservation lemmas (`spawnStep_wf`, `resumeThread_wf`,
`applyPairing_wf`, the arrival-analysis bounds); an untouched
goroutine's `ConfigWf` transports along allocator monotonicity and its
iteration-typing component along the step's types-invariance. This
definition is no longer a scaffold: it is a preserved invariant,
available as the slice-3-declared carrier for future detector work. -/
def MultiWf (m : MultiConfig) : Prop :=
  StateWf m.shared ∧ m.cur < m.threads.size ∧
    ∀ i (h : i < m.threads.size),
      ConfigWf m.shared.nextAddr m.threads[i]
        ∧ Config.itersNormalized m.shared.types m.threads[i] = true

instance (m : MultiConfig) : Decidable (MultiWf m) := by
  unfold MultiWf
  exact inferInstance


def runProgramPoolIntsM (fuel : Nat) (program : Program) (name : String)
    (args : Array Int) (choices : List Nat := []) : Except GoError Result :=
  runProgramPoolM fuel program name (args.map GoValue.int) choices

end GoLean.GoCore.Machine
