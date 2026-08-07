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

* **D2(a) — the scheduler consumption rule.** Context switches happen
  ONLY at registry ops (`Config.atBoundary`: channel-op/select apply
  positions, spawn positions, goroutine exit, parked-blocked configs);
  between boundaries the running goroutine steps without any scheduler
  involvement. The scheduler `Choices` site is consumed ONLY when
  `|runnable| > 1` — `Choices.consume` pops even at bound 1, so
  unconditional consumption would desynchronize every existing
  adversarial-stream run; sequential conservation depends on this.

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

* **Deadlock.** ALL goroutines asleep — no thread runnable (tombstones
  excluded, parked threads unrunnable unless wake-ready) — is the
  `GoError.deadlock` terminal, generalizing slice 1's immediate
  single-thread classification and matching Go's detector state.

Fail closed in this slice (each a visible `.unsupported`, never a
silent approximation): `go` of a nil func value (gc's "go of nil func
value" runtime FATAL — probed 2026-08-07; the fatal class is
unmodeled), select-with-select rendezvous, multi-ready select at
arrival or wake (the L2 envelope, slice 4).
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

/-- The slice-1 blocked shapes — the parked goroutines. -/
def isBlockedConfig : Config → Bool
  | .blockedSend _ _ _ => true
  | .blockedRecv _ _ _ _ _ => true
  | .blockedSelect _ _ _ => true
  | _ => false

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
  | .exec (.selectStmt clauses _) _ _ => (selectOperands clauses.toList).isEmpty
  | .next .stop => true
  | .returning .stop => true
  | .breaking .stop => true
  | .continuing .stop => true
  | .panicked _ => true
  | .blockedSend _ _ _ => true
  | .blockedRecv _ _ _ _ _ => true
  | .blockedSelect _ _ _ => true
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
refuting the older child-panic analysis): the fatal class is unmodeled
— fail closed. -/
def spawnStep (s : ExecState) (cv : GoValue) (args : List GoValue) (k : Cont) :
    Except GoError (Config × Config × ExecState) := do
  match cv with
  | .funcVal fid captured =>
      match enterFrame s fid (captured ++ args) with
      | .ok (func, frameEnv, _resultLocs, s') =>
          return (.next k,
            .exec func.body frameEnv (.frame [] [] [] .stop func.wrapper), s')
      | .error (.panic msg) =>
          return (.next k, .panicking [⟨runtimeErrorValue msg, false⟩] .stop, s)
      | .error e => throw e
  | .nil => throw (.unsupported
      "go of nil func value (gc raises an unrecoverable runtime fatal at the spawn; the fatal class is unmodeled this slice)")
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
wakes through `readyClauses`/`commitClause` — exactly one ready
clause commits; multiple ready at wake FAIL CLOSED (the L2 envelope
is slice 4). Unready resumes are `.internal` (the scheduler only
picks wake-ready parked goroutines — fail closed, never a silent
no-op). -/
def resumeThread (s : ExecState) : Config → Except GoError (Config × ExecState)
  | .blockedSend (some loc) v k => do
      let (buf, capacity, closed) ← chanCell s loc
      if closed then
        return (.panicking [⟨runtimeErrorValue "send on closed channel", false⟩] k, s)
      else if buf.size < capacity then do
        let s' ← storeLoc s loc (.chanData (buf.push v) capacity closed)
        return (.next k, s')
      else throw (.internal "resume on an unready blocked send")
  | .blockedRecv (some loc) targets elem env k => do
      let (buf, capacity, closed) ← chanCell s loc
      match buf[0]? with
      | some v => do
          let s₁ ← storeLoc s loc (.chanData (buf.eraseIdx! 0) capacity closed)
          resumeRecvDelivery s₁ v true targets env k
      | none =>
          if closed then do
            let zero ← defaultValue s elem
            resumeRecvDelivery s zero false targets env k
          else throw (.internal "resume on an unready blocked receive")
  | .blockedSelect evs env k => do
      match ← readyClauses s evs with
      | [] => throw (.internal "resume on an unready blocked select")
      | [cl] => commitClause s env k cl
      | _ :: _ :: _ => throw (.unsupported
          "select with multiple ready cases at wake (deterministic slice; the L2 choice envelope is slice 4)")
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
parked partner matches. No ready clause → `none` (`stepFn`: default or
park). Exactly one ready clause: waiter-matched → pair (a clause both
cell- and waiter-ready pairs, preserving gc's dequeue-first refill
semantics); cell-only → `none` (`applySelect` commits the same single
clause). Two or more ready clauses WITH a waiter involved → fail
closed (the L2 envelope, slice 4); with no waiter involved → `none`
(`applySelect`'s own multi-ready refusal, byte-identical to the
sequential behavior). Select-with-select rendezvous stays fail-closed.

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

@[inherit_doc chanArrivalPlan]
def selectArrivalPlan (s : ExecState) (threads : Array Config) (i : Nat)
    (clauses : List (SelectClauseHead × Stmt)) (vs : List GoValue)
    (env : LocalEnv) (k : Cont) :
    Except GoError (Option (Config × List (Nat × PairTarget))) := do
  match selectClauseChans clauses vs with
  | none => return none
  | some sides =>
      -- pure waiter-existence pre-scan
      if !sidesHaveWaiters threads i sides then return none
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
                -- ready in both directions), it falls to `applySelect`'s
                -- correct closed semantics: the send clause panics, the
                -- recv clause drains/zeroes, and a parked sender is left
                -- for its close-wake panic. Mirrors `chanArrivalPlan`'s
                -- closed guards.
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
        match readiness.filter (fun r => r.2.1 || !r.2.2.isEmpty) with
        | [] => return none
        | [(ci, _, ws)] =>
            if ws.isEmpty then return none  -- cell-only: applySelect commits it
            else if ws.any (fun w => w.2.isSelect) then
              throw (.unsupported
                "select-with-select rendezvous (unmodeled this slice)")
            else
              return some (.blockedSelect evs env k,
                ws.map fun w => (ci, w.2))
        | ready =>
            if ready.all (fun r => r.2.2.isEmpty) then
              return none  -- pure cell multi-ready: applySelect's refusal
            else
              throw (.unsupported
                "select with multiple ready cases under waiter-extended readiness (the L2 choice envelope is slice 4)")

@[inherit_doc chanArrivalPlan]
def arrivalPlanAux (s : ExecState) (threads : Array Config) (i : Nat) :
    Config → Except GoError (Option (Config × List (Nat × PairTarget)))
  | .retV v (.chanStK op done [] env k) =>
      chanArrivalPlan s threads i op ((v :: done).reverse) env k
  | .retV v (.selectOpsK clauses _default? done [] env k) =>
      selectArrivalPlan s threads i clauses ((v :: done).reverse) env k
  | _ => return none

@[inherit_doc chanArrivalPlan]
def arrivalPlan (s : ExecState) (threads : Array Config) (i : Nat)
    (c : Config) : Except GoError (Option (Config × List (Nat × PairTarget))) :=
  arrivalPlanAux s threads i c

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
candidates were just scanned). -/
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
            return ((threads.setIfInBounds i (.next k)).setIfInBounds j cr, s')
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
                return ((threads.setIfInBounds i (.next k)).setIfInBounds j cs', s')
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
              return ((threads.setIfInBounds i cr).setIfInBounds j (.next ks), s')
          | some hd => do
              -- gc recv(): head out, parked sender's value in at the tail
              let s₁ ← storeLoc s loc
                (.chanData ((buf.eraseIdx! 0).push vs) capacity closed)
              let (cr, s') ← resumeRecvDelivery s₁ hd true targets env k
              return ((threads.setIfInBounds i cr).setIfInBounds j (.next ks), s')
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
                  return ((threads.setIfInBounds i cr).setIfInBounds j
                    (.exec body envs ks), s')
              | some hd => do
                  let s₁ ← storeLoc s loc
                    (.chanData ((buf.eraseIdx! 0).push v') capacity closed)
                  let (cr, s') ← resumeRecvDelivery s₁ hd true targets env k
                  return ((threads.setIfInBounds i cr).setIfInBounds j
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
                          return ((threads.setIfInBounds i ci').setIfInBounds j
                            (.next ks), s')
                      | some hd => do
                          let s₁ ← storeLoc s loc
                            (.chanData ((buf.eraseIdx! 0).push vs) capacity closed)
                          let (ci', s') ← selectRecvDelivery s₁ hd true targets body env k
                          return ((threads.setIfInBounds i ci').setIfInBounds j
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
                        return ((threads.setIfInBounds i (.exec body env k)).setIfInBounds j cr, s')
                      else throw (.internal
                        "parked receiver beside a nonempty buffer (hchan invariant breach)")
              | _ => throw (.internal "pairing partner shape mismatch")
          | .selectWaiter _ _ => throw (.internal
              "select-with-select pairing reached applyPairing (refused upstream)")
      | none => throw (.internal "pairing arriving-clause index out of range")
  | _, _ => throw (.internal "pairing on a non-blocked configuration")

/-- One step of goroutine `i` in the pool: a parked goroutine WAKES
(`resumeThread`); a completed spawn position FORKS (`spawnStep`,
appending the child — stable ids); a channel/select apply position
consults PARKED PARTNERS FIRST (`arrivalPlan` — gc's waiter-queue
priority; the L4 pick is consumed ONLY when more than one candidate
matches); everything else — including every partnerless op — steps by
the sequential `stepFn`, a blocked outcome simply parking (partners
were already ruled out by the plan). -/
def stepThread (s : ExecState) (threads : Array Config) (i : Nat)
    (ch : Choices) : Except GoError (Array Config × ExecState × Choices) := do
  match threads[i]? with
  | none => throw (.internal "thread index out of range")
  | some c =>
    if isBlockedConfig c then do
      let (c', s') ← resumeThread s c
      return (threads.setIfInBounds i c', s', ch)
    else
      match spawnPlan c with
      | some (cv, args, k) => do
          let (parent', child, s') ← spawnStep s cv args k
          return ((threads.setIfInBounds i parent').push child, s', ch)
      | none => do
          match ← arrivalPlan s threads i c with
          | some (bc, cs) =>
              match cs with
              | [] => throw (.internal "empty arrival pairing plan")
              | [cand] => do
                  let (ts', s'') ← applyPairing s threads i bc cand
                  return (ts', s'', ch)
              | _ :: _ :: _ => do
                  -- L4: any matching waiter (consumed only at width > 1)
                  let (idx, ch₂) := ch.consume cs.length
                  match cs[idx]? with
                  | some cand => do
                      let (ts', s'') ← applyPairing s threads i bc cand
                      return (ts', s'', ch₂)
                  | none => throw (.internal "waiter pick out of range")
          | none => do
              let (c', s', ch₁) ← stepFn s c ch
              return (threads.setIfInBounds i c', s', ch₁)

/-- `stepThread` lifted back into a `MultiConfig` (the stepped goroutine
becomes the running one). -/
def stepThreadInto (m : MultiConfig) (i : Nat) (ch : Choices) :
    Except GoError (MultiConfig × Choices) := do
  let (ts, s', ch') ← stepThread m.shared m.threads i ch
  return ({ threads := ts, shared := s', cur := i }, ch')

/-- One pool step (D2a). If the running goroutine is at a registry
boundary, RESCHEDULE: the L1 scheduler site picks among the runnable
goroutines — consumed ONLY when `|runnable| > 1` (`runnableIdxs` has
the envelope statement) — and the picked goroutine takes its step in
the same call (so fuel counts exactly one goroutine-step per pool
step). No runnable goroutine at a boundary is the DEADLOCK terminal
(all goroutines are asleep). Between boundaries the running goroutine
steps privately. -/
def stepMulti (m : MultiConfig) (ch : Choices) :
    Except GoError (MultiConfig × Choices) := do
  match m.threads[m.cur]? with
  | none => throw (.internal "running goroutine out of range")
  | some c =>
    if c.atBoundary then
      match runnableIdxs m.shared m.threads with
      | [] => throw .deadlock
      | [i] => stepThreadInto m i ch
      | rs => do
          let (pick, ch₁) := ch.consume rs.length
          match rs[pick]? with
          | some i => stepThreadInto m i ch₁
          | none => throw (.internal "scheduler pick out of range")
    else
      stepThreadInto m m.cur ch

/-! ## The registry's SECOND duty: segment-level happens-before race
detection (slice 3, D2+D3(b))

Execution between registry ops is a SEGMENT: a goroutine's vector
clock changes only at registry-op HB edges, so every private step in
between records its accesses (`stepAccesses`, Race.lean) under one
clock — the segment's. `raceUpdate` below is the event dispatcher the
detecting loop (`execProgLoop`) runs after every pool step: it
classifies the step it just observed (spawn / wake / pairing /
cell-path channel or select op / private step) from the pre- and
post-configurations — deterministically, consuming NOTHING — and
either advances the clocks (the go_mem channel rules, quoted at
`ChanClocks`/`RaceState.spawn` in Race.lean) or checks-and-records the
step's footprint. A conflict is the terminal `raceDetected`: races
fail closed per run, on every run where the conflicting accesses
execute, deterministically given the stream.

The detector is EXTERNAL instrumentation in the `Choices`/fuel mold:
`stepMulti`, the `StepM` relation, and the whole correspondence kit
are untouched (grow by extension); the only influence on execution is
the refusal itself. It is inert (definitionally, `raceUpdate`'s first
branch) while the pool holds one goroutine — a single goroutine cannot
race with itself — which keeps sequential conservation literal and
the sequential corpus at zero detector overhead. -/

/-- The parked partner a pairing step woke, if any: the unique OTHER
index whose configuration went blocked → unblocked. Every non-pairing
pool step leaves all other goroutines' configurations untouched, and
`applyPairing`'s outcomes are never blocked shapes — so this is exactly
the pairing partner, recovered without re-running the L4 pick. -/
def wokenPartner (tsPre tsPost : Array Config) (i : Nat) : Option Nat :=
  (List.range tsPre.size).find? fun j =>
    j != i
      && (match tsPre[j]? with | some c => isBlockedConfig c | none => false)
      && (match tsPost[j]? with | some c => !isBlockedConfig c | none => false)

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
installs the edge). The refusal-set agreement with `-race` holds
anyway, for a different reason: gc flags EVERY close-beside-parked-
sender via its channel-OBJECT instrumentation (`racewritepc` at close
vs `racereadpc` at send entry), which we do not model — recorded in
Race.lean's inventory as under-approximation (U3). A buffered
send/receive completes through the slot clocks; a closed-empty receive
acquires the close clock. -/
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
      match ← readyClauses s evs with
      | [cl] => raceCommitClauseEvent s i r cl
      | _ => return r
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

/-- **The detector's event dispatcher** — run by the detecting loop
after every successful pool step, over the PRE-step pool
(`sPre`/`tsPre`) and the post-step pool `m'` (whose `cur` is the
goroutine that stepped). Inert while the pool holds ≤ 1 goroutine.
Classification mirrors `stepThread`'s dispatch order: spawn (pool
grew), wake (pre-config blocked), channel/select apply (pairing when a
partner was woken, cell path otherwise), private step (footprint
check-and-record; a step that PANICKED performed no access — the
panic fired in place of it). -/
def raceUpdate (sPre : ExecState) (tsPre : Array Config) (m' : MultiConfig)
    (r : RaceState) : Except GoError RaceState := do
  if m'.threads.size ≤ 1 then return r
  else
    let i := m'.cur
    match tsPre[i]? with
    | none => return r
    | some cPre =>
      if m'.threads.size > tsPre.size then
        -- Spawn: the go_mem edge, PLUS the child frame entry's possible
        -- interface-dispatch receiver deref (recorded under the CHILD's
        -- id, after the edge — gc attributes the read to the spawned
        -- goroutine; S3 audit, the dispatch-read footprint).
        let r₁ := r.spawn i tsPre.size
        match spawnPlan cPre with
        | some (.funcVal fid captured, args, _) =>
            r₁.accesses tsPre.size (dispatchAccesses sPre fid (captured ++ args))
        | _ => return r₁
      else if isBlockedConfig cPre then
        raceWakeEvent sPre i r cPre
      else
        match cPre with
        | .retV v (.chanStK op done [] _ _) => do
            match wokenPartner tsPre m'.threads i with
            | some j => racePairEvent sPre tsPre i j cPre r
            | none =>
                -- cell path: classify from the pre-cell + outcome shape
                match op, (v :: done).reverse with
                | .send _, chv :: _ =>
                    (match chanValueLoc chv with
                    | some loc =>
                        (match m'.threads[i]? with
                        | some (.next _) => do
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
                        | some (.next _) => do
                            let (_, cap, _) ← chanCell sPre loc
                            return (r.closeOp i loc cap)
                        | _ => return r)  -- close panic: no edge
                    | none => return r)
                | _, _ => return r
        | .retV v (.selectOpsK clauses _ done [] _ _) => do
            match wokenPartner tsPre m'.threads i with
            | some j => racePairEvent sPre tsPre i j cPre r
            | none => do
                match m'.threads[i]? with
                | some (.blockedSelect _ _ _) => return r
                | _ => do
                    let evs ← evalClauses clauses ((v :: done).reverse)
                    match ← readyClauses sPre evs with
                    | [cl] => raceCommitClauseEvent sPre i r cl
                    | _ => return r  -- default taken / refused upstream
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
`execStmtLoop`'s classification order exactly (any-goroutine panic
abort, then main's terminal, then the deadlock state, all BEFORE the
fuel check — a finished or wedged program never reports exhaustion),
with `stepMulti` in place of `stepFn`. Fuel counts goroutine-steps.
THE DETECTING LOOP (slice 3): a `RaceState` rides along, updated by
`raceUpdate` after every pool step — a conflict aborts the run with
the terminal `raceDetected` before anything else can be observed
(fail closed per run; deterministic given the stream; consumes no
choices and no fuel). Inert on one-goroutine pools, so sequential
conservation and the sequential corpus are untouched by construction. -/
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
            | some out => return (out, choices)
            | none =>
                if (runnableIdxs m.shared m.threads).isEmpty then
                  throw .deadlock
                else
                  match fuel with
                  | 0 => throw .fuelOut
                  | fuel + 1 => do
                      let (m', choices') ← stepMulti m choices
                      let r' ← raceUpdate m.shared m.threads m' r
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
executable instantiation — `stepMulti_sound`/`stepM_complete`). Three
rule classes: a partnerless goroutine step (`thread` — ordinary, spawn,
or park: `arrivalPlan` found no parked partner, so a blocked outcome
simply parks), the arrival pairing (`pair` — gc's waiter-queue
priority; the L4 waiter pick is the rule's `idx`), and the wake of a
parked goroutine (`wake`). Deadlock is relation-SILENT (no rule from an
all-asleep pool), mirroring the sequential machine's silent blocked
configs. -/
inductive StepM : MultiConfig → MultiConfig → Prop where
  | thread {m : MultiConfig} {i : Nat} {c : Config} {c' : Config} {σ' : ExecState}
      {efs : List Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      arrivalPlan m.shared m.threads i c = .ok none →
      StepE c m.shared c' σ' efs →
      StepM m ⟨(m.threads.setIfInBounds i c') ++ efs.toArray, σ', i⟩
  | pair {m : MultiConfig} {i : Nat} {c bc : Config} {σ'' : ExecState}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      spawnPlan c = none →
      arrivalPlan m.shared m.threads i c = .ok (some (bc, cs)) →
      (hidx : idx < cs.length) →
      applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'') →
      StepM m ⟨ts', σ'', i⟩
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

SCAFFOLD STATUS (recorded honestly, slice-2 build log): preservation
(`stepMulti` keeps `MultiWf`) is OWED — the active goroutine's step is
covered by the sequential kit (`step_preserves_wf_loc` and the slice-1
`applyChanOp_wf`/`commitClause_wf`/`enterRecvTargets_wf` family cover
the wake/pairing helpers), but the FOREIGN-thread frame argument
(`ConfigWf` of the untouched goroutines under the stepped shared
state) needs a step-level `nextAddr` monotonicity lemma the sequential
kit does not yet expose. Slice 3 did NOT become the consumer this line
once predicted: the detector's state was externalized into `RaceState`
(the `Choices`/fuel mold — slice-3 build log's recorded deviation), so
nothing consumes `MultiWf` at slice-3 tip either; it remains the
marked scaffold, and the recorded discharge route is extending the
existing `*_wf` lemma conclusions with the `≤ nextAddr` conjunct
(slice-3 build log, MultiWf disposition). -/
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
