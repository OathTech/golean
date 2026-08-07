import GoLean.GoCore.StepFn

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

* **D7 — pairing over waiter queues.** Blocked goroutines are the
  slice-1 blocked-Config shapes; channels hold NO waiter queues.
  Rendezvous is the ARRIVAL INTERCEPT: when a goroutine's channel op
  would park, the pool first looks for matching parked partners and
  performs the direct handoff in the same step (gc's shape: an arriving
  op never parks when it can proceed). Parked goroutines are woken by
  CELL changes only (close, buffer data, buffer room) — which restores
  hchan's invariant analogue: matched parked-parked pairs cannot
  coexist, so a close can never steal an already-pairable rendezvous
  (the too-wide close-window divergence this design rules out).

* **FIFO through handoff.** A direct handoff is performed ONLY when the
  channel's buffer is empty — otherwise the newest value would jump the
  queue past buffered elements (spec: "Channels act as first-in-first-out
  queues"). With a nonempty buffer the arriving op parks and the values
  flow through the buffer.

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
A frame-ENTRY panic (nil-interface dispatch and friends) fires in the
CHILD — its first observable act is aborting on that panic. A nil
callee is gc's "go of nil func value" runtime FATAL at the spawn
(probed 2026-08-07, refuting the older child-panic analysis): the
fatal class is unmodeled — fail closed. -/
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

/-- THE WAITER-PAIRING candidates of an arriving blocked outcome — the
L4 envelope site (design D4; ground-truth §6 row L4): the spec has NO
text on which of several matching parked waiters pairs with an arriving
operation (gc's FIFO wakeup is one legal point, membership-lane
territory), so the envelope is "ANY matching waiter", and when more
than one candidate exists the pick is drawn from the choice stream
bounded by the candidate count (consumed ONLY then — `stepThread`).
Width metadata for the enumerator/membership lane: the site's bound is
the number of matched parked waiters (clauses counted individually).

Candidates are attached as `(arriving-clause-index, target)`; for
chan-op arrivals the first component is 0 and unused.

FIFO guard: a direct handoff is performed only against an EMPTY buffer
(file docstring) — checked here for the send side; the receive side's
emptiness is implied by its blocking condition. The waiter scan runs
FIRST and the cell is consulted only when waiters exist, so a
partnerless park never touches the cell (this keeps the one-thread pool
literally equal to the sequential machine — `stepThread_single`).

Fail-closed refusals (never silent): an arriving select with matchable
waiters on MORE than one clause is the L2 multi-ready surface
(slice 4); a select-with-select rendezvous is unmodeled this slice. -/
def selectClauseWaiters (s : ExecState) (threads : Array Config) (i : Nat)
    (evs : List EvClause) (ci : Nat) :
    Except GoError (Nat × List (Nat × PairTarget)) := do
  match evs[ci]? with
  | some (.recvEv chv _ _ _) =>
      match chanValueLoc chv with
      | some loc =>
          -- clause not cell-ready (it blocked) ⇒ buffer empty, open
          return (ci, sendSideWaiters threads i loc)
      | none => return (ci, [])
  | some (.sendEv chv _ _ _) =>
      match chanValueLoc chv with
      | some loc => do
          let ws := recvSideWaiters threads i loc
          if ws.isEmpty then return (ci, []) else do
            let (buf, _, _) ← chanCell s loc
            if buf.isEmpty then return (ci, ws) else return (ci, [])
      | none => return (ci, [])
  | none => return (ci, [])

@[inherit_doc selectClauseWaiters]
def pairCandidates (s : ExecState) (threads : Array Config) (i : Nat) :
    Config → Except GoError (List (Nat × PairTarget))
  | .blockedSend (some loc) _ _ => do
      let ws := recvSideWaiters threads i loc
      if ws.isEmpty then return [] else do
        let (buf, _, _) ← chanCell s loc
        if buf.isEmpty then return ws else return []
  | .blockedRecv (some loc) _ _ _ _ =>
      -- a blocked receive implies the buffer is empty and open: a parked
      -- send-side waiter's value is exactly the queue head.
      return (sendSideWaiters threads i loc)
  | .blockedSelect evs _ _ => do
      let perClause : List (Nat × List (Nat × PairTarget)) ←
        (List.range evs.length).mapM (selectClauseWaiters s threads i evs)
      match perClause.filter (fun p => !p.2.isEmpty) with
      | [] => return []
      | [(ci, ws)] =>
          if ws.any (fun w => w.2.isSelect) then
            throw (.unsupported
              "select-with-select rendezvous (unmodeled this slice)")
          else
            return (ws.map fun w => (ci, w.2))
      | _ => throw (.unsupported
          "select with waiter-pairable cases on multiple clauses (the L2 multi-ready envelope is slice 4)")
  | _ => return []

/-- Perform ONE pairing: the arriving goroutine `i` (whose op produced
the blocked outcome `bc`) pairs with the chosen candidate — the direct
handoff (gc's `send()`/`recv()` shape): the value teleports, both
goroutines proceed, the buffer is untouched (empty by the FIFO guard).
Shape mismatches are `.internal` (the candidates were just scanned). -/
def applyPairing (s : ExecState) (threads : Array Config) (i : Nat)
    (bc : Config) (cand : Nat × PairTarget) :
    Except GoError (Array Config × ExecState) := do
  match bc, cand.2 with
  | .blockedSend _ v k, .opWaiter j =>
      match threads[j]? with
      | some (.blockedRecv _ targets _ envr kr) => do
          let (cr, s') ← resumeRecvDelivery s v true targets envr kr
          return ((threads.setIfInBounds i (.next k)).setIfInBounds j cr, s')
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedSend _ v k, .selectWaiter j ci =>
      match threads[j]? with
      | some (.blockedSelect evs envs ks) =>
          match evs[ci]? with
          | some (.recvEv _ targets _ body) => do
              let (cs', s') ← selectRecvDelivery s v true targets body envs ks
              return ((threads.setIfInBounds i (.next k)).setIfInBounds j cs', s')
          | _ => throw (.internal "pairing partner clause mismatch")
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedRecv _ targets _ env k, .opWaiter j =>
      match threads[j]? with
      | some (.blockedSend _ v ks) => do
          let (cr, s') ← resumeRecvDelivery s v true targets env k
          return ((threads.setIfInBounds i cr).setIfInBounds j (.next ks), s')
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedRecv _ targets _ env k, .selectWaiter j ci =>
      match threads[j]? with
      | some (.blockedSelect evs envs ks) =>
          match evs[ci]? with
          | some (.sendEv _ vv selem body) => do
              -- the select's send value normalizes at the element type at
              -- COMMIT (commitClause's discipline)
              let v' ← normalizeValueForTy s selem vv
              let (cr, s') ← resumeRecvDelivery s v' true targets env k
              return ((threads.setIfInBounds i cr).setIfInBounds j
                (.exec body envs ks), s')
          | _ => throw (.internal "pairing partner clause mismatch")
      | _ => throw (.internal "pairing partner shape mismatch")
  | .blockedSelect evs env k, tgt =>
      match evs[cand.1]? with
      | some (.recvEv _ targets _ body) =>
          match tgt with
          | .opWaiter j =>
              match threads[j]? with
              | some (.blockedSend _ v ks) => do
                  let (ci', s') ← selectRecvDelivery s v true targets body env k
                  return ((threads.setIfInBounds i ci').setIfInBounds j (.next ks), s')
              | _ => throw (.internal "pairing partner shape mismatch")
          | .selectWaiter _ _ => throw (.internal
              "select-with-select pairing reached applyPairing (refused upstream)")
      | some (.sendEv _ vv selem body) =>
          match tgt with
          | .opWaiter j =>
              match threads[j]? with
              | some (.blockedRecv _ targetsr _ envr kr) => do
                  let v' ← normalizeValueForTy s selem vv
                  let (cr, s') ← resumeRecvDelivery s v' true targetsr envr kr
                  return ((threads.setIfInBounds i (.exec body env k)).setIfInBounds j cr, s')
              | _ => throw (.internal "pairing partner shape mismatch")
          | .selectWaiter _ _ => throw (.internal
              "select-with-select pairing reached applyPairing (refused upstream)")
      | none => throw (.internal "pairing arriving-clause index out of range")
  | _, _ => throw (.internal "pairing on a non-blocked configuration")

/-- One step of goroutine `i` in the pool: a parked goroutine WAKES
(`resumeThread`); a completed spawn position FORKS (`spawnStep`,
appending the child — stable ids); everything else steps by the
sequential `stepFn`, with a blocked outcome routed through the ARRIVAL
INTERCEPT — pair with a matched parked waiter (the L4 site: the pick
is consumed ONLY when more than one candidate matches) or park.
Blocked outcomes leave the state untouched (`applyChanOp`/`applySelect`
block without effects), so the intercept reads the post-step state. -/
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
          let (c', s', ch₁) ← stepFn s c ch
          if isBlockedConfig c' then do
            let cs ← pairCandidates s' threads i c'
            match cs with
            | [] => return (threads.setIfInBounds i c', s', ch₁)
            | [cand] => do
                let (ts', s'') ← applyPairing s' threads i c' cand
                return (ts', s'', ch₁)
            | _ :: _ :: _ => do
                -- L4: any matching waiter (consumed only at width > 1)
                let (idx, ch₂) := ch₁.consume cs.length
                match cs[idx]? with
                | some cand => do
                    let (ts', s'') ← applyPairing s' threads i c' cand
                    return (ts', s'', ch₂)
                | none => throw (.internal "waiter pick out of range")
          else
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
with `stepMulti` in place of `stepFn`. Fuel counts goroutine-steps. -/
def execProgLoop : Nat → MultiConfig → Choices →
    Except GoError (ExecOutcome × Choices)
  | fuel, m, choices =>
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
                      execProgLoop fuel m' choices'

/-- **The `execStmt`-shaped POOL wrapper** (D8's carrier swap): run
`prog` as goroutine 0 of a fresh pool over `σ`. For programs that never
spawn this is `execStmt` verbatim (`execProg_single_eq_execStmt`,
MultiSound.lean — the sequential-conservation transfer lemma). -/
def execProg (fuel : Nat) (env : LocalEnv) (σ : ExecState) (choices : Choices)
    (prog : Stmt) : Except GoError (ExecOutcome × Choices) :=
  execProgLoop fuel ⟨#[.exec prog env .stop], σ, 0⟩ choices

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
  match ← execProgLoop fuel ⟨#[c₀], s₀, 0⟩ choices₁ with
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
executable instantiation — `stepMulti_sound`/`stepM_complete`). Four
rule classes: an ordinary/spawn goroutine step (`thread`), parking on a
partnerless blocked outcome (`park`), the arrival-intercept handoff
(`pair` — the L4 waiter pick is the rule's `idx`), and the wake of a
parked goroutine (`wake`). Deadlock is relation-SILENT (no rule from an
all-asleep pool), mirroring the sequential machine's silent blocked
configs. -/
inductive StepM : MultiConfig → MultiConfig → Prop where
  | thread {m : MultiConfig} {i : Nat} {c : Config} {c' : Config} {σ' : ExecState}
      {efs : List Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      StepE c m.shared c' σ' efs →
      isBlockedConfig c' = false →
      StepM m ⟨(m.threads.setIfInBounds i c') ++ efs.toArray, σ', i⟩
  | park {m : MultiConfig} {i : Nat} {c bc : Config} {σ' : ExecState} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      StepE c m.shared bc σ' [] →
      isBlockedConfig bc = true →
      pairCandidates σ' m.threads i bc = .ok [] →
      StepM m ⟨m.threads.setIfInBounds i bc, σ', i⟩
  | pair {m : MultiConfig} {i : Nat} {c bc : Config} {σ' σ'' : ExecState}
      {cs : List (Nat × PairTarget)} {idx : Nat} {ts' : Array Config} :
      schedPick m i →
      m.threads[i]? = some c →
      isBlockedConfig c = false →
      StepE c m.shared bc σ' [] →
      isBlockedConfig bc = true →
      pairCandidates σ' m.threads i bc = .ok cs →
      (hidx : idx < cs.length) →
      applyPairing σ' m.threads i bc cs[idx] = .ok (ts', σ'') →
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
sequential `MachineWf`'s components, thread-indexed. -/
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
