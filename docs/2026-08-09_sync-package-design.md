# The sync package — slice-2 design note (2026-08-09, spec-parity arc)

Status: design of record for spec-parity slice 2 (charter
`docs/2026-08-09_spec-parity-arc-charter.md`, work-plan item 2; scope
D4 as decided — `sync.Mutex`/`RWMutex`/`WaitGroup`/`Once` IN;
`sync/atomic`, `sync.Map`, `sync.Cond`, `sync.Pool` OUT, recorded in
§9). Every "gc does X" claim below is PROBED on go1.26.5
(`.tmp/sync-probes/p01..p17`, run 2026-08-09 with the repo-local
GOCACHE) or read from the gc sources at `/usr/local/go/src/sync/` +
`/usr/local/go/src/internal/sync/mutex.go` (the race-hook inventory) —
never inferred. The channels-arc registry growth contract
(`docs/2026-08-06_channels-arc-design.md` D2+D3) is the binding frame:
each primitive is added by REGISTERING it — a scheduling point + an HB
edge rule — with no change to the scheme, the sequential machine, or
existing statements.

## 1. The memory-model happens-before rules (verbatim, from the
package docs gc ships — the memory model page defers to them)

- **Mutex** (`sync/mutex.go`): "In the terminology of [the Go memory
  model], the n'th call to [Mutex.Unlock] 'synchronizes before' the
  m'th call to [Mutex.Lock] for any n < m. A successful call to
  [Mutex.TryLock] is equivalent to a call to Lock. A failed call to
  TryLock does not establish any 'synchronizes before' relation at
  all."
- **RWMutex** (`sync/rwmutex.go`): "In the terminology of [the Go
  memory model], the n'th call to [RWMutex.Unlock] 'synchronizes
  before' the m'th call to Lock for any n < m, just as for [Mutex].
  For any call to RLock, there exists an n such that the n'th call to
  Unlock 'synchronizes before' that call to RLock, and the
  corresponding call to [RWMutex.RUnlock] 'synchronizes before' the
  n+1'th call to Lock." ALSO API semantics, not just implementation
  (`rwmutex.go` header): "If a goroutine holds a RWMutex for reading
  and another goroutine might call [RWMutex.Lock], no goroutine should
  expect to be able to acquire a read lock until the initial read lock
  is released" — and at `Lock`: a blocked Lock excludes new readers
  from acquiring the lock. The writer-exclusion of new readers is
  documented behavior and is modeled (§4).
- **WaitGroup** (`sync/waitgroup.go`, at `Done` and `Go`): "In the
  terminology of [the Go memory model], a call to Done 'synchronizes
  before' the return of any Wait call that it unblocks."
- **Once** (`sync/once.go`): "In the terminology of [the Go memory
  model], the return from f 'synchronizes before' the return from any
  call of once.Do(f)."

## 2. The panic surface — PROBED, per the twice-burned rule

| probe | program | gc (go1.26.5) |
|---|---|---|
| p01 | `m.Unlock()` on unlocked Mutex, deferred recover | **`fatal error: sync: unlock of unlocked mutex`, exit 2 — recover does NOT catch** (runtime `fatal`, not a panic) |
| p02 | RWMutex `Unlock` without `Lock` | `fatal error: sync: Unlock of unlocked RWMutex`, exit 2, unrecoverable |
| p03 | RWMutex `RUnlock` without `RLock` | `fatal error: sync: RUnlock of unlocked RWMutex`, exit 2, unrecoverable |
| p04 | `wg.Done()` at counter 0, deferred recover | **recoverable panic** `sync: negative WaitGroup counter` (a real `panic()`) |
| p13 | recovered negative-counter panic, then `wg.Wait()` in another goroutine | Wait BLOCKS (deadlock) — gc updates the counter BEFORE panicking; the recovered state keeps the negative counter, and Wait unblocks only at exactly 0 |
| p05 | `once.Do(f)` with panicking f; then `once.Do(g)` | the panic propagates out of `Do` (recoverable); **f counts as completed** — g is never called (doc: gc sets done in a defer) |
| p06 | `m.Lock(); m.Lock()` single goroutine | `fatal error: all goroutines are asleep - deadlock!`, exit 2 — the EXISTING deadlock terminal |
| p07 | `wg.Add(1); wg.Wait()` single goroutine | deadlock fatal, same line |
| p08 | nested `o.Do(f)` where f calls `o.Do` | deadlock fatal, same line (doc: "if f causes Do to be called, it will deadlock") |
| p09 | Lock in main, Unlock in another goroutine | OK — "A locked Mutex is not associated with a particular goroutine" |
| p10 | copy a LOCKED mutex; unlock the copy, unlock the original | both succeed — **value semantics: the copy carries the state** (vet flags it; the runtime does not) |
| p14 | two goroutines `RLock; x++; RUnlock`, temporally serialized, no sync edge | `-race` FLAGS it — TSan's rwlock model gives readers no mutual HB even when serialized (drives the two-clock design, §5) |
| p15/p16/p17 | mutex-protected write / WaitGroup edge / Once edge litmus | all `-race` green (the HB edges to pin in the litmus lane) |

Not probed (racy-by-nature, gc source read instead —
`waitgroup.go:118-132,213`): the recoverable panics
`sync: WaitGroup misuse: Add called concurrently with Wait`
(condition in `Add`: waiters parked && delta > 0 && counter went
0 → delta) and `sync: WaitGroup is reused before previous Wait has
returned` (fires in the WOKEN waiter when the counter moved after its
semrelease). Disposition in §4 (WaitGroup) and §8 (known narrowing).

**Decision (fatal class): model gc's unrecoverable sync throws as a
real terminal, `GoError.fatal msg`** — status `fatal`, message = gc's
fixed string, differentially testable as `expected_status: fatal`
against a failing `go run` whose FIRST `fatal error: <msg>` line is
extracted and compared (the panic path's actual-message discipline —
audit fix round F8; arc-end correction 2026-08-10: "leading line" was
false for a fatal raised DURING PANIC UNWINDING — `defer m.Unlock()`
in a panicking frame — where gc LEADS with `panic: <value>` and puts
the fatal on a TAB-indented continuation line, still exit 2. The
extractor accepts exactly that one indented shape; pinned by
`sync/mutex-unlock-fatal/during-panic-unwind`. Recorded narrowing §8:
the model's `fatal` observation carries the fatal alone — the pending
panic VALUE gc prints on its leading line is dropped, so the
differential compares the fatal class+message, not the panic line)
and whose trailing `exit status 2` report is
checked (delta-review round 2: `go run` itself exits 1 and reports the
child's status as text — measured; the report line is the pin). Options
considered: (a) `.unsupported` refusal like the go-of-nil-func
precedent — rejected: gc's behavior here is UNambiguous (probed, fixed
message), and "fail closed on what's ambiguous" cuts the other way:
refusing a probed, deterministic, differentially-checkable behavior
would leave misuse guardrails permanently red and unverified; (b) a
recoverable panic — rejected outright, refuted by p01-p03 (this also
refutes the charter bullet's parenthetical "real recoverable panics
(unlock-of-unlocked etc.)" — unlock-of-unlocked is exactly the
UNrecoverable class; the charter text predates the probe). The
go-of-nil-func fatal is NOT migrated to the new class in this slice
(scope discipline; recorded in §9).

## 3. Machine shape — sync state as VALUES (the copy question answered
by p10)

`sync.Mutex`/`RWMutex`/`WaitGroup`/`Once` are Go STRUCTS with value
semantics; p10 shows copies carry state and the runtime detects
nothing (copy-after-use detection is `go vet`, best-effort, not
runtime behavior). Decision: **model, don't refuse** — one new value
constructor

    GoValue.syncData (p : SyncPrim)
    SyncPrim := mutex (locked) | rwmutex (writer) (readers) (pendingW)
              | waitGroup (counter : Int) | once (started done : Bool)

living in the heap cell where the variable lives (`Ty.sync kind` with
the zero value = zero primitive — "The zero value for a Mutex is an
unlocked mutex"). A struct copy copies the state — gc's behavior for
free; no reference cell, no registry of mutexes. Ops address the cell
through the method receiver's ADDRESS (all sync methods have pointer
receivers; the frontend emits `&recv` for addressable receivers,
exactly go/types' auto-address-of). Copy-after-use mis-programs
therefore behave as gc's runtime behaves, not as vet advises — the
faithful choice; vet-level static refusal is recorded as a non-goal.
(One narrowing, recorded in §8: gc's `-race` instruments reads OF the
sync object itself inside ops (`race.Read(&rw.w)`, `_ = m.state`),
which catches data races between an op and a WRITE to the sync
variable (e.g. overwriting a mutex while another goroutine locks it).
We do not model sync-object data accesses — U4.)

Op family (the `chanStK` mold, one new `Cont` family + one new `Stmt`
node, statement-position only — every in-scope method returns
nothing):

    Stmt.syncStmt (op : SyncOp) (args : List Expr)
    SyncOp := lock | unlock | rlock | runlock | wlock | wunlock
            | wgAdd | wgWait | onceBegin (target) | onceComplete

`Cont.syncStK op done rest env k` evaluates operands left-to-right
(arg 0 = the receiver address; `wgAdd` arg 1 = the delta);
`applySyncOp` at the apply position returns a CONFIGURATION (proceed /
panic / block / throw fatal) — `applyChanOp`'s exact signature. The
apply position joins `Config.atBoundary` (the registry's scheduling
point); blocking returns the ONE new blocked shape
`Config.blockedSync (op) (loc) (env) (k)`.

**Once is lowered by the frontend** (the range-over-channel /
`$deferClose` desugar precedent — a frontend concern, quarantined
outside GoCore): `once.Do(f)` becomes

    $onceF := f                      -- operand evaluated once, in order
    $onceStarted := onceBegin(&o)    -- blocks while started ∧ ¬done;
                                     --   false if done; true (and marks
                                     --   started) if fresh
    if $onceStarted {
        defer $onceDone(&o)          -- synthetic one-parameter closer
                                     --   wrapping onceComplete (the
                                     --   $deferClose precedent)
        $onceF()
    }

so f's PANIC path rides the existing defer machinery: `onceComplete`
runs during unwind, marking done — p05's "a panicking f counts as
completed" for free, no new panic-walk machinery. Nested `Do` on the
same Once: the inner `onceBegin` sees started ∧ ¬done and parks; a
single goroutine parked on itself is the deadlock terminal — p08 for
free. `onceBegin`'s target is always a fresh frontend temp (plain
local store).

## 4. Per-primitive operational rules (each argued from the probed
surface)

- **Mutex.** `lock`: cell unlocked → locked (HB acquire); locked →
  `blockedSync`. `unlock`: locked → unlocked (HB release); unlocked →
  `GoError.fatal "sync: unlock of unlocked mutex"` (p01). No owner
  tracking (p09 — unlock by another goroutine is legal; gc keeps no
  owner).
- **RWMutex.** State (writer, readers, pendingW). `wlock`: free and
  readerless and → writer (acquire semA + semB); else park and count
  itself in `pendingW` (the park step increments; the acquire
  decrements). `rlock`: `¬writer ∧ pendingW = 0` → readers+1 (acquire
  semA); else park — pendingW > 0 blocking new readers is the
  DOCUMENTED writer-exclusion rule (§1), and it is exactly why a
  pending-writer COUNT must live in the cell (the design rule "no
  waiter queues in the primitive state unless the model forces it" —
  this is the one forced scalar; it is a count, not a queue: no
  ordering, no identities). `wunlock`: writer → free (release semA);
  else `fatal "sync: Unlock of unlocked RWMutex"` (p02). `runlock`:
  readers > 0 → readers−1 (release semB); else
  `fatal "sync: RUnlock of unlocked RWMutex"` (p03; gc fatals on
  RUnlock-of-write-locked the same way — readers = 0 covers it).
- **WaitGroup.** Counter `Int`. `wgAdd delta`: counter += delta FIRST
  (p13 — the update lands before any panic), then: new counter < 0 →
  recoverable panic `sync: negative WaitGroup counter` (p04); a
  ZEROING add additionally resets the waiter count in the same atomic
  step (gc `waitgroup.go:134-135` — audit fix round F3; gc's Add-side
  misuse panic at waitgroup.go:120 is thereby unreachable at registry
  granularity and carries NO arm, per the record at the rule site);
  else proceed, with HB release iff delta < 0 (gc releases before the
  panic check — a recovered negative-counter Done still released;
  modeled). `Done()` is frontend-lowered to `wgAdd(-1)` (gc's own
  definition). `wgWait`: counter = 0 → proceed (HB acquire — also on
  the never-blocked fast path, gc `waitgroup.go:172`); counter ≠ 0 →
  park (negative counters keep waiters parked — p13's deadlock).
- **Once.** `onceBegin`: ¬started → started := true, store `true`, no
  edge; started ∧ done → store `false`, HB acquire; started ∧ ¬done →
  park. `onceComplete`: done := true, HB release. Wake of a parked
  `onceBegin`: done → resume storing `false` with the acquire.

## 5. The HB realization (TSan's realized edge set, per the standing
detector-alignment decision; hooks read from gc sources)

gc's hooks: Mutex.Lock success → `race.Acquire(&m)`; Mutex.Unlock →
`race.Release(&m)` (`internal/sync/mutex.go:64,190`). RWMutex.RLock →
`Acquire(&readerSem)`; RUnlock → `ReleaseMerge(&writerSem)`; Lock →
`Acquire(&readerSem) + Acquire(&writerSem)`; Unlock →
`Release(&readerSem)` (`rwmutex.go:78,117,159-160,204`). WaitGroup:
`Add` with delta < 0 → `ReleaseMerge(wg)`; `Wait` returning at
counter 0 → `Acquire(wg)`; plus the misuse-detection pair `Add`
(delta > 0, counter 0 → delta) → `race.Read(&wg.sema)` vs `Wait`
first-waiter registration → `race.Write(&wg.sema)`
(`waitgroup.go:81,111-116,172,185-190`). Once: realized through its
internal mutex + atomic done (release at completion incl. the panic
defer; acquire at every observing Do return).

Model (`RaceState` extension, the `ChanClocks` mold): per-sync-cell
clock pair `semA`/`semB` —

- semA: released by `unlock`/`wunlock`/`wgAdd(δ<0)`/`onceComplete`;
  acquired by `lock`/`wlock`/`rlock`/`wgWait`-return/
  `onceBegin`-observing-done. (For Mutex/WaitGroup/Once only semA is
  ever touched — one clock, the §1 Mutex/WaitGroup/Once sentences.)
- semB: released by `runlock` (ReleaseMerge — concurrent readers
  JOIN, the p14-driving distinction), acquired by `wlock` only — the
  §1 RWMutex sentence's second half ("the corresponding call to
  RUnlock 'synchronizes before' the n+1'th call to Lock"), and
  exactly why reader-reader pairs stay HB-unordered (p14: TSan flags
  serialized readers; a single-clock model would silently order
  them).

All releases are merge-joins (CORRECTED at the audit fix round F2 and
made SEMANTIC at delta-review round 2: merge equals gc's overwrite
`Release` at a release exactly when semA ⊑ the unlocker's clock —
entailed program-wide by strict lock-handoff discipline; neither
"previously acquired" nor "is the current holder" suffices per-unlock.
On owner-free cross-goroutine unlocks TSan drops the prior section's
clock and over-reports relative to the memory-model text. Recorded as
Race.lean's U5; the merge stays — it is the spec sentence verbatim). The
WaitGroup misuse pair is modeled as a per-cell shadow (`chanObjAccess`
mold): the Add-side READ and first-waiter WRITE, check-then-record —
keeping `-race` refusal alignment for Add-racing-Wait programs.
Edges dispatch in `raceUpdate` (the registry's second duty), classified
from the pre-step shape exactly like the channel arms: apply-position
success edges, wake edges at resume, no edge on park, no edge on the
fatal paths (the run aborts). Sync-cell loads/stores join the
inventory's SYNCHRONIZATION category (never data footprint).

## 6. Blocked shape, wake, and the scheduling story — NO new Choices
sites

Blocked sync ops are `Config.blockedSync` shapes (the D7 discipline:
no waiter queues in the primitive state; `pendingW` is the one
documented-behavior-forced scalar, §4). Wake is CELL-BASED
(`wakeReady` arms): parked `lock` ready iff unlocked; `wlock` iff
free ∧ readerless; `rlock` iff ¬writer ∧ pendingW = 0; `wgWait` iff
counter = 0; `onceBegin` iff done. `resumeThread` re-attempts the op
and must succeed (it runs in the same pool step as the wake-ready
scheduling pick — no window; unready resume is `.internal`, the
channel arms' discipline).

**The wake-order envelope is entirely L1.** Unlike channels there is
no rendezvous data transfer, so sync needs NO arrival intercept, NO
pairing step, and NO L4-analogue waiter pick: an unlock simply makes
parked contenders wake-ready, and WHICH contender (or barging
new arrival) acquires next is decided by the EXISTING L1 scheduler
pick at the next boundary. Envelope statement (shipped at the
`applySyncOp` site): the spec/package docs say nothing about
acquisition order among contenders (no fairness, no FIFO — gc
realizes semaphore-FIFO handoff WITH barging, one legal point);
envelope = every interleaving of registry-granularity schedules over
runnable goroutines, which contains both gc's handoff-to-oldest-waiter
member (schedule: parked waiter picked at the unlock boundary) and
every barging member (schedule: an arriving locker picked first).
Sound in the ⊇ direction because acquisition order is exactly
run-order of the acquire steps, and L1 admits all run-orders.
CONSEQUENCE: sync adds ZERO new `Choices` consumption sites — the
doctrine's canonical list is unchanged; the new boundaries only give
the EXISTING L1 site more consultation points, consumed (as always)
only at |runnable| > 1. Sequential conservation: a single-thread
`lock/unlock` never blocks and never consults the stream
(|runnable| = 1 at every boundary) — the conservation theorem's
hinge untouched.

**FairStream / termination class (the charter's required precision).**
Sync ops BLOCK: a contender that cannot acquire is PARKED and
unrunnable — it never spins, so the pick tree of a
blocking-discipline program stays finitely-branching with no new
infinite-branch source, and the ∀-stream `TerminatesNormallyC` class
(the finite-pick-tree class, `docs/2026-08-07_fairness-precision-note.md`
§1) is UNCHANGED by this slice: mutex/RWMutex/WaitGroup/Once programs
whose every schedule terminates still terminate on every stream
without any fairness assumption. What this slice does NOT add:
spin-waiting THROUGH contention (e.g. `TryLock` retry loops, or
mutex-protected polling of a flag in a `for` loop) — such a spinner is
RUNNABLE forever on unfair schedules, ∀-stream termination is honestly
FALSE for it, and the additive `FairStream` quantifier that would
cover it is parked to the atomics arc as decided (D5). `TryLock`
itself is out of scope (§9) precisely so this class boundary stays
clean this slice. (LANDED 2026-09-03 — Q-TRYLOCK, rulings row 5, lane
`q-trylock`: TryLock/TryRLock modeled with mem#locks' spurious-failure
member as the width-2 `ChoiceSite.tryLock`; the class boundary holds
as stated — spin rows ride the membership lane under `nonterm=`
accounting with NO termination claim.)

## 7. Frontend surface

`import "sync"` stops being a whole-package refusal; the emitter
recognizes EXACTLY: the four types (as `Ty.sync` wire nodes, zero
values included, embedded-struct fields included), method calls
`Lock/Unlock` on `sync.Mutex`, `Lock/Unlock/RLock/RUnlock` on
`sync.RWMutex`, `Add/Done/Wait` on `sync.WaitGroup` (Done →
`wgAdd(-1)`), `Do` on `sync.Once` (the §3 desugar), with receivers
lowered to addresses via go/types.

Method sets and interfaces (REWRITTEN at the arc-end fix round,
2026-08-10 — the original paragraph claimed "copies into interfaces
that would need method dispatch" fail closed, which was FALSE: the
boxing exported silently and satisfaction answered a wrong "no" with
status ok, the worst class — wrong comma-ok bool, wrong type-switch
branch, fabricated missing-method panic, all verifier-reproduced;
dispatch through a USER-defined interface additionally escaped the F4
quarantine and landed as runtime `stuck`): the four types' FULL
exported pointer method sets now ride the wire as declaration-only
stubs (`syncMethodStubs`, the D5 shape with a FAIL-THE-EXPORT posture
on un-emittable signatures — `Ty.sync` has no not-recorded refusal
lane, so a skipped set would silently reproduce the false "no").
Satisfaction/boxing/type-switch ANSWER what gc answers, for
user-defined interfaces and `sync.Locker` alike (`sync.Locker` is
emitted as a plain named interface — also needed by `RLocker`'s
signature); a CALL through any stub refuses per-stub with a precise
frontend-quarantined reason. Pinned by `sync/satisfaction`,
`sync/satisfaction-locker-sig`, `sync/iface-dispatch` (markers),
`sync/stub-satisfaction` (the embedding shape). EVERYTHING else under
`sync.` fails closed per-decl with a precise reason (`sync.OnceFunc`,
`WaitGroup.Go`, `TryLock/TryRLock/RLocker` as CALLS, `Cond`, `Map`,
`Pool`). Receivers that are unaddressable or reached through
unsupported shapes fail closed, never approximate.

## 8. Recorded approximations / known narrowings (each at its site)

- **R1 (audit fix round, F1 — RWMutex unlock-handoff successor
  divergence):** the model's `pendingW` exclusion attaches to every
  PARKED writer; gc's attaches only to the `rw.w`-owning writer, and
  gc's write-Unlock semreleases every parked reader BEFORE the next
  writer can announce (rwmutex.go:143-155, 206-217) — so at the
  both-parked state gc's successor is deterministically reader-first
  where the model's is writer-first. The ACQUISITION-ORDER envelope is
  unaffected (the reader-first member arrives via the direct-order
  schedules; no model-only deadlock exists — `wunlock` leaves
  readers = 0, so the pending writer is wake-ready exactly when the
  reader would have been), certified by sync/rwmutex-order/acquisition
  (members {10, 20}, BOTH gc-witnessed — plain sampling is 10-dominant
  with rare 20s, -race sampling near-even; delta-review round 2
  corrected the earlier "gc's realized 10" phrasing).
  **R1's VALUE-observable half (Q-TRYLOCK audit fix round F1,
  2026-09-03):** the same one-flag approximation — `pendingW` counts
  every parked writer, gc's exclusion belongs only to the `rw.w` owner
  who has passed `readerCount.Add(-rwmutexMaxReaders)` (rwmutex.go:152;
  a writer queued behind `rw.w.Lock()` at :150 has not touched
  `readerCount`) — becomes a RETURN VALUE with `TryRLock`: at the model
  state (writer = false, readers = 0, pendingW > 0) gc's TryRLock is
  TRUE when the pending writer is queued behind `rw.w`
  (`docs/evidence/2026-09-03_q-trylock/probes/` `rwTryRLockQueuedWriter`:
  true 40/40 plain at GOMAXPROCS 1 and 8, 40/40 `-race` at 1, 39/40 at
  8 — the woken writer occasionally reaches :152 first) and FALSE when
  it is past :152 waiting for readers (`rwTryRLockPendingWriter`: false
  20/20). A TryRLock forced false on `pendingW > 0` would therefore
  have been NARROWER than gc at the state level (masked per program:
  {0, 1} ⊇ {1}); the slice widened `tryAcquire`'s acquirability to
  `!writer` (machine ⊇ gc on both phases; an [AGENT] widening in the
  safe direction, RATIFIED [USER] 2026-09-03 («TryRLock decision sounds fine», relayed by the [AGENT] coordinator)). The BLOCKING `RLock` keeps this entry's exclusion (it
  parks on `pendingW > 0`) — and control D shows gc's blocking RLock does
  not honor it either for a queued writer (`rwRLockQueuedWriter`: main's
  RLock returned before the queued writer acquired 40/40 plain at both
  GOMAXPROCS; 17/40 and 20/40 under `-race`, whose scheduler lets the
  woken writer win the race to :152 about half the time) — fresh
  evidence for this entry's ORDER half: the acquisition-order envelope
  still contains both (the reader-first member via the direct-order
  schedules), no new row moves.
- **U5 (audit fix round, F2 — TSan release overwrite-vs-merge):** see
  Race.lean's inventory entry; the merge model is memory-model-exact
  and TSan over-reports on owner-free cross-goroutine unlocks without
  a handoff edge — TSan-red/ours-green, eval-pinned, un-lane-able
  (mixed-oracle class).
- **U4 (new, Race.lean inventory):** sync-OBJECT data accesses inside
  ops are not modeled (gc: `race.Read(&rw.w)` on every RWMutex op,
  `_ = m.state` in Mutex.Unlock) — a program racing a WRITE to the
  sync variable itself against ops on it can be TSan-red / ours-green.
  Misuse-only (such a program is also vet-red); joins U1–U2 in the
  racy lane's scope caption.
- **WaitGroup reuse window** (CORRECTED at the audit fix round, F3 —
  the original entry claimed our model realizes the window as the
  Add-side misuse panic, and §11 claimed that panic was always
  race-preempted; both wrong): gc's ZEROING Add resets the wait count
  before its semreleases (`waitgroup.go:134-135`), so no Add-side
  panic exists in the wake window and gc can be fully CLEAN there
  (probed 10/10 by the verifier; our resume-time retirement panicked
  on exactly those schedules — the two-waiter reuse-window eval pin
  was verified red pre-fix). FIXED: the zeroing Add resets `waiters`
  in the same atomic step, making the sema-pair condition gc-exact and
  the Add-side panic arm dead (REMOVED, with the record at the rule
  site: gc reaches waitgroup.go:120 only through sub-op Wait/Add
  interleavings, realized here as the wg-sema race or as clean runs).
  REMAINING narrowing, recorded: gc's WAITER-side panic ("sync:
  WaitGroup is reused before previous Wait has returned",
  waitgroup.go:213) fires when the counter moves in the woken
  waiter's wake window; our woken waiter instead stays parked until
  the counter is 0 again — a gc realization our envelope does not
  contain, misuse-only.
- **Fatal-path HB edges:** gc releases before its unlock-path fatal
  checks; we model no edge on fatal paths (the run aborts — no
  observable difference).
- **Fatal during panic unwinding drops the pending panic value**
  (arc-end fix round, 2026-08-10): `defer m.Unlock()` in a panicking
  frame — gc's abort LEADS with `panic: <value>` and carries the
  fatal on a tab-indented continuation line (probed; exit 2); our
  `fatal` observation carries the fatal class+message alone, so the
  differential compares those and not the pending panic line. Pinned
  by `sync/mutex-unlock-fatal/during-panic-unwind` (the extractor
  accepts exactly the one indented shape). The message discipline is
  otherwise unchanged; carrying the pending chain in the fatal
  observation is a recorded possible lift, not scheduled.

## 9. Out of scope, recorded (not silently dropped)

Per D4: `sync/atomic` (own arc — FairStream's gate; wave 1 LANDED
2026-09-03), `sync.Map`,
`sync.Cond` (blocks `unittest/condvar.go` + `unittest/locks.go` of the
phase-2 files), `sync.Pool`. Additionally recorded here: `TryLock`/
`TryRLock` as CALLS (§6's class-boundary reason; their method-set
PRESENCE answers satisfaction since the arc-end fix round) — LANDED
2026-09-03 (Q-TRYLOCK, own slice; every spelling — statement discard,
expression value, method value, interface dispatch, promoted receiver —
reaches the one `tryLock` site or refuses), `RLocker`
as a CALL, sync method CALLS through interface dispatch (user-defined
or `sync.Locker`; satisfaction/boxing answer — the call refuses
per-stub; markers `sync/iface-dispatch`; the lift is real stub bodies
over the machine's existing sync ops, recorded in §12) (LANDED
2026-09-01, Q-SYNCVAL slice — P-S2-6 bodied stubs; the modeled ops
dispatch through them, `sync/iface-dispatch` green; unmodeled members
stay declaration-only refusals),
composite-literal construction (`&sync.Mutex{}`, `sync.WaitGroup{}` —
refused naming the capability since the arc-end fix round, was the
internal `sync.noCopy`; markers `sync/composite-literal`; `var` and
`new` are the modeled construction surface) (LANDED 2026-09-01,
Q-SYNCLIT — empty literal ≡ zero value, `sync/composite-literal`
green; NON-empty literals stay refused), `defer wg.Add(n)` /
`defer once.Do(f)` (the deferred-operand shape — an argument evaluated
at defer time and threaded through the synthetic wrapper; Done already
threads a literal -1, so the lift is the natural follow-up) (LANDED
2026-09-01, audit fix round F4 — both spellings now take the ordinary
defer path over the P-S2-6 bodied stubs, receiver and argument
evaluated at defer time, Go's rule),
`WaitGroup.Go` (1.25 sugar), `OnceFunc`/`OnceValue`/`OnceValues`,
migrating the
go-of-nil-func refusal onto the new fatal class (a one-line follow-up,
but it re-pins a recorded permanent red — its own change with its own
reason), vet-style copy-after-use static detection (§3). Of the 17
sync-importing phase-2 goose files, most carry OTHER phase-2/3
blockers (disk FFI, marshal, time, testing, fmt, errors, primitive);
the sync-ONLY files this slice can actually flip are
`semantics/lock.go`, `unittest/synchronization.go`,
`unittest/spawn.go`, `channel/parallel_search_replace` — the tail
(§work-plan 5) lands what it can and records per-file refusal reasons
for the rest.

## 10. Validation plan (guardrails first — work-plan order 2 before 3)

Corpus lanes, all go-run-verified red-first before machine work:
`sync/mutex/*` (lock/unlock discipline, unlock-of-unlocked fatal,
double-lock deadlock, cross-goroutine unlock, copy semantics),
`sync/rwmutex/*` (reader interplay, writer exclusion of new readers,
misuse fatals, RLock-then-Lock deadlock), `sync/waitgroup/*`
(Add/Done/Wait, negative-counter panic incl. p13's
recovered-then-negative shape, Wait deadlock), `sync/once/*`
(once-runs-once, panicking f, nested-Do deadlock, blocking Do),
litmus pairs for each §1 edge (mutex-protected write visible after
Lock; the WaitGroup edge = p16's shape; the Once edge = p17's shape;
each with its racy twin refusing under the racy lane), membership
cases where the L1 latitude is observable (two-contender acquisition
order), confluent cases for deterministic sync programs
(mutex-counter + WaitGroup join). Cases the machine cannot run before
the machine movement classify as visible refusals (frontend-export
stage), never false passes.

## 11. Slice-2 build log (2026-08-09, branch `spec-parity-s2`)

Executed per the charter's order of work (note first, guardrails
second, machine third, lanes fourth, tail fifth). A session crash
interrupted the machine movement mid-proof; the working tree survived
as the verbatim checkpoint 2fc4f4f0 ("WIP (RED, does not build)") and
the next commit completes it — history legible, per the recovery
directive. Decisions made DURING the build, recorded here:

- **The registry growth contract HELD — with one honest qualifier.**
  Sync landed as designed: ONE new blocked shape (`.blockedSync`), one
  new `Cont` family (`syncStK`), new `atBoundary` rows, cell-based
  `wakeReady`/`resumeThread` arms, `raceUpdate` classification arms,
  and ZERO new `Choices` sites (the doctrine's canonical list is
  unchanged; wake order rides L1 — the envelope statement at
  `applySyncOp`). NOTHING in the scheduler scheme, `stepMulti`,
  `StepM`'s rule set, `arrivalPlan`, or any existing statement was
  revised; `stepThread`'s dispatch handles the new shapes through its
  EXISTING branches (blocked → resume; else stepFn). The qualifier:
  "one registry entry, nothing revises" still costs the LOCKSTEP
  sweeps their new cases — the fun_cases positional tags renumbered
  (+3/+7, the probe-derived map), and ~20 proof sites gained sync
  alternatives/refutation arms. That is extension-shaped repair
  (adding cases, never restating), but it is not free; the charter's
  phrasing should be read as "no revision", not "no work".
- **The Once desugar's defer scope (the slice's one real bug, caught
  by the guardrails).** The first `once.Do(f)` desugar inlined
  begin/complete into the CALLER, so the completer's `defer` fired at
  the caller's frame exit — a second `Do` in the same function parked
  forever (`once-basic/runs-once` red; `across-goroutines`' enumerator
  found a deadlock leaf, same root). The fix is the shape gc itself
  has: a per-site synthetic `$onceDo(p, f)` FUNCTION whose own frame
  carries the defer — completion lands when Do returns. Red-first
  paid for itself exactly here.
- **`GoError.fatal` went live end-to-end** (decided in §2): machine
  terminal, observation status, harness `expected_status: fatal`
  (message in expected_reason; go side must die with
  `fatal error: <reason>`), strict-lane only. The four probed sync
  fatals are differentially GREEN, including the recover
  discriminator (a deferred recover does not intervene).
- **The WaitGroup misuse surface, corrected at the audit fix round
  (F3).** This entry originally claimed the misuse shape was
  "intrinsically TSan-racy" so the race "always precedes" the misuse
  panic — REFUTED by the audit's two-waiter counterexample (a channel
  handoff HB-covers the first waiter's sema write while a second
  waiter stays parked: panic with no race, where gc is clean both
  plain and under -race). The honest account: gc's zeroing Add resets
  the wait count (waitgroup.go:134-135), which the model now mirrors,
  making the Add-side panic dead (removed) and the wake window CLEAN
  — pinned by the reuse-window eval pin (verified red pre-fix). What
  remains of the original claim: Add-from-0 beside a parked waiter
  whose sema write is HB-uncovered refuses as the wg-sema race,
  matching -race (the misuse eval pin, stream [1,1,0]). Neither shape
  is corpus-lane-able (mixed plain-green/-race-divergent oracle
  classes); the eval pins are the executable record.
- **Lanes delivered**: 26/28 sync rows green (the 2 reds are the
  PERMANENT out-of-scope refusal markers, Cond + TryLock, now at
  their honest frontend-export stage); race/free-sync 4/4 confluent
  (certified singletons; per-run enumeration figures live in the run
  artifacts — the REPRODUCIBLE record is each row's cases.tsv
  params + lane claim, re-certified on every --diff);
  race/negative-sync 3/3 racy at FULL strength — every enumerated
  path refuses — including the p14 TWO-CLOCK DISCRIMINATOR
  (rlock-serialized: serialized readers stay HB-unordered; a
  single-clock model would have admitted a value leaf and failed the
  lane loudly). The L1 acquisition-order membership case certifies
  {10, 20} with members=2, go sampling plain + -race.
  `waitgroup-workers-join` stays STRICT, recorded: the 3-worker tree
  exceeds the 40M work cap with subtrees unexplored (measured; the
  pipeline/two-stage DPOR-deferral precedent). [2026-09-03: re-measured
  under the POR `engine=dedup` — the state graph does not close either
  (27.1M nodes at the 60M work budget, 39.7 GB); declares `depth=128`
  under the strict-lane depth guard (memo P1) — three seeded 128-entry
  invariance streams verified to cover every wide pick; not an
  invariance certificate — `docs/evidence/2026-09-03_strict-routing/`.]
- **Sequential conservation held with zero effort**: the sync apply
  consumes nothing and single-thread pools never consult the stream
  (|runnable| = 1 at every new boundary), so
  `execProg_single_eq_execStmt`'s statement is untouched and the full
  corpus ran bit-identical on every prior id (zero drift on all 1419
  at both re-pins).
- **Phase-2 tail (the 17 sync-blocked goose files)**: the importer
  gained the explicit `--allow-import <pkg>` seam (fail-closed
  default; "sync" is the first member; per-path allowlist check on
  both import forms). Landed at R1, all GREEN: `semantics/lock`
  (upstream oracle), `unittest/synchronization` (hand wrapper),
  `unittest/spawn` (simpleSpawn; loopSpawn gets NO row — divergent by
  design, probed per the buildout retrospective's lesson 3), and
  `channel/parallel-search-replace` (the 8-worker WaitGroup pool,
  upstream verbatim). The other 13 sync-importing files remain
  blocked, honestly (CORRECTED at the audit fix round: the first
  version listed 12 labels — upstream has TWO wal-shaped files — and
  blamed "OTHER imports" for two files whose only import IS sync):
  disk-FFI/marshal/binary (append_log, logging2, semantics/wal.go,
  wal/log.go, simpledb — 5 files), time/testing/fmt/strconv/errors
  (elimination_stack ×2, etcd_session, lock_test, muxer_test — 5),
  goose-primitive FFI (prims — 1), and sync.Cond USE with no other
  import (condvar, locks — 2, out of scope by D4). R2 pins: none attempted for the concurrent
  imports (allStreamsOk is sequential; the pool checker's fuel trees
  for these shapes are beyond kernel-eval budgets — the R2
  attempt-or-skip judgment the charter delegates).

### Audit fix round (2026-08-10, S2 sub-branch audit: 12 agents, both
majors downgraded on verification, ~10 confirmed/downgraded minors)

Finding-by-finding record — the themes and dispositions:

- **F1 (RWMutex unlock-handoff, downgraded major)**: realization kept
  (the verifier showed the acquisition-order envelope contains gc's
  deterministic reader-first member via direct-order schedules, with
  no model-only deadlock); recorded as §8 R1; the `applySyncOp`
  envelope docstring scoped to acquisition-order granularity; pinned
  by the new tier=slow membership row sync/rwmutex-order/acquisition
  (certified {10, 20}, tracked record in baselines/certified/).
- **F2 (TSan release overwrite-vs-merge)**: merge kept (memory-model
  text verbatim; TSan over-reports on owner-free cross-goroutine
  unlocks); §8 U5 + Race.lean inventory entry; SyncClocks docstring
  corrected from "exclusivity" to lock-handoff discipline; the
  TSan-red/ours-green shape eval-pinned (un-lane-able mixed-oracle
  class).
- **F3 (WaitGroup reuse window)**: FIXED — the zeroing Add resets the
  waiter count in the same atomic step (waitgroup.go:134-135); the
  Add-side misuse panic arm became dead at registry granularity and
  was REMOVED with the record; the two-waiter reuse-window eval pin
  verified red pre-fix, green post; §4/§8/§11 claims corrected (the
  "intrinsically TSan-racy / always precedes" sentence was refuted).
- **F4 (promoted/method-value/go/defer sync escapes landed as runtime
  `stuck`)**: fail-closed now — the resolved-method guard quarantines
  every escape per-decl at the frontend (visible frontend-export
  refusals; four permanent marker cases in sync/escapes); promoted
  wrappers over sync methods became declaration-only quarantined
  stubs (satisfaction answers, calls refuse — no dangling
  `sync.Mutex.Lock` bodies, TryLock stub included). Lifting the
  promoted STATEMENT-position shape (raft's MemoryStorage idiom) is
  the recorded follow-up.
- **F5 (pendingW zero coverage)**: the rwmutex-order row exercises
  rlock parking/wake and both acquisition orders; the probed-but-
  unpinned RUnlock-while-write-locked fatal gained its strict row.
- **F6/F7/grants (--allow-import)**: the vet REWRITTEN fail-closed
  (strict gofmt-shape recognizer; any unrecognized import-shaped line
  refuses — the zero-path pass is gone), three fixtures added
  (accept-with-grant incl. the per-file grant line,
  reject-second-package, reject-unparsable-form), the grant recorded
  per landed file (`// imports-allowed:` header) and re-checked by
  check-imported-goose on every gate (negative-tested).
- **F8a (fatal-lane message)**: the compared observation now carries
  gc's ACTUAL leading fatal line (`fatal_message`, the panic path's
  extractor discipline; the first fix round also caught that worker
  processes need the helper in the `export -f` list).
- **F8b (records)**: the 12-vs-13 blocked-file list and the condvar/
  locks umbrella reason corrected above; the abbd0d13 re-pin header's
  "(Cond, TryLock) move" overstated — only TryLock moved stage (Cond
  was already frontend-export); the historical header stands, this
  line is its correction of record. The two completion-only import
  oracles are now marked in their cases.tsv; the five sibling rows'
  budget raises carry in-file notes; the unreproducible run-detail
  figure above was replaced by the tracked-record citation.

### Delta-review round 2 (2026-08-10; 1 major + ~7 minors, fixed)

- **MAJOR — the U5 pin was VACUOUS**: the first `syncXUnlockMain_F`
  published BEFORE the spawns, so the spawn edge ordered the pair
  under ANY release rule (the round-2 verifier proved it by mutation
  build: overwrite semA left the whole eval suite byte-identical), and
  its "-race red, verified by the audit" claim was refuted by probe
  (60/60 green). RE-ENCODED as the verifiers' discriminating shape
  (spawns before the publish; owner-free W1 unlock; W2's acquire
  after it): gc -race RED on it (3/3, exit 66 — delta-review probes
  .tmp/verify/u5disc, .tmp/verify-f2/true2.go), machine GREEN on the
  empty stream, and SENSITIVITY MUTATION-TESTED this round (tree copy
  with `semA := vt` overwrite → the pin flips to raceDetected; the
  unpatched tree passes). Docstrings rewritten to the true claims.
- **F4 stub regression pinned**: sync/stub-satisfaction/satisfies —
  interface satisfaction through the promoted-sync stubs answers YES
  (go 4 = machine 4); a dropped/mis-shaped stub flips it to a silent
  false-"no" (the verifier exhibited exactly that with a
  stub-dropping frontend build).
- **F6 round 2**: CR bytes refused outright (legal Go whitespace the
  strict rules missed — the last zero-path pass); the vet gate widened
  beyond line-initial (comment-prefixed imports never reached the vet
  at all) with a zero-output cross-check (loose gate fired + strict
  recognizer silent = die, over-refusal accepted as the fail-closed
  direction); grant WIDTH constrained to the machine-modeled set
  (sync) at both the importer and the standing guard; three new
  fixtures (CR, comment-prefixed, wide grant).
- **F3 precision**: "gc is CLEAN" scoped to the ADD side at all three
  comment sites — gc's misuse detection moves to the WAITER
  (waitgroup.go:213), the recorded §8 narrowing; the reuse-window eval
  pin's non-vacuity claim now names the exact pre-fix state + command.
- **applySyncOp docstring**: the removed Add-side panic no longer
  listed as a wgAdd outcome; the ⊇-gc sentence now carries the
  WaitGroup carve-out beside the RWMutex one; Value.lean's `waiters`
  gloss updated.
- **F2 precondition made SEMANTIC**: merge = overwrite at a release
  iff semA ⊑ the unlocker's clock (program-wide handoff discipline
  entails it inductively; neither "previously acquired" nor "current
  holder" suffices — verifier counterexamples).
- **Certified record honesty**: steps figure re-measured at the
  record's own params on the fixed semantics (2.23M steps/~26s; the
  16.4M figure was the original audit's pre-F3-fix probe — explained
  in the record header, tier=slow stands at the threshold).
- **gc realizes BOTH rwmutex-order members** (round-2 verifier: plain
  297x10/3x20; -race 56/64): the "gc exhibits 10 on every run" texts
  corrected — both certified members are now oracle-witnessed (a
  strengthening).
- **Fatal exit status**: checked, not claimed — `go run` exits 1 and
  reports the child's `exit status 2` as text (measured); the report
  line is the pin.
- Gate discipline note: this branch predates `scripts/capped`; every
  build/gate in both fix rounds ran through the wrapper extracted from
  main into .tmp (the cap arrives in-tree at the arc-merge rebase).

### Delta-review round 3 (2026-08-10; focused — U5 CONVERGED, gates not)

- **MAJOR — the round-2 vet cross-check was FILE-GLOBAL**: one
  recognized import laundered any number of unrecognized ones (the
  round-3 verifier landed `import "sync"` + `/* c */ import "os"`
  under a sync-only grant, and the standing guard certified it).
  FIXED per-occurrence in BOTH scripts: every line the loose gate
  fires on (`//`-comment lines excluded — they cannot carry live
  code) must be a strictly recognized import line; ANY count mismatch
  refuses, at landing and at every standing re-check. Fixtures: the
  dual-form shape in the importer suite AND a hand-assembled
  standing-guard negative test (both green); the 82 landed cases
  re-scanned clean under the fixed accounting; two fresh adversarial
  mixed-form candidates (comment-prefixed block import beside a gofmt
  block; tab-indented comment-prefixed import beside a plain import)
  both die with the per-occurrence message.
- **rwmutex-order cases.tsv aligned** (the round-2 "records made
  honest" miss): the retracted 16.4M/29.5s figures and the singular
  "gc's realized point, 5/5 plain" framing replaced with the measured
  truth (both members gc-witnessed; 2,230,228 steps / ~26s).
- **Reuse-window wording scoped** (U5-area note): the channel-handoff
  causal claim covers W1 only; W2's exclusion from the waiter-side
  panic is probed-empirical (the verifier's 5400-run probe), stated
  as such at both comment sites.
- **Recorded, no action** (verifier note): the standing guard's CR
  check is defense-in-depth behind the importer's landing-time
  refusal, not an independently reachable gate — do not mistake it
  for a second barrier.

### Delta-review round 4 (2026-08-10; escalated CRITICAL — the
STRUCTURAL fix)

- **CRITICAL/majors — the ad-hoc import recognizers are GONE.** Three
  rounds patched line regexes and each round a LEGAL Go import form
  escaped (round 2: indented/one-line-block/no-space; round 3:
  comment-prefixed; round 4's verifier: named/blank/dot forms — four
  fresh bypasses landed AND were certified, plus the importer's vet
  was CONDITIONAL on a loose grep while the guard's was not, so a
  named-only-import file landed with no vetting at all). The round-4
  fix is the verifier's principled one: Go's OWN grammar —
  `tools/lsimports` (go/parser, parser.ImportsOnly; ~50 lines,
  committed, trust argument in its header: the same toolchain already
  trusted as the differential oracle) — run UNCONDITIONALLY by BOTH
  scripts with one invariant: parsed imports ⊆ the allow-set ({sync}),
  parse failure = refuse, and the landed grant line records EXACTLY
  the parsed paths (the standing guard re-derives via the parser and
  compares set-equality in both directions — the tamper direction
  negative-tested). The regex machinery was removed outright rather
  than demoted (it must not gate anything the parser doesn't).
- **Fixtures**: every exhibited bypass class — named, blank, dot,
  comment-prefixed named, tab-indented, trailing-comment, factored
  block with a disallowed mid-block entry, the no-vet-conditional
  shape — refuses in the importer suite; the standing guard's
  laundered-import and tampered-grant negatives fail certification;
  and the PRECISION WIN is pinned: a raw string containing
  import-looking text (zero real imports) now correctly LANDS with no
  grant line, where rounds 1-3 falsely refused it.
- **82-case standing scan green** under the parser-based guard (the
  round-3 verifier's independent go/parser scan already confirmed the
  landed lane clean — the hole was prospective only).
- **Adversarial self-check against the parser** (fresh candidates):
  cgo (`import "C"` with preamble) — parser reports `C`, gate refuses
  by set membership; build-tag-guarded `import _ "sync/atomic"` —
  parser parses through the tag, reports `sync/atomic`, gate refuses.
  Nothing lands.
- **Scope note**: parser.ImportsOnly stops after the import section by
  design; the importer's full-compile self-containment step remains
  the backstop for anything after it.
- **NOTE**: the certified record's gc-sampling header now cites both
  verifier batches per mode, matching cases.tsv's scope.
- **Residue cleanup (post-convergence, schematic)**: the standing
  guard REFUSES any sibling .go file in an imported-goose case dir
  (the stricter line — the importer writes only main.go; multi-file
  packages are legitimate elsewhere in the corpus, never in this
  lane); lsimports refuses control characters in parsed paths (the
  one-path-per-line protocol's injectivity); the grant-token
  iteration is glob-safe with honest messages; and the guard's header
  records that below-marker content is covered by the verbatim diff +
  the differential gate's own corpus compile (a per-dir go build was
  considered and not added — 82 redundant compiles per run). Both
  shapes fixtured (suite now 47).

### Arc-end fix round (2026-08-10, branch `spec-parity` — the arc-end audit's sync findings; red-first throughout)

- **CRITICAL/major — satisfaction false-"no" (BUG-053), quarantine
  escape via user interfaces**: red-first pins exhibited every genre
  (comma-ok 0-vs-21/31/41/61, type-switch 0-vs-12, fabricated
  missing-method panic; user-iface dispatch `stuck`; sync.Locker
  whole-export refusal isolated in `satisfaction-locker-sig` so it
  could not mask the silent-wrong reds). Fix: `syncMethodStubs`
  (frontend-only; fail-the-export on un-emittable signatures, unlike
  D5's skip-whole — no refusal lane covers a skipped `Ty.sync` set) +
  `sync.Locker` as a plain named interface. Post-fix: satisfaction 9/9
  green incl. both definite-no controls; `sync/iface-dispatch` 3
  markers moved stuck→`frontend-export` with per-stub reasons.
- **major — wg panic payload class (BUG-054)**: `stringPanicValue` at
  the `wgAdd` arm (gc panics with package-code string, waitgroup.go:118;
  channels stay `runtimeErrorValue` = `plainError`). Discriminator pin
  3→1032.
- **minor — wg int32 wrap (BUG-055)**: `emod 2^32` wrap before the
  negative test; BOTH divergence directions pinned (`Add(1<<31)`
  missed panic, `Add(-(1<<32))` fabricated panic). Interpreter and
  relation move together through the shared `applySyncOp`; StateWf's
  wgAdd arm re-proved (`stringPanicValue_locSup`); full proof build
  green.
- **minor — fatal during unwinding**: extractor accepts the one
  tab-indented `fatal error:` continuation shape (gc leads with
  `panic: <value>`); §2's "LEADING line" premise corrected; dropped
  pending-panic value recorded as a §8 narrowing; pinned
  (`during-panic-unwind`, red-first at go-observation).
- **notes — composite-literal refusal** now names the capability (was
  `sync.noCopy`), markers `sync/composite-literal`; defer-position
  wording restated capability-scoped (the deferred-operand shape, §9)
  instead of "nothing uses them".
- The rwmutex-order certified record re-certified this round (the
  stub methods change the wire sha — schema-widening only, members
  unchanged {10, 20}).

### Class-closure round (2026-08-10, user direction: BUG-053's fix closed the instance, not the class)

The method-set record contract —
`docs/2026-08-10_method-set-record-contract.md` is the decision record;
BUGS.md BUG-053 carries the addendum; the D5 note
(2026-08-05_embedding-interfaces-design.md) records the guard re-key.
Summary: REQUIRED `methodSets` wire field (one explicit record per
method-carrying type, `full`/`exported` coverage, strict decode);
satisfaction/dispatch/renderer answer ONLY from records
(`methodCarrierKey?`/`methodSetCoverage?`; carrier kinds gc-probed:
`.defined` + `.sync`); no record ⇒ visible `.unsupported`, never an
answer, never stuck. Wire-boundary "MS:" fixtures (7, Tests/GoCoreEval)
pin the class; 12 pinned lowering terms + 3 golden reprs regenerated
(schema-only); both tier=slow certified records re-certified (sets and
stats bit-for-bit); corpus classification unchanged on all 1483 ids
(the contract is vacuously satisfied by today's frontend, as required).

## 12. Parking ledger (user-scale items, per the AFK posture)

- **P-S2-1 — Promote `fatal` into the membership/confluent lanes?**
  `fatal` members currently have no enumeration handling (they fail a
  certification loudly, like deadlock members) and fatal rows are
  strict-only. Nothing needed it this slice; widening is a lane-design
  decision (status-set semantics, -race interaction) → user call.
  Meanwhile: strict-only, loud refusal — reversible.
- **P-S2-2 — Migrate the go-of-nil-func refusal onto `GoError.fatal`.**
  The class now exists; the migration is small but re-pins a recorded
  permanent red (`spawn-edge/nil-func-fatal` would flip) and touches a
  channels-arc decision record → parked rather than flipped
  unilaterally. Meanwhile: the refusal stands unchanged.
- **P-S2-3 — Designated-statement candidates.** None designated
  (charter D3 is CURATED and user-owned). Candidate when the arc's
  proof slices reach sync: a mutex-protected-counter GoSpecC exemplar
  + first-order readout (the natural sync feature-class exemplar).
  The 44 designated statements are byte-identical this slice.
- **P-S2-4 — `valueEqFuel` refuses `==` at sync types.** Go's == IS
  defined on the sync structs (comparable fields); we fail closed
  (unsupported) since any comparison is copy-class misuse with no
  in-scope consumer. If a real target compares sync values, decide
  model-vs-refuse then. Recorded at the arm.
- **P-S2-5 — U4 (sync-object data accesses) scope.** gc's -race
  instruments reads OF the sync object inside ops (`rw.w`,
  `m.state`), catching op-vs-overwrite races we do not model
  (Race.lean inventory U4). Misuse-only; joins U1-U2 in the racy
  caption. Closing it means modeling struct-copy accesses of sync
  cells → future arc if ever needed.
- **P-S2-6 — Lift sync method CALLS through interface dispatch
  (arc-end fix round, 2026-08-10). LANDED 2026-09-01 (the Q-SYNCVAL
  slice, per `docs/2026-08-31_qrow-rulings.md` row 6): bodied stubs
  exactly as scoped below (Do's generic host is the bodied
  `sync.Once.Do` stub itself + a `$syncOnceDone` completer;
  TryLock/TryRLock/RLocker/Go stay declaration-only), plus the
  adjacent method-value/go-callee shapes and the Q-SYNCLIT
  empty-literal lowering (row 7).** [The trailing prose below is the
  PRE-LANDING scoping, kept for provenance — every "refuse"/"stay"
  it states for the modeled ops is superseded by the landing above
  (LANDED 2026-09-01); TryLock/TryRLocker/RLocker/Go declaration-only
  refusals still stand.] Satisfaction/boxing now answer
  correctly through the `syncMethodStubs` declaration-only stubs; the
  CALLS refuse per-stub (markers `sync/iface-dispatch`). The lift is
  real stub bodies over the machine's EXISTING sync ops (Lock/Unlock/
  RLock/RUnlock/Add/Done/Wait as one-statement bodies; Do via a
  generic `$syncOnceDo`; TryLock/TryRLock/RLocker/Go stay
  declaration-only) — semantics-identical to direct calls at registry
  granularity, but it grows the dispatchable surface, so it is a
  scoped slice with its own red-first cases, not a fix-round rider.
  Adjacent: the promoted-call lift (raft's MemoryStorage idiom,
  `sync/escapes/promoted`) and `defer wg.Add(n)`/`defer once.Do(f)`
  (§9's deferred-operand shape — LANDED 2026-09-01, audit fix round
  F4, via the ordinary defer path over the bodied stubs).
