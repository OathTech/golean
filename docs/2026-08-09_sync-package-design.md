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
against `go run` exit 2 + leading `fatal error: <msg>` (exactly the
deadlock terminal's pattern, which is also a gc fatal). Options
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
  recoverable panic `sync: negative WaitGroup counter` (p04); delta >
  0 ∧ old counter = 0 ∧ parked `wgWait` waiters exist on this cell →
  recoverable panic `sync: WaitGroup misuse: Add called concurrently
  with Wait` (gc `waitgroup.go:120`; needs pool visibility, so this
  one check runs at the pool layer where parked shapes are visible —
  the arrivalPlan precedent for pool-visible op semantics); else
  proceed, with HB release iff delta < 0 (gc releases before the
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

All releases are merge-joins (gc uses overwrite `Release` where
exclusivity makes it equivalent, merge where concurrency demands it;
merge is sound in both and equal under exclusivity — recorded). The
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
clean this slice.

## 7. Frontend surface

`import "sync"` stops being a whole-package refusal; the emitter
recognizes EXACTLY: the four types (as `Ty.sync` wire nodes, zero
values included, embedded-struct fields included), method calls
`Lock/Unlock` on `sync.Mutex`, `Lock/Unlock/RLock/RUnlock` on
`sync.RWMutex`, `Add/Done/Wait` on `sync.WaitGroup` (Done →
`wgAdd(-1)`), `Do` on `sync.Once` (the §3 desugar), with receivers
lowered to addresses via go/types. EVERYTHING else under `sync.`
fails closed per-decl with a precise reason (`sync.OnceFunc`,
`WaitGroup.Go`, `TryLock/TryRLock/RLocker`, `Locker`-interface
dispatch, `Cond`, `Map`, `Pool`, copies into interfaces that would
need method dispatch). Receivers that are unaddressable or reached
through unsupported shapes fail closed, never approximate.

## 8. Recorded approximations / known narrowings (each at its site)

- **U4 (new, Race.lean inventory):** sync-OBJECT data accesses inside
  ops are not modeled (gc: `race.Read(&rw.w)` on every RWMutex op,
  `_ = m.state` in Mutex.Unlock) — a program racing a WRITE to the
  sync variable itself against ops on it can be TSan-red / ours-green.
  Misuse-only (such a program is also vet-red); joins U1–U2 in the
  racy lane's scope caption.
- **WaitGroup "reused before previous Wait has returned"**
  (`waitgroup.go:213`): gc can fire this panic in the WOKEN WAITER
  when the counter moves in its wake window (sub-registry timing). Our
  model realizes those schedules as the ADD-side misuse panic (§4) or
  as the waiter staying parked; the waiter-side panic message is a gc
  realization our envelope does not contain. Misuse-only, recorded at
  the `wgAdd` rule site.
- **Fatal-path HB edges:** gc releases before its unlock-path fatal
  checks; we model no edge on fatal paths (the run aborts — no
  observable difference).

## 9. Out of scope, recorded (not silently dropped)

Per D4: `sync/atomic` (own arc — FairStream's gate), `sync.Map`,
`sync.Cond` (blocks `unittest/condvar.go` + `unittest/locks.go` of the
phase-2 files), `sync.Pool`. Additionally recorded here: `TryLock`/
`TryRLock` (§6's class-boundary reason; also unused by the 17 files),
`RLocker`, `sync.Locker` interface dispatch, `WaitGroup.Go` (1.25
sugar), `OnceFunc`/`OnceValue`/`OnceValues`, migrating the
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
