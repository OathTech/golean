import GoLean.GoCore.StepFn

/-!
# Segment-level happens-before race detection — the per-step kit
(channels arc slice 3, D2+D3(b); `docs/2026-08-06_channels-arc-design.md`)

The synchronization-op registry's SECOND duty: execution between
registry ops is a SEGMENT; the pool records each segment's read/write
set at `Loc`-path granularity and advances vector clocks over goroutine
ids on the registry ops' happens-before edges (the memory model's
channel rules, quoted at their implementation sites in `Multi.lean`).
Two HB-unordered conflicting accesses from different goroutines are the
terminal `Stop.raceDetected` — races FAIL CLOSED per run,
deterministically given the stream (the detector is a pure function of
the observed steps; it consumes NO choices).

This file is the pool-independent half: vector clocks, the per-location
shadow (TSan/FastTrack's skeleton — per-loc last-access epochs, one per
goroutine, subsumption by program order), the sync primitives' own
state-word tables (`syncEntryKinds`/`syncReleaseTailKinds`) and the
per-address atomic clocks. The pool half (channel-clock events, the
`raceUpdate` dispatcher, the detecting loop) lives in `Multi.lean`,
which imports this.

WHERE THE DATA ACCESSES COME FROM (C1 S2b, 2026-09-18). The recorded
accesses of a goroutine step are the step's LABEL — what the memory
module's EMITTING operations performed (`Ops.lean`, «The memory module's
access discipline»: `Mem.load`/`loadFor`/`store`/`mapRead`/`mapWrite`/
the element runs/`loadResults`/the dispatch read), carried by `Step` as
its fifth index, by `stepFn` as its fourth component and by the pool
event as `StepEvent.trace`; `raceUpdate` folds it (`RaceState.accessKeys`).
The former FOOTPRINT TABLE of this file — a curated per-shape function
`stepAccesses` from a step's pre-configuration to its accesses
(`strictOpAccesses`, `stmtOpAccesses`, `dispatchAccesses`,
`deferEntryAccesses`, `storeTargetAccess`, `unseqRunAccesses`,
`sliceElemLocs`, `mapAccess`, `targetWrite`, `RaceAccess`,
`RaceState.access/accesses`) and its 250-line call-site inventory — was
DELETED at C1 S2b-ii after (a) the whole-corpus + raft-twin trace-equality
audit found the two accounts equal on every traced step
(`docs/evidence/2026-09-18_c1-memory-module/`, 21,835 + 30 (row, stream)
results, 0 mismatches) and (b) the theorem `accesses_eq_stepAccesses`
(GoLean/GoCore/AccessTableEq.lean at the proving commit named in
`docs/2026-09-18_c1-memory-module-handoff.md` §1) proved every rule's
label EQUAL to the table's account on a non-panicking successor; the
theorem left with the table it audited. The inventory of PEEK sites
(what reads a cell without emitting, and why gc's `-race` build reads
nothing there) now lives in the module's docstring. The recorded
approximations O1 (value-path composite reads whole-cell unless narrowed
by an immediate projection chain — BUG-041, ledger [DL-1]), U2 (`len`/
`cap` on channels record nothing; `len` on a map is a real read), U3
(CLOSED — the channel OBJECT as a shadow location, `chanObjAccess`), U4
(CLOSED — the sync primitives' own state words, BUG-080) and U5
(cross-goroutine unlock without handoff HB: TSan-red / ours-green, ledger
[DL-5]) keep their pins; their statements were relocated to the ledger
entries and the module docstring with the table's deletion.

The recorded UNDER-approximation U5 keeps its statement here, verbatim
from the deleted inventory: **cross-goroutine unlock without handoff HB:
TSan-red / ours-green.** `syncRelease` is a merge-join; gc's TSan hook is
overwrite `race.Release`. The two agree at a release exactly when semA ⊑
the unlocker's clock (entailed by strict lock-handoff discipline); on a
legal owner-free unlock whose unlocker has no HB from the prior critical
section, TSan drops that section's clock and reports a race our merge
keeps ordered. The merge is the memory-model text verbatim (the n<m
Unlock/Lock sentence is unconditional), so the deviation is from the
TSan-alignment oracle in the missed-race direction; scope-limited to
cross-goroutine unlocks without a handoff edge. Provenance, probe and pin:
ledger [DL-5].
-/

namespace GoLean.GoCore.Machine

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)

open GoLean

/-! ## Vector clocks over goroutine ids -/

/-- A vector clock: component `t` is the last-known epoch of goroutine
`t`. Ragged on purpose — absent components read 0 (`get`). -/
abbrev VClock := Array Nat

/-- Component read; absent = 0. -/
def VClock.get (vc : VClock) (t : Nat) : Nat := (vc[t]?).getD 0

/-- Pointwise max (length = max of the lengths). -/
def VClock.join (a b : VClock) : VClock :=
  (Array.range (max a.size b.size)).map fun t => max (a.get t) (b.get t)

/-- Pad to length ≥ `n` with zeros. -/
def VClock.pad (vc : VClock) (n : Nat) : VClock :=
  if vc.size ≥ n then vc else vc ++ Array.replicate (n - vc.size) 0

/-- Set component `t` (padding as needed). -/
def VClock.setC (vc : VClock) (t : Nat) (v : Nat) : VClock :=
  (vc.pad (t + 1)).setIfInBounds t v

/-- Bump goroutine `t`'s own component — the RELEASE-side epoch
increment (FastTrack): accesses after a release are distinguishable
from the ones the release published. -/
def VClock.bump (vc : VClock) (t : Nat) : VClock :=
  vc.setC t (vc.get t + 1)

/-- The birth clock of goroutine `t` before any synchronization: own
component 1 (so its accesses are visibly unordered for every peer whose
view of `t` is still 0), everything else 0. -/
def VClock.birth (t : Nat) : VClock :=
  (Array.replicate (t + 1) 0).setIfInBounds t 1

-- MOVED to `GoLean/GoCore/Ops.lean` (C1 S2a, 2026-09-18): the access
-- vocabulary — `locPrefix`/`locOverlap`, `SyncWordName`, `ShadowKey` and its
-- `overlap` table, `AccessKind` and its `isWrite`/`isAtomic`/`conflicts` — is
-- the memory module's, emitted by its operations (charter §3, D9). The
-- detector below CONSUMES it; nothing here changed meaning.



/-- Last-access epochs at one `Loc` path: at most one entry `(t, e)`
per goroutine per KIND (same-goroutine accesses are totally ordered by
sequenced-before, so the LATEST epoch subsumes older ones for every
future HB test). Four kinds since BUG-080 (`AccessKind`, defined
below): the plain pair the data footprint records and the atomic pair
the sync ops record on their primitive's own path; the chan-object
shadow uses the plain pair only. -/
structure ShadowCell where
  reads : List (Nat × Nat) := []
  writes : List (Nat × Nat) := []
  atomicReads : List (Nat × Nat) := []
  atomicWrites : List (Nat × Nat) := []
  deriving Repr, BEq

/-- Replace-or-insert goroutine `t`'s entry. -/
def ShadowCell.upsert (entries : List (Nat × Nat)) (t : Nat) (e : Nat) :
    List (Nat × Nat) :=
  match entries with
  | [] => [(t, e)]
  | (u, e') :: rest =>
      if u == t then (t, e) :: rest else (u, e') :: ShadowCell.upsert rest t e

/-- The entries of one kind. -/
def ShadowCell.entries (cell : ShadowCell) : AccessKind → List (Nat × Nat)
  | .read => cell.reads
  | .write => cell.writes
  | .atomicRead => cell.atomicReads
  | .atomicWrite => cell.atomicWrites

/-- Record goroutine `t`'s access of kind `k` at epoch `e`. -/
def ShadowCell.record (cell : ShadowCell) (k : AccessKind) (t e : Nat) : ShadowCell :=
  match k with
  | .read => { cell with reads := ShadowCell.upsert cell.reads t e }
  | .write => { cell with writes := ShadowCell.upsert cell.writes t e }
  | .atomicRead => { cell with atomicReads := ShadowCell.upsert cell.atomicReads t e }
  | .atomicWrite => { cell with atomicWrites := ShadowCell.upsert cell.atomicWrites t e }

/-- Does some entry `(u, e)` with `u ≠ t` satisfy `e > vt[u]` — i.e. is
some prior access by another goroutine NOT happens-before goroutine
`t`'s current point? (Prior access at epoch `e` by `u` is ordered
before `t`-now iff `e ≤ vt[u]`.) -/
def ShadowCell.someConcurrent (entries : List (Nat × Nat)) (t : Nat)
    (vt : VClock) : Bool :=
  entries.any fun (u, e) => u != t && e > vt.get u

/-- Does the cell hold, under some kind that CONFLICTS with `k`
(`AccessKind.conflicts`), an access by another goroutine that is not
happens-before goroutine `t`'s current point? -/
def ShadowCell.conflicts (cell : ShadowCell) (k : AccessKind) (t : Nat)
    (vt : VClock) : Bool :=
  [AccessKind.read, .write, .atomicRead, .atomicWrite].any fun k' =>
    k.conflicts k' && ShadowCell.someConcurrent (cell.entries k') t vt

/-! ## The access footprint of one private step -/

-- DELETED (C1 S2b-ii, 2026-09-18): the FOOTPRINT TABLE — `RaceAccess`, `sliceElemLocs`,
-- `mapAccess`, `targetWrite`, `strictOpAccesses`, `dispatchAccesses`, `deferEntryAccesses`,
-- `stmtOpAccesses` — computed a step's data accesses from its pre-configuration; the memory
-- module's operations EMIT them now (Ops.lean, «The memory module's access discipline»), and
-- `accesses_eq_stepAccesses` (GoLean/GoCore/AccessTableEq.lean at the proving commit,
-- `docs/2026-09-18_c1-memory-module-handoff.md` §1) proved the two accounts equal before both
-- left. The module docstring above records where the data accesses come from.

/-! ## The detector state

Vector clocks per goroutine, the per-`Loc` access shadow, and the
per-channel synchronization clocks. The pool threads one `RaceState`
alongside the `MultiConfig` (external instrumentation, like `Choices`
and fuel: it OBSERVES steps and never influences them except by the
terminal `raceDetected` refusal) — deterministic given the stream, no
`Choices` consumption, kernel-reducible plain structures. -/

/-- Per-channel synchronization clocks — gc's race instrumentation
realized (`runtime/chan.go`'s `racenotify`/`racesync`/`racerelease`/
`raceacquire` points), which is what keeps the in-machine
classification structurally aligned with the `go run -race` oracle:

* `slots` — one clock per buffer slot (`max 1 cap`); a buffered send
  RELEASE-ACQUIREs slot `sendCount % size`, a buffered receive slot
  `recvCount % size`. Slot reuse every `cap` operations is EXACTLY the
  memory model's counting-semaphore rule — go_mem: "The kth receive on
  a channel with capacity C is synchronized before the k+Cth send from
  that channel completes" — and the release half of the send slot-op
  is go_mem's "A send on a channel is synchronized before the
  completion of the corresponding receive from that channel."
* `closeVC` — the closer's clock; a receive that returns a zero value
  because the channel is closed ACQUIREs it — go_mem: "The closing of
  a channel is synchronized before a receive that returns a zero value
  because the channel is closed." (A close-woken SENDER's panic gets
  NO edge — deliberately STRONGER than gc's realized HB: gc's
  `closechan` DOES `raceacquireg` the parked sender at the
  "release all writers" loop, exactly as for receivers (the S3 audit
  correction at `raceWakeEvent`, Multi.lean — the closer installs the
  edge; the old justification "gc's woken `chansend` performs no
  `raceacquire`" was true but irrelevant). Moot on refused programs:
  the modeled chan-object pair refuses at the CLOSE first. Docstring
  re-synced 2026-08-22, launch audit N-13.)
* unbuffered rendezvous is the bidirectional `racesync` (both go_mem
  directions at once: send-before-receive AND "A receive from an
  unbuffered channel is synchronized before the completion of the
  corresponding send on that channel"), implemented as
  `RaceState.rendezvous` at the pool's pairing step. -/
structure ChanClocks where
  slots : Array VClock
  sendCount : Nat := 0
  recvCount : Nat := 0
  closeVC : Option VClock := none
  deriving Repr, BEq

/-- Per-sync-cell synchronization clocks (spec-parity slice 2, design
note §5) — gc's race hooks realized, keeping the in-machine
classification aligned with the `go run -race` oracle. The package-doc
memory-model sentences are quoted in the design note §1; the hook
inventory (read from the gc sources at the probe date):

* `semA` — the write-release clock (gc's `readerSem` role for RWMutex,
  the whole clock for Mutex/WaitGroup/Once): RELEASED by
  Mutex.Unlock (`race.Release(&m)`, internal/sync/mutex.go:190),
  RWMutex.Unlock (`race.Release(&rw.readerSem)`, rwmutex.go:204),
  WaitGroup.Add with negative delta (`race.ReleaseMerge(wg)`,
  waitgroup.go:81 — "a call to Done 'synchronizes before' the return
  of any Wait call that it unblocks"), and Once completion (through
  its internal mutex/atomic — "the return from f 'synchronizes
  before' the return from any call of once.Do(f)"); ACQUIRED by
  Mutex.Lock ("the n'th call to Unlock 'synchronizes before' the
  m'th call to Lock for any n < m"), RWMutex.Lock AND RLock
  (rwmutex.go:78,159 — "the n'th call to Unlock 'synchronizes
  before' that call to RLock"), WaitGroup.Wait's return
  (waitgroup.go:172), and a Do return that observed completion.
* `semB` — the read-release clock (gc's `writerSem`): RELEASED by
  RUnlock (`race.ReleaseMerge(&rw.writerSem)`, rwmutex.go:117 — "the
  corresponding call to RUnlock 'synchronizes before' the n+1'th
  call to Lock"), ACQUIRED by RWMutex.Lock ONLY (rwmutex.go:160).
  The two-clock split is what keeps concurrent READERS mutually
  HB-unordered (probe p14: TSan flags serialized readers writing
  under RLock; a single-clock model would silently order them —
  pinned by race/negative-sync/rlock-serialized).

All releases here are merge-joins. CORRECTED at the audit fix round
(2026-08-10, F2; precondition made SEMANTIC at delta-review round 2 —
"previously acquired", and even "is the current holder", are
insufficient: a stray owner-free unlock by a third party can seed the
sem clock with entries the holder's clock lacks): merge and gc's
overwrite `Release` coincide at a release exactly when semA ⊑ the
unlocker's clock at that moment — i.e. the unlocker has already
acquired every prior release into the cell. Program-wide lock-HANDOFF
discipline (every unlock performed by the goroutine whose acquire is
the latest, no owner-free unlocks anywhere) entails that inductively;
no per-unlock syntactic condition does. This slice deliberately models the
shape where that fails (probe p09: a cross-goroutine unlock is legal
and owner-free), and there gc's overwrite DROPS the earlier release's
clock while our merge keeps it — TSan reports a race our detector does
not (the U5 ledger entry in the module docstring; eval-pinned). The
merge model is the MEMORY-MODEL text ("for n < m, call n of
l.Unlock() is synchronized before call m of l.Lock() returns" — 
unconditional), so this is a recorded deviation from the
detector-alignment ORACLE, not from Go. -/
structure SyncClocks where
  semA : VClock := #[]
  semB : VClock := #[]
  deriving Repr, BEq

/-- Update-or-insert in a keyed association list (insertion order). Used by
`chans`/`syncs`/`atomics`: those stay INSERTION-ordered, so the dedup
engine's structural equality is order-sensitive on them — the same latent
lost-merge hazard A6 removed from the shadow (`shadowSet`); OWED, engine
side (A-series audit fix round, 2026-09-04). -/
def assocSet {κ α : Type} [BEq κ] (xs : List (κ × α)) (key : κ) (v : α) :
    List (κ × α) :=
  match xs with
  | [] => [(key, v)]
  | (l, w) :: rest =>
      if l == key then (key, v) :: rest else (l, w) :: assocSet rest key v

/-- Update-or-insert in the shadow, keeping it SORTED by key (A6): two
detector states that record the same cells under the same keys are then
structurally EQUAL whatever order the goroutines first touched the keys
in — the dedup engine (`RaceState.eqb` is structural) merges them. Before
A6 the channel-object shadow was a separate list, which gave this
interleaving-insensitivity for free between data and channel keys; one
list needs it stated, and gets it for every key class at once. -/
def shadowSet : List (ShadowKey × ShadowCell) → ShadowKey → ShadowCell →
    List (ShadowKey × ShadowCell)
  | [], key, v => [(key, v)]
  | (k, w) :: rest, key, v =>
      match compare key k with
      | .lt => (key, v) :: (k, w) :: rest
      | .eq => (key, v) :: rest
      | .gt => (k, w) :: shadowSet rest key v

/-- The detector state: per-goroutine clocks (index = pool goroutine
id; absent = the birth clock), THE access shadow — one `ShadowCell` per
`ShadowKey`: data paths, sync words, and (BUG-045) channel objects (gc's
`c.raceaddr()` instrumentation point, channel identity — exact match; A6
folded the former separate channel-object shadow into this one under
its own key constructor) — and the channel clocks. Empty until the pool
holds a second goroutine — a single goroutine cannot race with itself
(every access is sequenced), so the detector is inert on sequential
runs BY CONSTRUCTION (the conservation theorem's hinge, and the
whole-corpus zero-overhead guarantee). -/
structure RaceState where
  clocks : Array VClock := #[]
  shadow : List (ShadowKey × ShadowCell) := []
  chans : List (Loc × ChanClocks) := []
  /-- Per-sync-cell clock pairs (spec-parity slice 2, `SyncClocks`). -/
  syncs : List (Loc × SyncClocks) := []
  /-- Per-ADDRESS atomic clocks (the atomics arc, wave 1 — the section
  "sync/atomic — the per-address clocks" below): one `VClock` per
  `Loc` a `sync/atomic` op has released into, keyed EXACTLY by the
  addressed cell's path (TSan's `SyncVar` per atomic address). -/
  atomics : List (Loc × VClock) := []
  deriving Repr, BEq

def RaceState.vcOf (r : RaceState) (t : Nat) : VClock :=
  (r.clocks[t]?).getD (VClock.birth t)

/-- Set goroutine `t`'s clock, padding missing peers with their birth
clocks. -/
def RaceState.setVC (r : RaceState) (t : Nat) (vc : VClock) : RaceState :=
  let clocks :=
    if t < r.clocks.size then r.clocks
    else r.clocks ++ (Array.range (t + 1 - r.clocks.size)).map
      (fun k => VClock.birth (r.clocks.size + k))
  { r with clocks := clocks.setIfInBounds t vc }

def RaceState.chanOf (r : RaceState) (loc : Loc) (cap : Nat) : ChanClocks :=
  match r.chans.find? (·.1 == loc) with
  | some (_, cc) => cc
  | none => { slots := Array.replicate (max 1 cap) #[] }

def RaceState.setChan (r : RaceState) (loc : Loc) (cc : ChanClocks) : RaceState :=
  { r with chans := assocSet r.chans loc cc }

/-- RELEASE-ACQUIRE on the channel's next send/receive buffer slot
(gc's `racenotify` — see `ChanClocks`): the goroutine's clock joins the
slot's, the slot takes the joined clock, the goroutine's own epoch
bumps (the FastTrack release increment). -/
def RaceState.slotOp (r : RaceState) (t : Nat) (loc : Loc) (cap : Nat)
    (isSend : Bool) : RaceState :=
  let cc := r.chanOf loc cap
  let size := max 1 cc.slots.size
  let idx := (if isSend then cc.sendCount else cc.recvCount) % size
  let joined := (r.vcOf t).join ((cc.slots[idx]?).getD #[])
  let cc' := { cc with
    slots := cc.slots.setIfInBounds idx joined
    sendCount := if isSend then cc.sendCount + 1 else cc.sendCount
    recvCount := if isSend then cc.recvCount else cc.recvCount + 1 }
  (r.setVC t (joined.bump t)).setChan loc cc'

/-- Unbuffered rendezvous (gc's `racesync`): both goroutines join each
other's clocks — both go_mem directions of the unbuffered rules — then
each bumps its own epoch. -/
def RaceState.rendezvous (r : RaceState) (i j : Nat) : RaceState :=
  let joined := (r.vcOf i).join (r.vcOf j)
  (r.setVC i (joined.bump i)).setVC j (joined.bump j)

/-- `close(ch)` releases the closer's clock into `closeVC` (gc's
`racerelease(c.raceaddr())`). -/
def RaceState.closeOp (r : RaceState) (t : Nat) (loc : Loc) (cap : Nat) :
    RaceState :=
  let cc := r.chanOf loc cap
  let vt := r.vcOf t
  let cc' := { cc with closeVC := some (vt.join ((cc.closeVC).getD #[])) }
  (r.setVC t (vt.bump t)).setChan loc cc'

/-- A receive that returns the zero value because the channel is
closed acquires the closer's clock (gc's closed-and-empty
`raceacquire`). -/
def RaceState.closeAcquire (r : RaceState) (t : Nat) (loc : Loc) : RaceState :=
  match r.chans.find? (·.1 == loc) with
  | some (_, cc) =>
      match cc.closeVC with
      | some cv => r.setVC t ((r.vcOf t).join cv)
      | none => r
  | none => r

/-- The `go` statement's edge — go_mem: "The go statement that starts
a new goroutine is synchronized before the start of the goroutine's
execution." The child is born with the parent's clock (own epoch 1);
the parent's epoch bumps, so its post-spawn accesses are visibly
unordered with the child. The goroutine-EXIT direction gets NO edge —
go_mem: "The exit of a goroutine is not guaranteed to be synchronized
before any event in the program." -/
def RaceState.spawn (r : RaceState) (parent child : Nat) : RaceState :=
  let pv := r.vcOf parent
  let childVC := (pv.pad (child + 1)).setIfInBounds child 1
  (r.setVC parent (pv.bump parent)).setVC child childVC

/-- Check ONE access against the shadow, then record it. A conflict —
some overlapping path holds an access by another goroutine that is not
happens-before this goroutine's current point, of a kind that CONFLICTS
with this one (`AccessKind.conflicts`: at least one write, not both
atomic) — is the terminal `raceDetected` (fail closed per run; the
message is fixed so the refusal is choice-invariant per stream). -/
def RaceState.accessKey (r : RaceState) (t : Nat) (kind : AccessKind)
    (key : ShadowKey) : Except Stop RaceState :=
  let vt := r.vcOf t
  let conflict := r.shadow.any fun (k, cell) =>
    key.overlap k && cell.conflicts kind t vt
  if conflict then throw .raceDetected
  else
    let cell := ((r.shadow.find? (·.1 == key)).map (·.2)).getD {}
    return { r with shadow := shadowSet r.shadow key (cell.record kind t (vt.get t)) }

-- DELETED (C1 S2b-ii): `RaceState.access`/`RaceState.accesses` — the footprint table's `.data`
-- recorders. DELETED (C1 S2c): `RaceState.accessKeys` — the recorder of a plain access list; the
-- label is a list of memory-model EVENTS now, folded by `RaceState.events` (below, after the
-- clock operations it interprets).

/-- **The CHANNEL-OBJECT access pair (BUG-045 + BUG-046; U3 in the
module docstring)** — gc's `c.raceaddr()` instrumentation, modeled
exactly: a plain send is a chan-object READ (`chansend`'s entry
`racereadpc` — recorded at the apply position whether the send
commits, parks, or panics), a successful close is a chan-object WRITE
(`closechan`'s `racewritepc`; the closed/nil panics fire before it), a
receive records NOTHING (`chanrecv` is acquire-only), and a SELECT
records one READ per SEND clause at its poll — `selectgo` pass 1's
`racereadpc` per polled send case (select.go:288; recv clauses
acquire-only, nil channels excluded from pollorder; BUG-046 corrected
the first version's false "selectgo bypasses chansend/closechan"
premise — that is true of the commit path, not the poll).
Check-then-record under the `.chanObj` key and the goroutine's CURRENT
clock (before the op's own release/acquire, matching gc's instruction
order): an HB-unordered read↔write or write↔write on the same channel is
the terminal `raceDetected` — send↔send never conflicts. Exact keying
(channel identity — `ShadowKey.overlap`'s `chanObj` arm), unlike the data
keys' path overlap. -/
def RaceState.chanObjAccess (r : RaceState) (t : Nat) (loc : Loc)
    (isWrite : Bool) : Except Stop RaceState :=
  r.accessKey t (if isWrite then .write else .read) (.chanObj loc)

def RaceState.syncOf (r : RaceState) (loc : Loc) : SyncClocks :=
  match r.syncs.find? (·.1 == loc) with
  | some (_, sc) => sc
  | none => {}

def RaceState.setSync (r : RaceState) (loc : Loc) (sc : SyncClocks) : RaceState :=
  { r with syncs := assocSet r.syncs loc sc }

/-- RELEASE into one of a sync cell's clocks (merge-join; `toB` picks
`semB`, the read-release clock): the goroutine's clock joins the sem
clock, and the goroutine's own epoch bumps (FastTrack). -/
def RaceState.syncRelease (r : RaceState) (t : Nat) (loc : Loc)
    (toB : Bool := false) : RaceState :=
  let sc := r.syncOf loc
  let vt := r.vcOf t
  let sc' := if toB then { sc with semB := sc.semB.join vt }
             else { sc with semA := sc.semA.join vt }
  (r.setVC t (vt.bump t)).setSync loc sc'

/-- ACQUIRE from a sync cell's clocks: join `semA` (always) and `semB`
(when `alsoB` — the write-Lock's second acquire) into the goroutine's
clock. -/
def RaceState.syncAcquire (r : RaceState) (t : Nat) (loc : Loc)
    (alsoB : Bool := false) : RaceState :=
  let sc := r.syncOf loc
  let joined := (r.vcOf t).join sc.semA
  r.setVC t (if alsoB then joined.join sc.semB else joined)

/-! ## sync/atomic — the per-address clocks and access kinds (the atomics arc, wave 1)

Q-ATOMIC RULED [USER] 2026-09-02 option A′ (`docs/2026-08-31_qrow-rulings.md`
row 2; design note `docs/2026-09-03_atomics-w1-design.md`). The machine
op is `applyAtomicOp` (Machine.lean — SC by construction, the envelope
statement there); THIS section is the detector half: what `raceUpdate`'s
atomic arm records and which clocks it moves, derived from the two
registers the Q-U4RESIDUAL (A) ruling made the standard (TSan's realized
set ∪ go_mem's operation kind — for atomics the two COINCIDE, row by
row):

THE TEXT. mem#atomic: "If the effect of an atomic operation A is
observed by atomic operation B, then A is synchronized before B. All
the atomic operations executed in a program behave as though executed
in some sequentially consistent order." mem#model kinds them: "atomic
read" is read-like, "atomic write" write-like, "atomic
compare-and-swap is both read-like and write-like" — and every
`sync/atomic` op is a SYNCHRONIZING operation, so by mem#model's
data-race definitions ("at least one of which is non-synchronizing")
two atomics never race each other while an atomic beside a PLAIN
access races exactly when one of them is write-like: `AccessKind.
conflicts` verbatim, with the op recorded as `.atomicRead` (Load) or
`.atomicWrite` (Store, Add, Swap, CompareAndSwap — the CAS's read-like
half adds no conflict an atomic write lacks, so one kind carries it,
succeed or fail).

WHAT gc's `-race` BUILD REALIZES (go1.26.5). `sync/atomic` is a
`noRaceFuncPkgs` package; under `-race` its entry points are the
assembly stubs of `runtime/race_amd64.s` (the block "Atomic operations
for sync/atomic package": `sync∕atomic·LoadInt32/LoadInt64/StoreInt32/
StoreInt64/SwapInt32/SwapInt64/AddInt32/AddInt64/CompareAndSwapInt32/
CompareAndSwapInt64`, each `MOVQ $__tsan_go_atomic{32,64}_<op>(SB), AX;
CALL racecallatomic<>(SB)`; the `Uint32`/`Uint64`/`Uintptr` names of
every op `JMP` to their same-width `Int*` twin — so the FIVE integer
kinds of one width are ONE realized op — and of the pointer family only
`LoadPointer` is a `JMP` (to `LoadInt64`); `Store/Swap/CompareAndSwap-
Pointer` have no stub in that block and are outside this wave anyway).
`racecallatomic` first touches the address (`MOVBLZX (R12), R13` —
"Trigger SIGSEGV early": a nil address faults BEFORE any TSan call, so a
nil-address op records nothing and moves no clock — the machine's
`valueAsLoc` panic likewise precedes everything), then calls the TSan
hook with the goroutine's race context. The hooks' semantics below is
DERIVED from LLVM compiler-rt's TSan sources — NOT vendored in `deps/`
(the linked `race_linux_amd64.syso` is a binary): the Go entry points
`__tsan_go_atomic{32,64}_{load,store,exchange,fetch_add,
compare_exchange}` are the Go block at the end of
`compiler-rt/lib/tsan/rtl/tsan_interface_atomic.cpp` (guarded
`#if SANITIZER_GO`), which call the same `AtomicLoad`/`AtomicStore`/
`AtomicRMW`/`AtomicCAS` templates as the C++ interface with the orders
`mo_acquire` (load), `mo_release` (store), `mo_acq_rel` (exchange,
fetch_add), `(mo_acq_rel, mo_acquire)` (compare_exchange). The
realized behavior is what the probe family MEASURES
(`docs/evidence/2026-09-03_atomics-w1/probes`); the source citation is
the derivation, the measurement the check. In those templates:

* **Load** (acquire): `thr->clock.Acquire(s->clock)` for the address's
  sync object, THEN `MemoryAccess(… kAccessRead | kAccessAtomic)`.
  Machine: `atomicAcquire` then record `.atomicRead` — acquire FIRST, so
  a plain write the releasing store published is ordered before the
  read's record (`raceUpdate`'s atomic arm keeps this order).
* **Store** (release): `MemoryAccess(… kAccessWrite | kAccessAtomic)`,
  then `thr->clock.ReleaseStore(&s->clock)` — an OVERWRITE of the
  address's clock by the storer's (not a merge: a store observes
  nothing, so by mem#atomic's sentence only its OWN predecessors are
  synchronized before a later observer — C++'s "a store breaks the
  release sequence"), then the epoch increment. Machine: record
  `.atomicWrite`, then `atomicReleaseStore` (clock := vt; bump).
* **Add / Swap** (acq_rel RMW): `MemoryAccess(… kAccessWrite |
  kAccessAtomic)`, then `thr->clock.ReleaseAcquire(&s->clock)` — the
  address clock and the goroutine's clock both become their join (the
  RMW observes the previous value, so its writer is synchronized before
  it; and it publishes) — then the epoch increment. Machine: record
  `.atomicWrite`, then `atomicReleaseAcquire`.
* **CompareAndSwap**: `MemoryAccess(… kAccessWrite | kAccessAtomic)`
  regardless of outcome; on SUCCESS `ReleaseAcquire` + increment (an
  RMW); on FAILURE `Acquire` only (the failed CAS observed the current
  value — mem#atomic gives its writer's edge — and published nothing).
  Machine: record `.atomicWrite`; success → `atomicReleaseAcquire`,
  failure → `atomicAcquire` (the outcome re-derived from the pre-state
  by `atomicCompute`, the same function the apply ran).

The RECORD-then-ACQUIRE order of the RMW/CAS/store rows is TSan's, kept
deliberately (the union rule: nothing the oracle refuses is run here).
Its ONE consequence beyond literal go_mem, recorded and MEASURED for
EVERY write-recording head: goroutine A `x = 1` (plain) then
`atomic.StoreInt64(&x, 2)`; goroutine B ONE atomic op on `x` that lands
AFTER A's store (in the probes, after a real-time sleep — no HB) —
go_mem orders A's plain write before B's op (the store is synchronized
before the op that observes it), TSan records B's atomic WRITE before
acquiring and reports a race with A's plain write: probes
`plainThenStoreVsLate{Add,Swap,CasSuccess,CasFail}`, gc RACE 20/20 each
at GOMAXPROCS 1 and 8 (the failed CAS included — its write record
precedes its failure-acquire); the Load twin `plainThenStoreVsLateLoad`
(acquire THEN record) green 20/20. The machine refuses those schedules
too — an over-refusal against literal
go_mem in the fail-closed direction, aligned with the oracle
(`docs/evidence/2026-09-03_atomics-w1/`). (The spin-loop forms of the
same shape are go_mem-racy on their own — a spin RMW or LOAD landing
between the plain write and the store is an unordered atomic beside a
plain write — and do not isolate the order; their probe headers say
so.) Every other row is identical under both registers.

`racecallatomic`'s other branch — an address OUTSIDE the Go heap arena
and data segments (a non-escaping stack variable) runs the op under
`__tsan_go_ignore_sync_begin/end`: the MemoryAccess still records, the
sync effect is dropped. Unobservable here: a variable shared across
goroutines escapes to the heap in gc, and a single goroutine cannot
race with itself; the machine keys clocks by `Loc` uniformly.

WHERE the access lands: the addressed cell's own `Loc` — the integer
cell IS the word (no `syncWord` sub-path: a `sync/atomic` op on `&x`
touches exactly `x`; on a typed wrapper `atomic.Int64` it touches the
`v` field, `.field loc ⟨"sync/atomic.Int64"⟩ "v"`, which the shadow
model's method bodies address). The path-overlap relation does the
rest: a plain read/write of the same variable, or a whole-struct
copy/overwrite of a struct holding the atomic, overlaps it and
conflicts (`race/atomics-misuse/*`); a sibling field's plain access
does not; two atomics never conflict (`race/atomics-free/*`). -/

/-- The per-address atomic clock (absent = never released into: the
empty clock, so a load before any store acquires nothing). -/
def RaceState.atomicOf (r : RaceState) (loc : Loc) : VClock :=
  match r.atomics.find? (·.1 == loc) with
  | some (_, vc) => vc
  | none => #[]

def RaceState.setAtomic (r : RaceState) (loc : Loc) (vc : VClock) : RaceState :=
  { r with atomics := assocSet r.atomics loc vc }

/-- ACQUIRE from an address's atomic clock (TSan `Acquire`: the Load, and
the failed CAS): the goroutine's clock joins the address clock. -/
def RaceState.atomicAcquire (r : RaceState) (t : Nat) (loc : Loc) : RaceState :=
  r.setVC t ((r.vcOf t).join (r.atomicOf loc))

/-- RELEASE-STORE into an address's atomic clock (TSan `ReleaseStore`:
the Store): the address clock BECOMES the storer's clock — an
overwrite, not a merge (a store observes nothing: mem#atomic gives a
later observer only the storer's own predecessors) — then the storer's
own epoch bumps (FastTrack: accesses after the release are visibly
unordered with the ones it published). -/
def RaceState.atomicReleaseStore (r : RaceState) (t : Nat) (loc : Loc) : RaceState :=
  let vt := r.vcOf t
  (r.setVC t (vt.bump t)).setAtomic loc vt

/-- RELEASE-ACQUIRE on an address's atomic clock (TSan `ReleaseAcquire`:
Add, Swap, a SUCCESSFUL CompareAndSwap): the address clock and the
goroutine's clock both become their join — the RMW observed the
previous value (its writer is synchronized before it) and publishes —
then the goroutine's own epoch bumps. -/
def RaceState.atomicReleaseAcquire (r : RaceState) (t : Nat) (loc : Loc) : RaceState :=
  let joined := (r.vcOf t).join (r.atomicOf loc)
  (r.setVC t (joined.bump t)).setAtomic loc joined

/-- **The clock movement of one happens-before action** performed by goroutine `t`
(C1 S2c, charter §7 D9) — the ONE interpretation of `HbAction` (Ops.lean): go_mem's
channel rules as gc realizes them (`slotOp`/`rendezvous`/`closeOp`/`closeAcquire`,
quoted at `ChanClocks`), the sync primitives' acquire/release (`SyncClocks`), the
`sync/atomic` per-address clocks (the section above), and the `go` statement's edge
(`RaceState.spawn`). The registry apply that performs the synchronization EMITS the
action in its label; the fold performs the movement here; nothing else moves a
clock. -/
def RaceState.hbAction (r : RaceState) (t : Nat) : HbAction → RaceState
  | .slotOp loc cap isSend => r.slotOp t loc cap isSend
  | .closeOp loc cap => r.closeOp t loc cap
  | .closeAcquire loc => r.closeAcquire t loc
  | .syncAcquire loc alsoB => r.syncAcquire t loc (alsoB := alsoB)
  | .syncRelease loc toB => r.syncRelease t loc (toB := toB)
  | .atomicAcquire loc => r.atomicAcquire t loc
  | .atomicReleaseStore loc => r.atomicReleaseStore t loc
  | .atomicReleaseAcquire loc => r.atomicReleaseAcquire t loc
  | .spawn child => r.spawn t child
  | .rendezvous partner => r.rendezvous t partner

/-- Fold ONE memory-model event of goroutine `t`: an access is checked against the
shadow and recorded (`accessKey` — a conflict is the terminal `raceDetected`); a
happens-before action moves the clocks (`hbAction`); an attributed event is the
OTHER goroutine's (the spawned child's entry read, the pairing partner's slot
transit) and folds under its id. -/
def RaceState.event (r : RaceState) (t : Nat) : MemEvent → Except Stop RaceState
  | .access k key => r.accessKey t k key
  | .hb a => return r.hbAction t a
  | .attributed who e => r.event who e

/-- Fold a LABEL in order — the step's events exactly as the module's operations
emitted them (the order is gc's instrumentation order; `MemEvent`'s docstring says
where it is load-bearing). -/
def RaceState.events (r : RaceState) (t : Nat) : AccessTrace → Except Stop RaceState
  | [] => return r
  | e :: rest => do RaceState.events (← r.event t e) t rest

-- MOVED (C1 S2c, 2026-09-18): `atomicOpKind`, the sync primitives' OWN state words section
-- (`syncWord`, `syncEntryKinds`, `syncReleaseTailKinds` and the BUG-080 / Q-U4RESIDUAL (A)
-- derivation docstring) now live in Machine.lean beside the registry applies that EMIT them
-- (`applySyncOpCore`/`applyTryLock`, `applyAtomicOp` via `atomicEvents`); the fold reads the
-- emitted events (`RaceState.events`), it computes none of them.

-- DELETED (C1 S2b-ii): `storeTargetAccess`, `unseqRunAccesses` and **`stepAccesses`** — the
-- footprint of one PRIVATE machine step from its pre-configuration (the table's root). The
-- step's LABEL (`Step`'s fifth index, `stepFn`'s fourth component, `StepEvent.trace`) is the
-- account; `raceUpdate` (Multi.lean) folds it. Provenance: the module docstring above.

end GoLean.GoCore.Machine
