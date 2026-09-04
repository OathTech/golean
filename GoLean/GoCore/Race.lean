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
terminal `GoError.raceDetected` — races FAIL CLOSED per run,
deterministically given the stream (the detector is a pure function of
the observed steps; it consumes NO choices).

This file is the pool-independent half: vector clocks, the per-location
shadow (TSan/FastTrack's skeleton — per-loc last-access epochs, one per
goroutine, subsumption by program order), the `Loc`-path overlap
relation, and THE ACCESS FOOTPRINT `stepAccesses` — the read/write set
of one private machine step, computed from the pre-step configuration.
The pool half (channel-clock events, the `raceUpdate` dispatcher, the
detecting loop) lives in `Multi.lean`, which imports this.

## Why a curated per-shape footprint, NOT autologging at the
`loadLoc`/`storeLoc` chokepoint (recorded deviation from the design
note's phrasing "through the existing loadLoc/storeLoc chokepoint")

Every heap access does flow through `loadLoc`/`storeLoc` — the
chokepoint is what makes the footprint below AUDITABLE against the
call-site inventory recorded at the end of this docstring (S3 audit
response: the inventory is now enumerated exhaustively, not asserted).
But logging raw chokepoint calls would record accesses gc never
performs and misgrade granularity in BOTH directions:

* `indexTargetLoc`/`resolveChain` LOAD base cells to bounds-check —
  gc's address formation reads no user memory (bounds come from
  headers/types); logging those loads would flag races on address
  formation (false positives vs `-race`).
* channel-cell loads/stores are SYNCHRONIZATION, race-free by spec
  ("A single channel may be used … by any number of goroutines without
  further synchronization") — never data accesses.
* `loadLoc` is a pure reader (no state to carry a log), so chokepoint
  logging would mean re-plumbing the sequential machine — growth by
  REVISION, against the arc's deciding principle.

So the footprint is a per-shape table argued against Go's ACCESS
semantics (what memory does gc's compiled code read/write here), in
the plan-extraction mold (`stmtPlan`/`spawnPlan` precedent). Its
completeness over access-bearing shapes is a LOCKSTEP obligation like
the relation's: a new `stepFn` arm (or frame-entry helper) that
touches user memory must add its footprint arm AND its inventory row
below, and the racy-negative corpus lane is the executable check.

## Recorded approximations (each pinned)

OVER-approximations (fail-closed direction — may REFUSE a
`-race`-green program; every one bounded and pinned):

* **O1 — value-path composite reads are whole-cell, except through an
  immediate PROJECTION chain (`fieldGet` / CONSTANT-index `indexGet`).**
  `evalVar` on a composite local and `.deref` of a composite pointee
  read the WHOLE cell; when the value is delivered straight into
  single-operand `fieldGet` frames, or into `indexGet` frames whose
  index is a constant literal over an ARRAY cell, the read is NARROWED
  to the projected path (`projChainTarget` — covers `p.a` on struct
  locals AND on `*struct`, the dominant raft-like idiom; S3 audit
  widened the original evalVar-only record to the `.deref` arm;
  Q-RACEPATH (RULED [USER] 2026-08-31, implemented 2026-09-02) added
  the constant-index member: `a[1]`, `a[1].x`, `s.arr[1]`). What
  remains whole-cell — the RESIDUAL: value-path array-element reads
  with a DYNAMIC index (`a[i]` — go/types did not fold the index to a
  literal; the element path is not determined until the index
  evaluates, after the base read), and composite reads whose
  continuation is not a projection chain (a whole-struct copy, a
  boxing, a send operand — all of which gc also reads whole).
  RE-OPEN TRIGGER (memo §4 option (B), deferred-footprint recording,
  effort M): a real target exhibiting dynamic-index DISJOINTNESS on a
  value-path ARRAY — raft's hot indexing is on SLICES, whose element
  reads are address-based and already precise. BUG-041 (constant-index
  half FIXED; residual OPEN); residual red-pinned by
  `race/free/array-dyn-index-read-write`; green-guarded by
  `race/free/{field-read-write,ptr-field-read-write,array-read-write,
  array-const-index-field,field-array-const-index}`; the narrowing's
  must-stay-racy direction pinned by
  `race/negative/{array-const-index-same-elem,array-const-index-whole-write}`.
  The FRAME-ENTRY member of the same class (S3 convergence): a
  needsDeref dispatch to a synthesized PROMOTION WRAPPER is narrowed
  to the wrapper's hop path (`dispatchAccesses` — gc's autogenerated
  wrapper loads only the embedded field; green-guarded by
  `race/free/promoted-ptr-box`, red-guarded by
  `race/negative/{promoted-dispatch,iface-dispatch}`), with
  UNRECOGNIZED wrapper shapes (embedded-POINTER hops, whose mid-chain
  deref reads another cell; any body outside the synthesized
  two-level block) falling back to the whole-pointee read —
  over-refusal, this envelope.

UNDER-approximations (fail-OPEN vs the `-race` oracle — each recorded
loudly; the racy-negative lane's claim is scoped by these):

* **U1 — CLOSED (BUG-005 (L) surgery, 2026-08-19): map-range now
  performs a real per-iteration read.** The live-iteration pick loads
  the map cell at EVERY `mapIterNext` step including the final
  done-check (gc's exhausted `mapIterNext` still reads — probed:
  "Previous read ... runtime.mapIterNext()"), recorded by the
  `stepAccesses` mapIterK arm; `race/negative/map-range-iter` flipped
  green with the arm. The old snapshot model's blindness (a write
  landing mid-range ran to a silent value) is retired with the
  snapshot itself.
* **U2 — `len`/`cap` on CHANNELS record nothing** — correct per spec
  ("without further synchronization") and per probe p26 (gc does not
  instrument chanlen). `len` on MAPS IS recorded (S3 audit refuted the
  earlier claim that it is invisible to `-race` — probed red on
  go1.26.5); slices/strings/pointer-to-array read headers/types only.
* **U3 — CLOSED (BUG-045 + BUG-046): the channel OBJECT is now a
  shadow location**, modeling exactly gc's instrumentation (go1.26.5
  runtime/chan.go + select.go): `chansend` performs `racereadpc` on
  `c.raceaddr()` at ENTRY (before the closed check, before parking —
  so the read is recorded whether the send commits, parks, or
  panics), `closechan` performs `racewritepc` on success (it panics
  on closed/nil BEFORE instrumenting — no record on the panic path),
  `chanrecv` performs only `raceacquire` — NO read — and `selectgo`
  pass 1 performs the SAME `racereadpc` for every polled SEND case
  (select.go:288, above its closed check; recv cases acquire-only,
  nil-channel cases excluded from pollorder). CORRECTED at the
  convergence check (BUG-046): the first version of this entry
  claimed select clauses record nothing because "selectgo's clause
  commits bypass chansend/closechan" — true of the COMMIT path,
  false of the instrumentation point (the poll), and the two probes
  it cited never tested the claim (`selectSendClosedArrival`'s close
  is same-goroutine-sequenced before its select;
  `selectWakeClosed`'s select has only recv clauses — both remain
  TSan-green for THOSE reasons). Realized as
  `RaceState.chanObjAccess` (a `ShadowCell` under the channel's
  `ShadowKey.chanObj` key, EXACT match — channel identity, no path
  overlap), checked-and-recorded by `raceUpdate`'s chan-op arm
  (plain ops) and select-apply arm (the per-send-clause poll read).
  Consequence recorded honestly: `resumeThread`'s
  close-woke-parked-sender panic arm is reachable only through a
  chan-object-racy shape (no HB edge can order a close after a send
  entry that then parks), so under the DRF-SC discipline the detector
  refuses at the close before any such wake — the arm stays (racy
  members traverse it only when the refusal is later on their path;
  the refused programs' pre-refusal semantics still needs it).
  The old "refusal-set agreement holds anyway" summaries (here, the
  doctrine's racy caption, the design note ×2) were FALSE in the
  fail-open direction — three shipped confluent-green subjects were
  TSan-red — and are corrected in place (BUG-045).

## THE loadLoc/storeLoc CALL-SITE INVENTORY (the lockstep obligation's
evidence — S3 audit response; audit this table when touching either
side)

Semantic-core call sites of `loadLoc`/`storeLoc` (incl. via helpers),
each mapped to its footprint treatment:

FOOTPRINT ARMS (recorded accesses):
- StepFn `evalVar` load → `stepAccesses` evalVar arm (O1 narrowing).
- `applyStrictOp .deref` load → `stepAccesses` deref arm (O1).
- `.indexGet` slice-element load → `strictOpAccesses`.
- `.mapGet` via map base load → `strictOpAccesses` (`mapAccess`).
- `.lengthOf` MAP load → `strictOpAccesses` (U2's map half).
- `.stringFromByteSlice` via `sliceVisibleValues` → `strictOpAccesses`.
- `.stringFromRuneSlice` via `sliceVisibleValues` → `strictOpAccesses`
  (triage L1, same treatment; `.runesFromString`'s operand is a string
  VALUE in hand and its allocation is fresh — no footprint, like
  `.bytesFromString`).
- `applyStmtOpCore` newValue/makeSlice/makeMap/makeChan target stores,
  mapAssign/mapDelete/clearMap (via `mapEntries`/`mapAssignValue`),
  clearSlice/sortSlice/copySlice element loops, appendSlice (in-place
  writes, spill reads via `sliceVisibleValues`, header store) →
  `stmtOpAccesses`. (mapLookup/typeAssertStmt rows retired with the
  StmtOps themselves — spine migration, BUG-034: the comma-ok forms'
  map read is the `rhsK`-apply arm below, their stores are ordinary
  `storeK` steps.)
- `applyRhsOp .mapLookup` map read (the `rhsK` apply step; BUG-034
  spine migration — gc's mapaccess2 instrumentation point) →
  `stepAccesses` rhsK arm. `.vals`/`.typeAssert` sources touch no
  user memory. Single assigns (BUG-037) ride the same spine: their
  store is the `storeK` row below (`storeTargetAccess`); the retired
  `assignStoreK` row is gone with the frames.
- `storeTarget` (phase-2 stores; `mapAssignValue` map half) →
  `storeTargetAccess`.
- frame EXIT `loadMany` (result reads) → `stepAccesses` frame-[] arms;
  the caller-target WRITES are per-target `storeK` steps since the
  BUG-025 spine migration (`storeTargetAccess`, phase 2 — `storeMany`
  is retired from the frame exit).
- `mapRangeStartSets` range-start load (base + start entry ids) →
  `stepAccesses` mapRangeK arm.
- `mapIterLiveEntries` per-pick live load (BUG-005 (L): every pick
  incl. the done-check) → `stepAccesses` mapIterK arm (closed U1).
- `dynamicDispatch?` needsDeref load (frame ENTRY) →
  `dispatchAccesses`, at the call/defer/spawn entry arms — narrowed to
  the promotion hop path when the target is a synthesized wrapper
  (O1's frame-entry member; whole-pointee for non-wrapper targets and
  unrecognized wrapper shapes).

READ-BUT-UNINSTRUMENTED (real loads whose gc counterpart reads memory
`-race` does not instrument — recorded, deliberately not footprinted;
S3 convergence: these two rows were missing from the first
"exhaustive" table):
- `.lengthOf` CHANNEL load (Machine.lean's chan len arm) → U2: gc's
  chanlen reads `c.qcount` uninstrumented (probe p26 green).
- `.capacityOf` CHANNEL load → U2, same basis.

NO ACCESS AT ALL (neither `loadLoc` nor `storeLoc` — listed so the
absence is legible as a decision, not an omission):
- `applyStrictOp .addrOfDeref` (BUG-056, fix 2026-08-19): `&*p`'s nil
  check consumes the pointer VALUE already in hand and touches no
  cell. gc's counterpart is a 1-byte hardware `TESTB` nil-probe that
  `-race` does not instrument (memo §2: TSan-green beside a
  concurrent pointee write where a real `*p` read is TSan-red), and
  our model performs NO load at all — so this is deliberately not
  even a READ-BUT-UNINSTRUMENTED row.

MODEL-INTERNAL loads gc never performs (excluded on purpose):
- the `.opDone` completion marker's strip (stage C, generalizing
  BUG-040's `.spawned` strip): a pure control step — touches no
  memory (`stepAccesses` catch-all; the wrapped op's own accesses and
  HB edges were recorded at the APPLY step, and the spawn's edge plus
  the child's dispatch read at the FORK step, by `raceUpdate` —
  unchanged).
- `loadLoc`/`storeLoc` own path recursion (walking to the root cell).
- `indexTargetLoc`/`resolveChain` bounds-check loads (address
  formation; bounds come from headers/types in gc).
- `applySlice` array-size load; `lengthOf`/`capacityOf` on
  pointer-to-array (length is type-static in gc).

SYNCHRONIZATION (the registry's ops — HB updates, never data):
- `chanCell` loads and `chanData` stores in `applyChanOp`,
  `commitClause`, `resumeThread`, `applyPairing`, `wakeReady`,
  `clauseReady` (spec: channels race-free without synchronization;
  the CHANNEL-OBJECT access pair gc layers on top of this is modeled
  since BUG-045 — U3 above, `chanObjAccess`, dispatched by
  `raceUpdate`'s chan-op arm, not by the footprint table: it is
  keyed to the OP, not to a machine-step memory access).
- `syncCell` loads and `syncData` stores in `applySyncOp`,
  `wakeReady`, `resumeThread` (spec-parity slice 2): the machine's
  cell traffic is the primitive's STATE TRANSITION, never a
  footprint-table access; the HB edges are the sync-clock updates in
  `raceUpdate`'s sync arm. What gc's `-race` build DOES realize on the
  primitive's own words — the state CAS/Add atomics, RWMutex's
  `race.Read(&rw.w)` plain read, WaitGroup's `wg.sema` misuse pair —
  is recorded by that same arm from the per-op table
  `syncEntryKinds`/`syncReleaseTailKinds` (BUG-080, U4 CLOSED —
  the section "The sync primitives' OWN state words" below), keyed to
  the OP like the chan-object pair, at the primitive's gc words under
  the sync cell's path — together with the op's go_mem kind
  (Q-U4RESIDUAL (A), 2026-09-02).
- `loadLoc`/`storeLoc` in `applyAtomicOp` (the atomics arc, wave 1):
  the `sync/atomic` op's own read-modify-write of an ORDINARY integer
  cell — never a footprint-table access (the step is one indivisible
  registry op); `raceUpdate`'s atomic arm records it at the cell's own
  `Loc` with the op's ATOMIC kind (`atomicOpKind`: Load `.atomicRead`,
  the rest `.atomicWrite` — TSan's `kAccessAtomic` access AND
  mem#model's operation kind, which coincide here) and moves the
  per-address atomic clock (the section "sync/atomic — the per-address
  clocks" below). Because the cell is user memory, a plain access to
  the same variable anywhere else conflicts through path overlap —
  mem#restrictions' mixed atomic/plain rule, and exactly what `-race`
  reports.

* **U5 — cross-goroutine unlock without handoff HB: TSan-red /
  ours-green** (audit fix round 2026-08-10, F2). `syncRelease` is a
  merge-join; gc's TSan hook is overwrite `race.Release`
  (internal/sync/mutex.go:188-191, rwmutex.go:203-204). The two agree
  at a release exactly when semA ⊑ the unlocker's clock (entailed
  program-wide by strict lock-handoff discipline; delta-review round 2
  made this semantic — no per-unlock syntactic condition suffices); on
  a legal owner-free unlock (probe p09) whose unlocker has no HB from
  the prior critical section, TSan drops that section's clock and
  reports a race our merge keeps ordered. The merge is the
  memory-model text verbatim (the n<m Unlock/Lock sentence is
  unconditional), so the deviation is from the TSan-alignment oracle
  in the missed-race direction; scope-limited to programs doing
  cross-goroutine unlocks without a handoff edge. Eval-pinned (the
  cross-unlock publication pin); un-lane-able as a corpus row (the
  mixed oracle class: plain gc green, race-instrumented gc red — the
  three-way rule's investigation shape, resolved here by this record).
* **U4 — CLOSED (BUG-080, 2026-09-02): the sync primitives' OWN
  state-word accesses are modeled as `-race` realizes them.** Before:
  a sync op recorded NO access on its primitive's cell, so a plain
  copy/overwrite of a Mutex/WaitGroup/RWMutex/Once another goroutine
  was operating on — racy by mem#model, TSan-red 10/10 — ran to
  a value (the detector-soundness differential's third cell,
  `docs/2026-09-02_detector-soundness.md` §3.2; born-FAIL pins
  `race/negative-sync/{wg-overwrite,mutex-copy}`). The fix is NOT a
  footprint-table entry (recording sync ops as plain writes would make
  two legal contending Locks conflict) but a third-and-fourth access
  KIND: `RaceAccess := AccessKind × Loc` with `AccessKind ∈ {read,
  write, atomicRead, atomicWrite}` — atomic↔atomic never conflicts,
  atomic↔plain conflicts unless both are reads (`AccessKind.conflicts`
  is the memory-model sentence verbatim). `raceUpdate`'s sync arm
  records, at the sync cell's path, the per-op set TSan realizes
  (`syncEntryKinds`/`syncReleaseTailKinds`, derived primitive by
  primitive from go1.26.5's sources — the section docstring below has
  the table): Mutex Lock/Unlock atomic writes; RWMutex ops a PLAIN read
  (`race.Read(&rw.w)`; the counters run under `race.Disable`); the
  WaitGroup `wg.sema` misuse pair (formerly the `wgSemaAccess`
  carve-out in a private shadow, now in the data shadow at the
  primitive's path so a copy/overwrite overlaps it); Once's atomic
  read/writes. The ruling's two checks: (i) the single `syncData`
  cell vs `locPrefix` — the access sits at the primitive's own PATH,
  so sibling-field plain accesses are disjoint (green guards
  `race/free-sync/{mutex-siblings,disjoint-prims}` and the probe
  controls); (ii) the per-primitive instrumentation differences —
  measured both directions by `probes/u4kind` (28 subjects, evidence
  dir). The slice's residual (a) — shapes go_mem calls racy but TSan
  cannot see (`race.Disable`) — was posed as Q-U4RESIDUAL and RULED
  [USER] 2026-09-02, option (A): the detector records go_mem's
  operation kind BESIDE TSan's realized set, each at its gc word
  (`syncWord`), so those shapes REFUSE where the `-race` build runs —
  a designed divergence from the oracle, pinned born-FAIL at
  `race/gomem-only/*` on BUG-084's Cases line (never counted as a
  pass). The section docstring below carries the derivation.

FRESH ALLOCATION / DRIVER (excluded — the malloc convention):
- `ExecState.alloc`, `allocDecls`, `bindParams`, `bindIterVars`,
  `enterFrame`'s binding half, `seedGlobals`, driver result readouts
  (`loadMany` after termination), `$pkginit` (sequential phase).
-/

namespace GoLean.GoCore.Machine

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

/-! ## Loc-path overlap

Go's memory locations at our heap's granularity: a `Loc` PATH names a
memory region; two paths conflict iff one is a prefix of the other
(equal included) — a whole-struct write overlaps every field, distinct
fields / distinct indices are disjoint. -/

/-- Is `l` a prefix of `m` (equality included)? -/
def locPrefix (l : Loc) : Loc → Bool
  | m@(.base _) => l == m
  | m@(.field b _ _) => l == m || locPrefix l b
  | m@(.index b _) => l == m || locPrefix l b

/-- Path overlap: the conflict relation on recorded DATA accesses. -/
def locOverlap (a b : Loc) : Bool := locPrefix a b || locPrefix b a

/-! ## Shadow keys (design-hygiene A6, 2026-09-04)

The shadow is keyed by a `ShadowKey`, not a `Loc`: a `Loc` is a memory
PATH and means only that. The two non-path things the detector shadows —
a sync primitive's gc WORD (formerly a phantom `Loc.field` under a
made-up `TypeId`) and a channel OBJECT (formerly a second shadow with its
own exact-match cell logic) — are their own constructors, and the one
`overlap` table says how every pair of keys conflicts. -/

/-- The gc state words of the sync primitives (the field names of the
pinned struct definitions: `state`/`sema` for Mutex and WaitGroup,
`w`/`readerCount` for RWMutex, `done`/`m` for Once). -/
inductive SyncWordName where
  | state | sema | w | readerCount | done | m
  deriving Repr, BEq, DecidableEq, Ord

-- The shadow is kept in CANONICAL (sorted) key order, so the dedup
-- engine's structural state equality is insensitive to the interleaving in
-- which keys were first touched (`shadowSet`); the total order is the
-- derived one on the key's components.
deriving instance Ord for Addr
deriving instance Ord for TypeId
deriving instance Ord for Loc
deriving instance Ord for SyncKind

/-- What one shadow cell is keyed by. -/
inductive ShadowKey where
  /-- A memory path (the data footprint; overlap = path prefix). -/
  | data (l : Loc)
  /-- A sync primitive's gc word: the primitive's cell path, its kind, the
  word. Overlaps itself exactly, and any DATA path that is a prefix of
  the primitive's path (a whole-struct copy/overwrite covers the words); a
  sibling field's access overlaps none. -/
  | syncWord (l : Loc) (kind : SyncKind) (word : SyncWordName)
  /-- A channel object (gc's `c.raceaddr()` instrumentation point): channel
  identity — exact match only, never path overlap (BUG-045/BUG-046). -/
  | chanObj (l : Loc)
  deriving Repr, BEq, DecidableEq, Ord

/-- THE conflict-keying table: when do two shadow keys name overlapping
memory? Data/data by path overlap; word/word by identity; data/word iff
the data path is a prefix of the primitive's path (either direction of
the pair); channel objects only with themselves, exactly. Symmetric by
construction (each mixed arm is stated both ways). -/
def ShadowKey.overlap : ShadowKey → ShadowKey → Bool
  | .data a, .data b => locOverlap a b
  | .syncWord l k wd, .syncWord l' k' wd' => l == l' && k == k' && wd == wd'
  | .data d, .syncWord m _ _ => locPrefix d m
  | .syncWord m _ _, .data d => locPrefix d m
  | .chanObj a, .chanObj b => a == b
  | .data _, .chanObj _ | .chanObj _, .data _ => false
  | .syncWord .., .chanObj _ | .chanObj _, .syncWord .. => false

/-! ## Access kinds and the per-location shadow (TSan/FastTrack skeleton) -/

/-- The KIND of one recorded access — the two axes of mem#model's data-
race definitions, quoted verbatim: "A read-write data race on memory
location x consists of a read-like memory operation r on x and a
write-like memory operation w on x, at least one of which is
non-synchronizing, which are unordered by happens before"; "A
write-write data race on memory location x consists of two write-like
memory operations w and w' on x, at least one of which is
non-synchronizing, which are unordered by happens before". (The
informal one-liner — "a write to a memory location happening
concurrently with another read or write to that same location, unless
all the accesses involved are atomic data accesses" — is mem#overview,
the same relation in words.) It is also TSan's shadow rule (two
accesses race unless both are reads or both are atomic). The plain pair is the data footprint's (`stepAccesses`);
the atomic pair is the sync primitives' own state-word traffic — as
`-race` realizes it AND as mem#model kinds the op (BUG-080 +
Q-U4RESIDUAL (A) — `syncEntryKinds` below, recorded by `raceUpdate`'s
sync arm); and the `sync/atomic` ops' own accesses at the addressed
cell (the atomics arc wave 1 — `atomicOpKind`, recorded by
`raceUpdate`'s atomic arm; section "sync/atomic — the per-address
clocks" below). -/
inductive AccessKind where
  | read
  | write
  | atomicRead
  | atomicWrite
  deriving Repr, BEq, DecidableEq

def AccessKind.isWrite : AccessKind → Bool
  | .write | .atomicWrite => true
  | .read | .atomicRead => false

def AccessKind.isAtomic : AccessKind → Bool
  | .atomicRead | .atomicWrite => true
  | .read | .write => false

/-- Do two HB-unordered accesses of these kinds (different goroutines,
overlapping paths) constitute a data race? At least one write, and not
both atomic — the memory-model sentence verbatim, and TSan's
`both_read_or_atomic` exclusion. Symmetric. -/
def AccessKind.conflicts (a b : AccessKind) : Bool :=
  (a.isWrite || b.isWrite) && !(a.isAtomic && b.isAtomic)


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

/-- `(kind, loc)` — one recorded access. -/
abbrev RaceAccess := AccessKind × Loc

/-- The element paths a slice's visible range names. -/
def sliceElemLocs (slice : SliceValue) (count : Nat) : List Loc :=
  match slice.base with
  | none => []
  | some b =>
      (List.range count).map fun i => .index b (Int.ofNat (slice.offset + i))

/-- Read of a map's data cell (map objects are ONE location for race
purposes — gc/TSan's classification of "concurrent map read and map
write"). A nil map contributes nothing (the op returns zeros or
panics; no memory named). -/
def mapAccess (kind : AccessKind) : GoValue → List RaceAccess
  | .map m =>
      match m.base with
      | some l => [(kind, l)]
      | none => []
  | _ => []

/-- A write through an evaluated target-address value; nothing if the
address is malformed/nil (the step itself panics — no store happens). -/
def targetWrite (tv : GoValue) : List RaceAccess :=
  match valueAsLoc tv with
  | .ok l => [(.write, l)]
  | .error _ => []

/-- Footprint of a strict-operator application (the operands are
already values — their own reads were recorded at their own steps).
Arms argued against gc's compiled accesses; anything not listed
touches no user memory (bounds/type metadata, header math, values in
hand). `.deref` is handled at the `stepAccesses` level instead — its
read is narrowed by the CONTINUATION (`projChainTarget`). `len(m)` on
a MAP is a real instrumented read on the oracle toolchain (S3 audit:
probed `-race`-red beside a concurrent map write, refuting the earlier
"len is uninstrumented" claim for maps); `len`/`cap` on channels stay
exempt (spec: race-free without synchronization; ground-truth probe
p26: not flagged), and on slices/strings/pointer-to-array they read
headers/types only. -/
def strictOpAccesses (op : StrictOp) (vs : List GoValue) : List RaceAccess :=
  match op, vs with
  | .indexGet, [b, i] =>
      match b with
      | .slice slice =>
          match valueAsInt i with
          | .ok idx =>
              match sliceIndexLoc slice idx with
              | .ok l => [(.read, l)]
              | .error _ => []
          | .error _ => []
      -- Pointer-to-array read `p[i]` (triage L5): gc compiles a single
      -- ELEMENT load, so the footprint is the element loc — the same
      -- `.index base idx` shape element STORES use, keeping read/write
      -- pairs aligned and disjoint elements race-free. A nil base
      -- panics before any access.
      | .addr baseLoc =>
          match valueAsInt i with
          | .ok idx => [(.read, .index baseLoc idx)]
          | .error _ => []
      | _ => []  -- array/string VALUES are in hand (read recorded at their producer)
  | .mapGet _ _, [b, _] => mapAccess .read b
  | .lengthOf _, [v] => mapAccess .read v
  | .stringFromByteSlice, [v] =>
      match valueAsSlice v with
      | .ok slice => (sliceElemLocs slice slice.len).map ((.read, ·))
      | .error _ => []
  | .stringFromRuneSlice, [v] =>
      match valueAsSlice v with
      | .ok slice => (sliceElemLocs slice slice.len).map ((.read, ·))
      | .error _ => []
  | _, _ => []

/-- Narrow a whole-cell read through the chain of PROJECTIONS its
continuation will immediately apply: when the value a read produces is
delivered straight into single-operand `fieldGet` frames, only the
projected FIELD PATH is semantically read (Go compiles `p.a` to a
single field load; the rest of the struct is discarded unobserved).
This is what keeps disjoint-field READ/WRITE pairs race-free at the
detector (S3 audit: the free lane's read/write direction) for both the
local (`evalVar` under a `fieldGet` frame) and pointer (`deref` under a
`fieldGet` frame) forms.

**Q-RACEPATH — CONSTANT-index narrowing (RULED [USER] 2026-08-31,
`docs/2026-08-31_qrow-rulings.md` row 4; implemented 2026-09-02, the
Tier-4 detector-soundness lane).** The chain also passes through an
`indexGet` frame whose pending index operand is a CONSTANT literal
(`Expr.intLit` — go/types constant-folds every constant index
expression to one, and a constant index is compile-time bounds-checked,
so the element path is fully determined before the projection applies)
PROVIDED the cell the read produces is an ARRAY: element paths live
under the array's own `Loc`, exactly where element STORES land
(`storeTargetAccess` resolves `a[1] = v` to `.index base 1`), so a
constant-index read and a disjoint-element write are disjoint paths.
gc compiles `a[1]` to a single element load, and mem#restrictions
licenses the per-sub-value decomposition of composite reads verbatim
(quoted at inventory C10) — the narrowed footprint is the faithful
one. A SLICE or STRING variable's cell is a HEADER whose elements live
elsewhere: its read stays whole-cell (the element read is the
`strictOpAccesses` indexGet arm's job), which is why the narrowing is
gated on the loaded cell being `.array` — never on the frame shape
alone. The chain composes in either order (`a[1].x` and `s.arr[1]`).
DYNAMIC indices (any non-literal index expression — a variable, a call,
an arithmetic form go/types could not fold) are NOT narrowed and remain
the recorded whole-cell over-approximation: O1's RESIDUAL, red-pinned
by `race/free/array-dyn-index-read-write`, with its re-open trigger
recorded in O1 (a real target needing dynamic-index disjointness on a
value-path ARRAY — memo option (B), deferred-footprint recording). -/
def projChainTarget (s : ExecState) : Cont → Loc → Loc
  | .strictK (.fieldGet tid f) [] [] _ k', loc =>
      projChainTarget s k' (.field loc tid f)
  | .strictK .indexGet [] [.intLit i _] _ k', loc =>
      match loadLoc s loc with
      | .ok (.array _) => projChainTarget s k' (.index loc i)
      | _ => loc
  | _, loc => loc

/-- Peel a pure `fieldGet` chain over a synthesized wrapper's RECEIVER
parameter: `some hops`, outermost projection LAST. `none` on any other
shape (mid-chain derefs from embedded-pointer hops, address-formers,
non-receiver anchors) — the caller then falls back to the whole-pointee
read (over-refusal, the fail-closed direction; recorded in O1).

The receiver is identified by its PARAMETER NAME taken from the target
`Func`'s own first parameter (`recvId` — `dispatchAccesses` passes
`target.args[0]`), never by a frontend string literal (arc-final audit
F7, 2026-08-08: this arm previously matched the frontend-chosen name
`"$recv"` verbatim — GoCore's only raw frontend string outside its own
reserved ids, violating "semantic identity is TypeId/FuncId, never raw
frontend strings"; the verifier showed a semantics-preserving frontend
rename flipping race/free/promoted-ptr-box from ok to a spurious
raceDetected). RESIDUAL COUPLING, recorded honestly: the BODY-shape
half remains — `wrapperForwardArg` recognizes exactly the decoder's
synthesized two-level wrapper block, and any other emission shape
falls back to the whole-pointee read (fail-closed over-refusal, pinned
by the `race/free/promoted-ptr-box` strict row going red on drift,
per O1). -/
def recvFieldChain (recvId : String) : Expr → Option (List (TypeId × String))
  | .var v => if v == recvId then some [] else none
  | .fieldGet recv tid f => (recvFieldChain recvId recv).map (· ++ [(tid, f)])
  | _ => none

/-- The forwarding call's RECEIVER argument in a synthesized promotion
wrapper's body (`synthesizePromotionWrappers`: one block of
[forwarding call, return]). Deliberately shallow — one statement-list
level — so it recognizes EXACTLY the synthesized shape and fails
closed (whole-pointee fallback) on anything else. -/
def wrapperForwardArg (body : Stmt) : Option Expr :=
  -- Two flattening levels, deliberately bounded: the decoder emits the
  -- wrapper as `.block #[] #[.seqn [init, call], .seqn [assign, ret]]`.
  let flat : Stmt → List Stmt := fun s =>
    match s with
    | .seqn ss => ss.toList
    | .block _ ss => ss.toList
    | s => [s]
  ((flat body).flatMap flat).findSome? fun s =>
    match s with
    | .call _ _ args => args[0]?
    | .callValue _ _ args => args[0]?
    | _ => none

/-- The user-memory read a frame ENTRY performs: interface dynamic
dispatch of a *T box to a VALUE-receiver method copies the receiver
out of the pointee (`dynamicDispatch?`'s `needsDeref` read,
Ops.lean — found fail-OPEN by the S3 audit). The FOOTPRINT is argued
against gc's compiled access, which is NARROWER than the model's load
for one class (S3 convergence, major): when the dispatch target is a
SYNTHESIZED PROMOTION WRAPPER (`Func.wrapper`), gc's autogenerated
`(*T).M` loads only the promotion hop path (the embedded field), not
the whole outer struct — so the read is recorded at the hop path,
recovered from the wrapper's own synthesized body
(`wrapperForwardArg`/`recvFieldChain`; unrecognized wrapper shapes —
e.g. embedded-POINTER hops, whose mid-chain deref reads another cell —
fall back to the whole-pointee read, over-refusal per O1). Non-wrapper
value-receiver dispatch really does copy the whole pointee in gc
(probed `-race`-red on a disjoint-field write:
`race/negative/iface-dispatch`) and keeps the whole-cell read. Every
other part of frame entry allocates fresh cells only. -/
def dispatchAccesses (s : ExecState) (fid : FuncId) (args : List GoValue) :
    List RaceAccess :=
  match findFunctionIn? s.functions fid with
  | none => []
  | some func =>
      match methodInfoByFuncId? s func.id with
      | none => []
      | some method =>
          match methodRecvInterfaceName? s method with
          | none => []
          | some _ =>
              match args.head? with
              | some (.interface dynTy inner) =>
                  match concreteMethodForDynamic? s dynTy method.name with
                  | some (concrete, needsDeref) =>
                      if needsDeref then
                        match inner with
                        | .addr loc =>
                            (match findFunctionIn? s.functions concrete.funcId with
                            | some target =>
                                if target.wrapper then
                                  -- The receiver anchor is the target's OWN
                                  -- first parameter name (audit F7): the
                                  -- decoder builds a method's args as
                                  -- #[recv] ++ args, so args[0] is the
                                  -- receiver whatever the frontend calls it.
                                  match target.args[0]? with
                                  | some recvParam =>
                                      match wrapperForwardArg target.body
                                          >>= recvFieldChain recvParam.id with
                                      | some hops =>
                                          [(.read, hops.foldl
                                            (fun l (h : TypeId × String) =>
                                              Loc.field l h.1 h.2) loc)]
                                      | none => [(.read, loc)]
                                  | none => [(.read, loc)]
                                else [(.read, loc)]
                            | none => [(.read, loc)])
                        | _ => []  -- nil box: the entry panics, no read
                      else []
                  | none => []
              | _ => []

/-- The frame-entry footprint of a deferred call about to enter
(`(cv, args)` at the head of a frame's defer list). -/
def deferEntryAccesses (s : ExecState) : GoValue × List GoValue → List RaceAccess
  | (.funcVal fid captured, args) => dispatchAccesses s fid (captured ++ args)
  | _ => []

/-- Footprint of a wide-statement application. Fresh allocations are
never recorded (the malloc convention: a fresh location's creating
write precedes every path by which its address can race-freely
escape); target-cell writes, map-object accesses, and slice-element
reads/writes are. -/
def stmtOpAccesses (op : StmtOp) (vs : List GoValue) : List RaceAccess :=
  match op, vs with
  | .newValue _, [tv, _] => targetWrite tv
  | .makeSlice _ _, tv :: _ => targetWrite tv
  | .makeMap _, tv :: _ => targetWrite tv
  | .makeChan _ _, tv :: _ => targetWrite tv
  | .mapAssign _ _, [bv, _, _] => mapAccess .write bv
  | .appendSlice _, [tv, sliceV, elemsV] =>
      (match valueAsSlice sliceV, valueAsSlice elemsV with
       | .ok slice, .ok elems =>
           let newLen := slice.len + elems.len
           let srcReads := (sliceElemLocs elems elems.len).map ((.read, ·))
           if newLen ≤ slice.cap then
             -- in place: writes the cells [len, newLen) of the backing
             (match slice.base with
              | some b =>
                  srcReads ++ ((List.range elems.len).map fun i =>
                    (.write, Loc.index b (Int.ofNat (slice.offset + slice.len + i))))
              | none => srcReads)
           else
             -- spill: reads the old elements out; the new backing is fresh
             srcReads ++ (sliceElemLocs slice slice.len).map ((.read, ·))
       | _, _ => []) ++ targetWrite tv
  | .copySlice, [tv, dstV, srcV] =>
      (match valueAsSlice dstV, valueAsSlice srcV with
       | .ok dst, .ok src =>
           let count := Nat.min dst.len src.len
           (sliceElemLocs src count).map ((.read, ·))
             ++ (sliceElemLocs dst count).map ((.write, ·))
       | _, _ => []) ++ targetWrite tv
  | .mapDelete _, [bv, _] => mapAccess .write bv
  | .clearMap, [bv] => mapAccess .write bv
  | .clearSlice _, [bv] =>
      match valueAsSlice bv with
      | .ok slice => (sliceElemLocs slice slice.len).map ((.write, ·))
      | .error _ => []
  | .sortSlice _, [bv] =>
      match valueAsSlice bv with
      | .ok slice =>
          (sliceElemLocs slice slice.len).map ((.read, ·))
            ++ (sliceElemLocs slice slice.len).map ((.write, ·))
      | .error _ => []
  | _, _ => []

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

/-- Update-or-insert in a keyed association list (insertion order). -/
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
    (key : ShadowKey) : Except GoError RaceState :=
  let vt := r.vcOf t
  let conflict := r.shadow.any fun (k, cell) =>
    key.overlap k && cell.conflicts kind t vt
  if conflict then throw .raceDetected
  else
    let cell := ((r.shadow.find? (·.1 == key)).map (·.2)).getD {}
    return { r with shadow := shadowSet r.shadow key (cell.record kind t (vt.get t)) }

/-- A DATA access: the footprint's `(kind, path)` under the `.data` key. -/
def RaceState.access (r : RaceState) (t : Nat) (a : RaceAccess) :
    Except GoError RaceState :=
  r.accessKey t a.1 (.data a.2)

def RaceState.accesses (r : RaceState) (t : Nat) :
    List RaceAccess → Except GoError RaceState
  | [] => return r
  | a :: rest => do RaceState.accesses (← r.access t a) t rest

/-- Keyed accesses (the sync ops' word accesses). -/
def RaceState.accessKeys (r : RaceState) (t : Nat) :
    List (AccessKind × ShadowKey) → Except GoError RaceState
  | [] => return r
  | (kind, key) :: rest => do RaceState.accessKeys (← r.accessKey t kind key) t rest

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
    (isWrite : Bool) : Except GoError RaceState :=
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

/-- The access KIND a `sync/atomic` op records at the addressed cell —
both registers agree (section docstring): a Load is an atomic read;
Store, Add, Swap and CompareAndSwap (succeed or fail) atomic writes. -/
def atomicOpKind : AtomicStmtOp → AccessKind
  | .load => .atomicRead
  | .store | .add | .swap | .cas => .atomicWrite

/-! ## The sync primitives' OWN state words (BUG-080 — U4 CLOSED; Q-U4RESIDUAL RULED (A))

Two registers say what a sync op does to its primitive's own words,
and since the [USER] ruling of 2026-09-02 (Q-U4RESIDUAL, option (A) —
`docs/2026-08-31_qrow-rulings.md` row 9: "we want to follow go_mem
exactly") the detector records the UNION of both — the UNION itself
being an [AGENT] READING of the ruling (audit fix F3; the paragraph
"Why the union" below says where it departs from the literal words and
why) — both the union and the per-gc-word keying were COUNTERSIGNED
[USER] 2026-09-03 at the round-5 merge sign-off («sounds good merge
it», relayed to the recording worker by the [AGENT] coordinator, not
firsthand; record: `docs/2026-08-31_qrow-rulings.md`, row-9 appendix,
"Countersign of the two [AGENT] readings"):

1. **go_mem's operation kind** (mem#model, verbatim: "Some memory
   operations are read-like, including read, atomic read, mutex lock,
   and channel receive. Other memory operations are write-like,
   including write, atomic write, mutex unlock, channel send, and
   channel close. Some, such as atomic compare-and-swap, are both
   read-like and write-like."). Every sync op is a SYNCHRONIZING
   operation on its primitive, so its kind is recorded as an ATOMIC
   kind — `.atomicRead` for a read-like op, `.atomicWrite` for a
   write-like one: by mem#model's read-write/write-write definitions
   ("at least one of which is non-synchronizing") two sync ops never
   race each other, while a plain access beside a write-like op — or a
   plain write beside a read-like one — IS a data race, TSan or no
   TSan. mem#locks names the ops for BOTH `sync.Mutex` and
   `sync.RWMutex` ("The sync package implements two lock data types"):
   `RLock`/`Lock` are mutex lock = read-like, `RUnlock`/`Unlock` are
   mutex unlock = write-like. mem#more defers WaitGroup and Once to
   their package docs: `Done` "synchronizes before" the return of the
   `Wait` it unblocks (waitgroup.go), the release/acquire shape of
   unlock/lock and send/receive — so `Add`/`Done` (the counter RMW) are
   write-like and `Wait` read-like; `Once.Do`'s completion
   "synchronizes before" every return (mem#once), so the first `Do` is
   write-like and a `Do` observing completion read-like.
2. **What gc's `-race` build realizes** on the words, read PRIMITIVE BY
   PRIMITIVE from the pinned sources (go1.26.5) — the oracle's register
   (#13). `sync`, `internal/sync` and `sync/atomic` are
   `noRaceFuncPkgs` (cmd/internal/objabi/pkgspecial.go), and under
   `-race` the SSA builder skips memory instrumentation for every
   function of such a package (cmd/compile/internal/ssagen/
   ssa.go:340-342) — so their own plain loads/stores (e.g. `lockSlow`'s
   `old := m.state`) are invisible and the packages annotate by hand.
   Exactly three things reach TSan: `race.Read/Write` annotations,
   `race.Acquire/Release*` hooks, and `sync/atomic` calls — which the
   -race build routes to TSan's atomic hooks (runtime/race_amd64.s
   `racecallatomic`) UNLESS `race.Disable()` is active, in which case
   Go's TSan glue performs them un-instrumented (measured:
   `probes/u4kind/{wg-copy-vs-done,rw-copy-vs-rlock}` gc-green).

Why the union ([AGENT] reading), and why it is sound: mem#restrictions
licenses ANY implementation to "report the race and halt execution" on
detecting a data race, so a refusal the oracle would not issue costs
completeness (a go_mem-racy program the `-race` build happens to run)
never soundness; and every access TSan realizes is kept, so nothing
the oracle refuses is run here (no HOLE cell opens). WHERE THIS
DEPARTS FROM LITERAL go_mem: mem#model's operation-level list makes
EVERY mutex lock read-like, `sync.Mutex.Lock` included, so "follow
go_mem exactly" read literally would RUN a lone copy beside
`Mutex.Lock`. gc's `-race` build REFUSES it — the Lock is a CAS on
`m.state`, reported by TSan as a Write (measured: `probes/u4gomem/
mu-copy-vs-lock-only`, the copy unordered with the Lock op ALONE, gc
RACE 20/20 at GOMAXPROCS 1 and 8, machine RACE — agree-race; and the
BUG-080 pin `race/negative-sync/mutex-copy`). Dropping the realized
`.atomicWrite` would open a HOLE cell against the oracle, so the
[AGENT] kept it, grounded in mem#model's own sentence that a
compare-and-swap "is both read-like and write-like" (the read-like
half adds no conflict an atomic write lacks). THE CONSEQUENCE, plainly:
a lone copy beside `sync.Mutex.Lock` REFUSES, a lone copy beside
`sync.RWMutex.Lock`/`RLock` RUNS (`race/free-sync/rw-copy-beside-
{rlock,lock}`) — because TSan realizes Mutex's CAS but runs RWMutex's
counter RMW under `race.Disable`, leaving only go_mem's read-like lock
kind to apply. The asymmetry is the oracle's, inherited on purpose,
and [USER]-countersigned 2026-09-03 (above).
Where TSan realizes NOTHING (`race.Disable`) the go_mem kind alone is
recorded — the former residual (a), now closed BY DESIGN.

WHERE each access lands — the gc WORD, the `ShadowKey.syncWord` of the
sync cell's path, kind and word (`SyncWordName`: the field names of the
pinned struct definitions). A whole-struct copy/overwrite at the
primitive's or an enclosing path overlaps every word
(`ShadowKey.overlap`'s data/word arm is `locPrefix`); a SIBLING field's
plain access overlaps none (check
(i) of the BUG-080 ruling — `probes/u4kind/mu-siblings-under-lock`,
`mu-disjoint-prims`, `mu-sibling-beside-lock` and the corpus rows
`race/free-sync/{mutex-siblings,disjoint-prims}` are the green guards).
The words being DISTINCT is load-bearing: the `wg.sema` misuse pair
and RWMutex's `race.Read(&rw.w)` are PLAIN accesses in TSan's
realization, and had they shared one path with the go_mem atomic
kinds, a legal `Done` (atomic write) would conflict with a legal first
`Wait` (plain sema write), and a contending `RLock` (plain `rw.w`
read) with an `Unlock` (atomic write). On gc's own layout they are
different words and never meet — exactly as they never meet under
TSan.

THE TABLE (entry = before the op's acquire/release hook, under the
pre-op clock, commit or park alike — `syncEntryKinds`; tail = after a
committed op's release, at the bumped epoch — `syncReleaseTailKinds`):

* **Mutex** (`internal/sync/mutex.go`): `Lock` → `.atomicWrite @state`
  (the CAS, :63, whether it wins or falls into `lockSlow`'s CAS loop —
  TSan "Write … CompareAndSwapInt32"; go_mem's read-like lock is
  subsumed); `Unlock` → entry nothing, tail `.atomicWrite @state` (the
  Add at :194 follows `race.Release` :190). go_mem's write-like unlock
  is covered by the tail alone: an access unordered with the op is
  unordered with the tail (the release joins nothing INTO the
  unlocker's clock), and the tail additionally catches the acquirer's
  own later plain read — TSan's verdict. The `_ = m.state` at :189 is
  an uninstrumented load in a `noRaceFuncPkgs` package — nothing
  (`race/free-sync/mutex`, `probes/u4kind/mu-contend` stay green).
* **RWMutex** (`sync/rwmutex.go`): every op opens with
  `race.Read(unsafe.Pointer(&rw.w))` (:69/:116/:146/:203) → `.read @w`
  (realized, kept), then under `race.Disable()` performs its counter
  RMW → the go_mem kind `@readerCount`: `RLock`/`Lock` → `.atomicRead`
  (lock is read-like: a copy beside the LOCK OP ALONE is read-like
  beside read-like, NO race — the ruling's own statement of what is
  NOT in the class; isolated by `probes/u4gomem/rw-copy-vs-{rlock,
  lock}-only` and the corpus guards `race/free-sync/rw-copy-beside-
  {rlock,lock}`, agree-DRF/green), `RUnlock`/`Unlock` → `.atomicWrite`
  (unlock is write-like: a copy beside them REFUSES where TSan is
  green — by design; `probes/u4gomem/rw-copy-vs-{runlock,unlock}`).
  NOTE the BUG-080 probe shapes `probes/u4kind/rw-copy-vs-{rlock,lock}`
  pair the lock with its UNLOCK, both unordered with the copy, so under
  this table they refuse THROUGH the unlock — over-refusal by design,
  not a contradiction of the lock-is-read-like row.
* **WaitGroup** (`sync/waitgroup.go`): the state RMW runs under
  `race.Disable()` (:83, :162) → go_mem kind `@state`: `Add`/`Done` →
  `.atomicWrite` (a copy or overwrite beside them refuses — TSan sees
  neither), `Wait` → `.atomicRead` (an overwrite beside a `Wait` at
  counter 0 refuses; a copy beside any `Wait` that is not the first
  blocking waiter does not). Realized and kept, `@sema`: the misuse
  pair — a plain READ when an Add takes the counter off 0 upward
  (:111-115), a plain WRITE when the FIRST waiter registers before
  parking (:184-190); Add↔Wait misuse detection is unchanged (same
  pair, same check, at its own word), and the first waiter's plain
  write is why a copy beside a first blocking `Wait` stays red
  (`probes/u4kind/wg-copy-vs-first-wait`, TSan-red 10/10).
* **Once** (`sync/once.go`, no `race.Disable`): `Do` opens with the
  atomic LOAD of `o.done` (:67) — a Do observing completion is that
  `.atomicRead @done` alone (read-like: a copy beside it is green, an
  overwrite red); every other Do takes `doSlow`, whose `o.m.Lock()` CAS
  is `.atomicWrite @m` (the winner's and the parked contender's
  alike). The winner's completion (`onceComplete`) is the deferred
  `o.done.Store(true)` → `.atomicWrite @done` BEFORE the deferred
  `o.m.Unlock()` (LIFO) — then the Unlock's release and its trailing
  Add → tail `.atomicWrite @m`. go_mem and TSan agree on every Once
  row.

* **TryLock / TryRLock** (Q-TRYLOCK, RULED [USER] 2026-08-31 row 5;
  implemented 2026-09-03; probes in `docs/evidence/2026-09-03_q-trylock/`,
  20 runs each at GOMAXPROCS 1 and 8): `Mutex.TryLock`
  (`internal/sync/mutex.go:76-93`) on an UNLOCKED cell → `.atomicWrite
  @state` on BOTH envelope members — the CAS at :85 is realized by TSan
  whether it wins (the acquire, `race.Acquire` :90 follows) or loses
  (gc's realization of mem#locks' spurious false; a CAS records an
  atomic write regardless of outcome, as the atomics section's
  `cas`-failure row already relies on) — and on a HELD cell → NOTHING:
  the early return at :77-79 is a plain load in a noRaceFuncPkgs
  package (probes `muOverwriteLockedVsFailedTryLock`,
  `muCopyVsFailedTryLock`: gc green 20/20 against a plain overwrite /
  copy). go_mem adds nothing to a failed call ("An unsuccessful call has
  no synchronizing effect at all" — not a synchronizing operation, so no
  kind). `RWMutex.TryRLock`/`TryLock` (`sync/rwmutex.go:87-112,169-198`):
  the realized `race.Read(&rw.w)` (:89/:171) precedes `race.Disable` on
  EVERY outcome → `.read @w` always (probe `rwOverwriteVsFailedTryRLock`:
  gc RACE 20/20 on an overwrite beside a FAILED TryRLock); the counter
  CAS runs under `race.Disable`, so only go_mem's kind applies and only
  to a SUCCESSFUL call ("equivalent to a call to l.RLock/l.Lock" — lock
  is read-like) → `.atomicRead @readerCount` when acquired, the
  `rlock`/`wlock` row exactly. HB: the acquire edge on success only
  (`raceUpdate`; probe `muFailedTryLockNoEdge`: gc RACE 20/20 on a plain
  read after a failed TryLock — agree-race). One gc shape is
  schedule-dependent and pinnable in NO lane: an overwrite that RESETS a
  held Mutex to unlocked beside a TryLock (RACE 10/20 — when the reset
  lands first the TryLock succeeds and its CAS races; probe
  `muOverwriteVsFailedTryLock`, probe only).

Atomic↔atomic never conflicts, so contending ops on one primitive stay
green (`race/free-sync/{mutex,rw-writers,wg-edge,once-edge}`,
`probes/u4kind/{mu,rw,once}-contend`).

Wakes record nothing: a parked goroutine released nothing after its
entry, so no other goroutine can be HB-after the entry without being
HB-after the wake — every conflict a wake-time access would find, the
entry access already found (gc's woken `lockSlow` CAS is thus
detection-redundant here).

THE DESIGNED DIVERGENCE FROM THE `-race` ORACLE (was residual (a);
[USER]-ruled 2026-09-02 — recorded at BUGS.md BUG-084 and the ruling
sheet's row 9, provenance chain there): a plain access beside a
write-like op gc runs under `race.Disable` — `RUnlock`, RWMutex
`Unlock`, WaitGroup `Add`/`Done` — or a plain OVERWRITE beside `Wait`
at counter 0, is REFUSED here and RUN by gc's `-race` build. The racy
lane's three-way rule (our refusal + `-race` green on every sample)
files such a row as an investigation, never a pass; these rows are
classified BY DESIGN as go_mem-racy (one write-like operand, one
non-synchronizing — mem#model). The corpus pins them as born-FAIL rows
against gc's `ok` observation (`race/gomem-only/*`, BUG-084's Cases
line) so the divergence stays visible and never counts as a pass; the
probe family `probes/u4kind` re-run under this table
(`docs/evidence/2026-09-02_q-u4-gomem/`) shows them as `over-refusal`
cells, and the formerly UNPROBED copy-beside-`RUnlock`/`Unlock` shapes
are probed there (family `u4gomem`). NOT in the class, and unchanged:
a copy beside `RLock`/`Lock` ALONE (two read-likes — the isolated
shapes `probes/u4gomem/rw-copy-vs-{rlock,lock}-only` and the corpus
guards `race/free-sync/rw-copy-beside-{rlock,lock}` stay green), and
every race-free program (vet's `copylocks` flags every shape in the
class).

RESIDUAL (b), an outcome-CLASS deviation — both sides ABORT, but the
machine's abort is an asserted program outcome (`GoError.fatal`,
Value.lean:207-217) where gc's is the race report then the same abort:
the
detector folds SUCCESSFUL pool steps only (`execProgLoop` runs
`raceUpdate` after `stepMulti` returns), so a sync op whose apply is
FATAL — an `Unlock`/`RUnlock` after a concurrent plain overwrite reset
the primitive to unlocked — ends the run `fatal` before its entry
access is ever checked, where gc's `race.Read`/state Add precede the
misuse check and TSan reports the race first, then the fatal fires.
Reachable only by an overwrite-then-cross-goroutine-unlock shape
(`probes/u4kind/rw-overwrite-vs-{runlock,unlock}`, possible-HOLE by the
runner's definition, diagnosed at BUG-080). The owed fix's scope and
its call-site list are AUTHORITATIVE at TODO.md's BUG-080 follow-up
item (S–M, trust-surface) — cited, not restated here. -/

/-- The gc WORD of a sync primitive an access lands on: the
`ShadowKey.syncWord` of the primitive's own cell path, its kind and the
word (`state`/`sema` for Mutex and WaitGroup, `w`/`readerCount` for
RWMutex, `done`/`m` for Once — the section docstring's table). A shadow
KEY (A6; formerly a phantom `Loc.field` path under a made-up `TypeId`):
`ShadowKey.overlap` is what makes a copy/overwrite of the primitive (or
its enclosing struct) overlap the word while sibling fields and sibling
words stay disjoint. -/
def syncWord (loc : Loc) (kind : SyncKind) (word : SyncWordName) : ShadowKey :=
  .syncWord loc kind word

/-- The accesses recorded on the primitive's own words at a sync op's
ENTRY — before the op's release/acquire hook — from the op and the
PRE-step cell (`delta` is `wgAdd`'s operand, 0 for every other op):
TSan's realized set ∪ go_mem's operation kind, each at its gc word
(the section docstring's table is the derivation; Q-U4RESIDUAL (A)).
Recorded under the goroutine's current clock by `raceUpdate`'s sync
arm, commit or park alike. `acquired` is the TRY heads' outcome
(`tryLockAcquired`, re-derived by `raceUpdate` from the pre/post cells)
— it selects the success-only go_mem lock kind of RWMutex `TryLock`/
`TryRLock`; every other head's row ignores it (their kinds are
outcome-independent — commit or park alike). -/
def syncEntryKinds (op : SyncOp) (pre : SyncPrim) (delta : Int) (acquired : Bool)
    (loc : Loc) : List (AccessKind × ShadowKey) :=
  let at_ := syncWord loc pre.kind
  match op, pre with
  -- Mutex: the state CAS (TSan: atomic write; go_mem's read-like lock
  -- is subsumed by it).
  | .lock, _ => [(.atomicWrite, at_ .state)]
  -- Mutex Unlock: the state Add FOLLOWS the release (`syncReleaseTailKinds`).
  | .unlock, _ => []
  -- RWMutex: the realized `race.Read(&rw.w)` + the counter RMW's go_mem
  -- kind (lock read-like, unlock write-like).
  | .rlock, _ | .wlock, _ => [(.read, at_ .w), (.atomicRead, at_ .readerCount)]
  | .runlock, _ | .wunlock, _ => [(.read, at_ .w), (.atomicWrite, at_ .readerCount)]
  -- WaitGroup Add/Done: the state RMW is write-like (go_mem); the
  -- realized sema READ when the counter leaves 0 upward.
  | .wgAdd, .waitGroup counter _ =>
      (if delta > 0 && counter == 0 then [(.read, at_ .sema)] else [])
        ++ [(.atomicWrite, at_ .state)]
  | .wgAdd, _ => [(.atomicWrite, at_ .state)]
  -- WaitGroup Wait: the counter read is read-like (go_mem); the
  -- realized sema WRITE for the FIRST blocking waiter.
  | .wgWait, .waitGroup counter waiters =>
      (if counter != 0 && waiters == 0 then [(.write, at_ .sema)] else [])
        ++ [(.atomicRead, at_ .state)]
  | .wgWait, _ => [(.atomicRead, at_ .state)]
  -- Once: a Do observing completion is the atomic load of `o.done`;
  -- every other Do is `doSlow`'s `o.m.Lock()` CAS; completion is the
  -- `o.done.Store(true)` (its Unlock's Add is the tail).
  | .onceBegin _, .once true true => [(.atomicRead, at_ .done)]
  | .onceBegin _, _ => [(.atomicWrite, at_ .m)]
  | .onceComplete, _ => [(.atomicWrite, at_ .done)]
  -- Q-TRYLOCK (the section docstring's TryLock rows). Mutex TryLock on
  -- an UNLOCKED cell: the state CAS (:85), realized by TSan whether it
  -- wins (the acquire) or loses (gc's realization of the spurious
  -- member) — `.atomicWrite @state` on BOTH members; on a HELD cell:
  -- the plain early return (:77-79) in a noRaceFuncPkgs package —
  -- nothing realized, and go_mem gives an unsuccessful call no kind
  -- ("no synchronizing effect at all").
  | .tryLock _, .mutex locked => if locked then [] else [(.atomicWrite, at_ .state)]
  -- RWMutex TryRLock/TryLock: the realized `race.Read(&rw.w)` opens
  -- every outcome (:89/:171, BEFORE `race.Disable`); the counter CAS is
  -- under `race.Disable` (nothing realized), so only go_mem's kind
  -- applies, and only to a SUCCESSFUL call ("equivalent to a call to
  -- l.RLock/l.Lock" — lock is read-like → `.atomicRead @readerCount`,
  -- the `rlock`/`wlock` row); a failed call has no go_mem kind.
  | .tryRLock _, .rwmutex .. | .tryWLock _, .rwmutex .. =>
      (.read, at_ .w) :: (if acquired then [(.atomicRead, at_ .readerCount)] else [])
  -- KIND MISMATCH — UNREACHABLE BY NAME (audit fix round F4; the
  -- `wakeReady` discipline): `tryAcquire` is `stuck` on a TRY head over
  -- the wrong primitive before any state change, and `raceUpdate` folds
  -- SUCCESSFUL pool steps only, so no such (op, cell) pair reaches this
  -- table. Enumerated per kind, never `_`-absorbed, so a new primitive or
  -- a new head is a compile error here; the empty list is the honest
  -- value for a step that cannot have happened (an access on a
  -- fabricated word would be the fail-OPEN mistake — `at_` keys words by
  -- `pre.kind`, so a Mutex-word access under a TryRLock would be a
  -- fiction).
  | .tryLock _, .rwmutex .. | .tryLock _, .waitGroup .. | .tryLock _, .once .. => []
  | .tryRLock _, .mutex .. | .tryRLock _, .waitGroup .. | .tryRLock _, .once .. => []
  | .tryWLock _, .mutex .. | .tryWLock _, .waitGroup .. | .tryWLock _, .once .. => []

/-- The accesses `-race` realizes AFTER a sync op's release hook:
`Mutex.Unlock`'s state Add follows `race.Release` (mutex.go:188-194),
and so does the Add inside Once's deferred `o.m.Unlock()`. Recorded
after `syncRelease` (at the bumped epoch), so a goroutine that ACQUIRES
this very release and then plainly reads the primitive still conflicts
— TSan's verdict exactly; it also covers go_mem's write-like unlock
(section docstring, Mutex row). -/
def syncReleaseTailKinds (op : SyncOp) (pre : SyncPrim) (loc : Loc) :
    List (AccessKind × ShadowKey) :=
  let at_ := syncWord loc pre.kind
  match op with
  | .unlock => [(.atomicWrite, at_ .state)]
  | .onceComplete => [(.atomicWrite, at_ .m)]
  -- Every other head's recorded set lies entirely at ENTRY
  -- (`syncEntryKinds`). Enumerated, never `_`-absorbed, so a new
  -- constructor is a compile error here as in every other sync arm.
  | .lock => []
  | .rlock => []
  | .runlock => []
  | .wlock => []
  | .wunlock => []
  | .wgAdd => []
  | .wgWait => []
  | .onceBegin _ => []
  | .tryLock _ => []
  | .tryRLock _ => []
  | .tryWLock _ => []

/-- The write of one phase-2 store step (`storeK`): the resolved
target path. Chain resolution itself reads no user memory (address
formation — see the module docstring); a resolution/bounds/nil failure
means the step panics and no store happens. -/
def storeTargetAccess (s : ExecState) (r : TargetRef) : List RaceAccess :=
  match r with
  | .chain anchor idxs steps =>
      match resolveChain s anchor steps idxs with
      | .ok v => targetWrite v
      | .error _ => []
  | .mapElem b _ _ _ => mapAccess .write b

/-- **The footprint of one PRIVATE machine step**, from its pre-step
configuration: which user-memory paths the step reads/writes. Every
configuration shape not listed performs no user-memory access (control
gluing, operand accumulation, address formation, fresh allocation,
channel/select operations — the latter are the registry's
synchronization ops, handled by the HB updater in `Multi.lean`, and
race-free by spec). Completeness over access-bearing shapes is a
lockstep obligation (module docstring). -/
def stepAccesses (s : ExecState) (c : Config) : List RaceAccess :=
  match c with
  | .evalE (.var id) env k =>
      match LocalEnv.lookup env id with
      | some loc => [(.read, projChainTarget s k loc)]
      | none => []
  | .retV v (.strictK (.deref _) [] [] _ k') =>
      -- Handled here (not in strictOpAccesses) so the continuation can
      -- narrow the pointee read through an immediate projection chain
      -- (fieldGet / constant-index indexGet).
      (match valueAsLoc v with
       | .ok l => [(.read, projChainTarget s k' l)]
       | .error _ => [])
  | .retV v (.strictK op done [] _ _) =>
      strictOpAccesses op ((v :: done).reverse)
  | .retV v (.stmtOpK op _ done [] _ _) =>
      stmtOpAccesses op ((v :: done).reverse)
  -- The rhsK APPLY step (spine migration, BUG-034/BUG-037): the value
  -- source applies to the completed RHS operands. `.mapLookup` READS
  -- the map object (gc's mapaccess2 instrumentation point);
  -- `.vals`/`.typeAssert` touch no user memory. The subsequent stores
  -- are per-target `storeK` steps (`storeTargetAccess` below), exactly
  -- like every other spine-riding assignment.
  | .retV v (.rhsK rop _ done [] _ _ _) =>
      (match rop, (v :: done).reverse with
       | .mapLookup _ _, [bv, _] => mapAccess .read bv
       | _, _ => [])
  | .retV v (.mapRangeK _ _ _ _ _ _ _) => mapAccess .read v
  -- BUG-005 (L) surgery: EVERY mapIterK pick step — including the
  -- final done-check — loads the live map cell (gc's exhausted
  -- mapIterNext still reads; this is the arm that closed U1). Nil-map
  -- ranges (base none) read nothing. SOUNDNESS OF THIS FOOTPRINT under
  -- the B1 entry-identity stamps (2026-09-03): the pick's only inputs
  -- besides the frame are the cell's live entries (ids, keys, values),
  -- read here; the frame's `produced`/`start` ID sets are thread-private
  -- data written only by this goroutine's own picks and range start,
  -- and every id in them was read off THIS cell by such a load. A
  -- foreign `mapDelete`/`clearMap`/`mapAssign` changes what the pick
  -- computes only by writing this cell — an access `stmtOpAccesses`
  -- records — so a pick whose candidate set another goroutine could
  -- have changed conflicts with that write at this location (HB-ordered
  -- or refused). No goroutine step rewrites another's frame (the
  -- pool-level prune is gone), so nothing the pick depends on lies
  -- outside this one read.
  | .next (.mapIterK _ _ _ _ _ base _ _ _ _) =>
      (match base with
       | some l => [(.read, l)]
       | none => [])
  -- Frame ENTRIES with a possible interface-dispatch receiver deref
  -- (S3 audit major: dynamicDispatch?'s needsDeref read): the ordinary
  -- call shapes with their last operand arriving, and the deferred-call
  -- drains (normal, return, and panic paths). Zero-argument entries
  -- (bare `.call`, callTargetsK with no args) cannot dispatch — no
  -- receiver — and stay footprint-free.
  | .retV v (.callArgsK fid _ vals [] _ _) =>
      dispatchAccesses s fid (vals ++ [v])
  | .retV (.funcVal fid captured) (.callValCalleeK _ [] _ _) =>
      dispatchAccesses s fid captured
  | .retV v (.callValArgsK cv _ vals [] _ _) =>
      (match cv with
       | .funcVal fid captured => dispatchAccesses s fid (captured ++ vals ++ [v])
       | _ => [])
  | .next (.frame _ _ _ (d :: _) _ _) => deferEntryAccesses s d
  | .returning (.frame _ _ _ (d :: _) _ _) => deferEntryAccesses s d
  | .panicking _ (.frame _ _ _ (d :: _) _ _) => deferEntryAccesses s d
  | .next (.storeK (r :: _) (_ :: _) _ _ _) => storeTargetAccess s r
  -- Frame EXIT (BUG-025 spine migration): the exit step only READS the
  -- pinned result cells; the caller-target WRITES are the subsequent
  -- per-target `storeK` steps (the `storeTargetAccess` arm above),
  -- exactly like every other phase-2 store.
  | .next (.frame _ _ results [] _ _) =>
      results.map ((.read, ·))
  | .returning (.frame _ _ results [] _ _) =>
      results.map ((.read, ·))
  | _ => []

end GoLean.GoCore.Machine
