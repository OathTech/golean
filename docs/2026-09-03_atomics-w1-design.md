# The atomics arc, wave 1 — `sync/atomic` integer core (design note, 2026-09-03)

[AGENT] design note of the `atomics-w1` lane, written under the
[USER] ruling of 2026-09-02 (Q-ATOMIC, option A′, owner = this repo —
`docs/2026-08-31_qrow-rulings.md` row 2; charter
`docs/2026-09-01_qatomic-owner-proposal.md` §4 wave 1 + the design
argument of record `docs/2026-08-21_w32-qrow-memos.md` §2). It records
what wave 1 built, what it refused, the SC argument, the detector
derivation, and the questions it did NOT decide. Evidence:
`docs/evidence/2026-09-03_atomics-w1/`.

## 1. Scope (what landed)

**Modeled — the integer core.** `sync/atomic`'s `Load*`, `Store*`,
`Add*`, `Swap*`, `CompareAndSwap*` over `Int32`, `Int64`, `Uint32`,
`Uint64`, `Uintptr` (25 functions; `uintptr` is realized as `uint64`
throughout the frontend — inventory R1's pin), as ONE machine op
family, plus the five typed integer wrappers `atomic.Int32/Int64/
Uint32/Uint64/Uintptr` with their `Load/Store/Swap/CompareAndSwap/Add`
methods.

**Refused, by name and wave, at the frontend** (every refusal reaches
the differential as a `frontend-export` red naming its cause):

| member | refusal | why |
|---|---|---|
| `And*`, `Or*` (Go 1.23 bitwise RMWs; the wrappers' `And`/`Or`) | "atomics WAVE 2" | not in wave 1's op family; the wrappers' `And`/`Or` land as declaration-only stubs whose calls refuse |
| `*Pointer`, `atomic.Pointer[T]` | "unsafe.Pointer family — outside the unsafe policy" | the proposal's exclusion (§4) |
| `atomic.Value` | "atomics WAVE 2" | interface-valued slot, gc's nil / inconsistent-type panics — the proposal's wave 2; the frontier row `sync/atomic-frontier/value` stays FAIL, its stage moving `lean-observation → frontend-export` (a named refusal, not a dangling stub) |
| `atomic.Bool` | "atomics WAVE 2" | uint32-backed with a bool surface — trivially wave 2 with `Value` |
| the function VALUE shape (`f := atomic.LoadInt64`), `go`/`defer` of an atomic function | the standing stdlib-selector-in-value-position refusal | the direct-call shape is the whole surface, as for every stdlib member |

**Not in this wave, and why (§6):** Q-TRYLOCK's rider.

## 2. The wire and the lowering (frontend → decoder)

`tools/nativefrontend/atomics.go`. A direct call of a `sync/atomic`
package-level function — resolved through the `*types.Func` (package
path `sync/atomic`, no receiver), so the qualified spelling
`atomic.AddInt64(&n, 1)` and the bare-ident spelling inside the shadow
model meet at ONE site — emits

```
{"expr":"atomic-op","op":"load|store|add|swap|cas",
 "kind":<the integer's wire type>,"args":[addr, operands...],
 "resultTypes":[...]}
```

an EFFECTFUL node the ANF hoist statement-anchors exactly like a call
(`x := atomic.AddInt64(&n, 1) * 2` becomes `$c0 := atomic-op…; x := $c0
* 2`). The decoder (`GoLean/NativeToIR.lean`, `asAtomicOp?`) admits it
ONLY where it admits `call` — an expression statement (result
discarded: no target) and the single RHS of an assignment (exactly one
target, blank → a typed discard temp) — with strict keys, the op name
from the closed set, the kind from `{int32, int64, uint32, uint64}`,
and the arity checked here AND again by `atomicPlan` (fail closed
twice, the sync-op discipline). Every other position refuses by name.

**Typed wrappers — the E5-T shadow model** (`importedmodel.go`'s
vehicle, the `strings.Builder` precedent): a pinned `package atomic`
(import path `sync/atomic`) whose struct types and method bodies are
TRANSCRIBED from go1.26.5 `sync/atomic/type.go` — `func (x *Int64)
Add(delta int64) (new int64) { return AddInt64(&x.v, delta) }` — so a
method call on a typed atomic lowers through the very same `atomic-op`
node as the direct call (the ledger's recorded judgment "typed
variants ride the same lowering", now by construction). The model's
package-level functions are BODYLESS declarations (gc's own `doc.go`
shape — intrinsics), dropped by `lowerShadowModel` before emission;
the bodyless shape is admitted ONLY for the atomics table
(`atomicIntrinsicDecl`), any other refuses the model. Upstream's blank
`_ noCopy` / `_ align64` fields are omitted: blank fields carry no
value, take no part in `==` (spec#Comparison_operators — "corresponding
non-blank field values"), and `unsafe.Sizeof` is refused; the empty
composite literal `atomic.Int64{}` — the only legal cross-package
literal (spec#Composite_literals, non-exported fields) — lowers to the
type's default like the sync primitives' (`emitStructLit`).

**Not shim injection under D-002 — stated as the proposal owes.** No
stdlib BODY is hand-modeled: the calls plumb to a machine op family
whose semantics is argued from mem#atomic (§3), identical in shape to
the `sync` ops (`emitSyncOpStmt` → `sync-op` → `applySyncOp`). The
shadow model's method bodies are gc's own one-line definitions calling
the intrinsics, not a re-implementation of library behavior; the
identity principle (Q-SYNCVAL's contract) holds by construction since
every lowering spelling reaches the one node. **[USER] confirmation of
this D-002 reading is owed at dispatch per proposal §4 and was NOT in
the dispatching brief — it is posed in the lane report, not
self-adjudicated.**

## 3. The machine op (GoCore) and the SC argument

`GoLean/GoCore/Syntax.lean`: `AtomicStmtOp ∈ {load, store, add, swap,
cas}`; `Stmt.atomicStmt (op) (kind : IntKind) (args) (targets)`.
`Machine.lean`: `AtomicOp := ⟨head, kind, targets⟩`; `atomicPlan`
(arity, kind ∈ the four, `atomicTargetsOk`: `store` takes no target,
the rest 0 or 1 through `targetsPlan`); `Cont.atomicStK` (the
`syncStK` mold: address then value operands, one apply);
`atomicCompute` (the pure value semantics — `IntKind.normalize` is
spec#Integer_overflow's wrap, which is what `Add` realizes;
`AddUint32(&x, ^uint32(c-1))` is the documented decrement);
`applyAtomicOp` (ONE step: load the cell — it must be an integer AT
THE OP'S KIND, else `stuck` — compute, `atomicStore`, deliver the
result through `enterRecvTargets` (the `onceBegin` shape), every
proceeding outcome wrapped in `.opDone .postOp`). Rules
`Step.atomicSt{First,Shift,Apply,ApplyPanic}`; `stepFn` arms verbatim.
`Config.atBoundary` admits the apply position (Multi.lean).

**The forced point.** mem#atomic — "If the effect of an atomic
operation A is observed by atomic operation B, then A is synchronized
before B. All the atomic operations executed in a program behave as
though executed in some sequentially consistent order." / "The
preceding definition has the same semantics as C++'s sequentially
consistent atomics and Java's volatile variables." A conforming
implementation may not weaken these (inventory U-6): the machine owes
EXACTLY SC — a direct upper bound from the text.

**The envelope statement (at `applyAtomicOp`).** Each op is ONE
indivisible pool step at a registry boundary, so an execution IS an
interleaving of atomic steps and that interleaving IS "some
sequentially consistent order": ⊇ SC because any SC order of the ops is
realized by the L1 schedule that runs their steps in that order (C1's
width — `l1Sched`/`postOp`); ⊆ SC because no non-SC mixing is
expressible when every op is a single step. WHICH SC order occurs is
C1's existing latitude: the apply consumes NOTHING from the choice
stream — **zero new `ChoiceSite` constructors** (the census is
unchanged; `Choices.consumeAt` has no new caller). Single-goroutine
atomic programs are stream-transparent (sequential conservation
untouched; `stepFn_oblivious` extends by the sync recipe).

**The executable check that the realization is neither wide nor
narrow:** `sync/atomic-frontier/mp-litmus` (membership) — writer
stores data then flag, reader loads flag then data — enumerates
EXACTLY {0, 1, 11}: the SC-excluded 10 ("flag seen, data missed") is
mechanically absent; gc's 400/400 → 0 is a member. Flipped green this
wave (sites 8 → 32: every apply and its `postOp` completion is a
consult).

**Panic surface.** A nil address is gc's recoverable "invalid memory
address or nil pointer dereference" (`valueAsLoc`, before any effect —
gc's `racecallatomic` and the intrinsic alike fault on the address
first: no store, no HB edge, nothing recorded by `-race`;
`atomics/ops/nil-address{,-recovered}`, `atomics/typed/nil-receiver`).
No alignment panic: the oracle is linux/amd64, where 64-bit atomics
need no alignment; the 32-bit `unaligned 64-bit atomic operation`
fatal is outside the pin (R1's transfer caveat).

**F4 non-foreclosure (memo §2).** Atomic ops are statement-anchored by
the ANF hoist and fused, so no expression-position atomic step exists
for a future expression-machine reshape (Q-ATOMICITY, BUG-002) to
split. Nothing here decides F4's question.

## 4. The detector: TSan-realized edges ∪ go_mem kinds (they coincide)

`GoLean/GoCore/Race.lean`, section "sync/atomic — the per-address
clocks and access kinds"; `raceUpdate`'s atomic arm (Multi.lean).
Under the Q-U4RESIDUAL (A) standard the detector records TSan's
realized set ∪ go_mem's operation kind, each at its gc word. For
atomics the word IS the addressed integer cell (no `syncWord` sub-path;
a typed wrapper's op lands on its `v` field), and the two registers
coincide row by row:

| op | TSan (`tsan_go.cpp` → `tsan_interface_atomic.cpp`, the linked `race_linux_amd64.syso`'s source) | go_mem (mem#model kinds; mem#atomic edge) | machine (`atomicOpKind`; `RaceState.atomic*`) |
|---|---|---|---|
| Load | `AtomicLoad(mo_acquire)`: `Acquire(s->clock)` THEN `MemoryAccess(kAccessRead ∣ kAccessAtomic)` | atomic read = read-like; observing a store ⇒ its writer synchronized-before | `atomicAcquire` then record `.atomicRead` |
| Store | `MemoryAccess(kAccessWrite ∣ kAccessAtomic)` then `ReleaseStore` (OVERWRITE the address clock) + epoch increment | atomic write = write-like; a store observes nothing, so a later observer gets only the storer's predecessors | record `.atomicWrite` then `atomicReleaseStore` (clock := vt; bump) |
| Add, Swap | `MemoryAccess(kAccessWrite ∣ kAccessAtomic)` then `ReleaseAcquire` (join both ways) + increment | RMW observes the previous value (its writer synchronized-before) and publishes | record `.atomicWrite` then `atomicReleaseAcquire` |
| CompareAndSwap | `MemoryAccess(kAccessWrite ∣ kAccessAtomic)` regardless; success → `ReleaseAcquire` + increment; failure → `Acquire` | "both read-like and write-like"; a failed CAS observed the current value | record `.atomicWrite`; success → `atomicReleaseAcquire`, failure → `atomicAcquire` (outcome re-derived from the pre-state by `atomicCompute`) |

Every access is at the cell's own `Loc`, so the path-overlap relation
gives mem#restrictions' mixed rule for free: a plain access to the same
variable, or a whole-struct copy/overwrite of a struct holding the
atomic, conflicts (`race/atomics-misuse/*` — each of the 5 rows has a
probe twin, gc `-race` red 20/20 at GOMAXPROCS 1 and 8); a sibling
field's plain access does not; two atomics never conflict
(`race/atomics-free/*` — each of the 7 rows has a probe twin, gc green
20/20; the membership rows through their spin-form twins). Store's
OVERWRITE (not the sync ops' merge) is both TSan's and go_mem's
realization (C++'s "a store breaks the release sequence"); the probe
`storeOverwrite` is the discriminator (evidence README).

**The one recorded consequence of TSan's record-then-acquire order on
RMWs** (kept — the union rule: nothing the oracle refuses is run here):
A: plain `x = 1` then `atomic.StoreInt64(&x, 2)`; B: ONE `atomic.AddInt64
(&x, 0)` landing after A's store (real time, no HB). go_mem orders A's
plain write before B's Add (the store is synchronized before the RMW
that observes it); TSan records B's atomic write BEFORE acquiring and
reports a race with A's plain write — and so does the machine on those
schedules. An over-refusal against literal go_mem in the fail-closed
direction, aligned with the oracle — for EVERY write-recording head:
probes `plainThenStoreVsLate{Add,Swap,CasSuccess,CasFail}`, gc RACE
20/20 each at GOMAXPROCS 1 and 8 (the failed CAS included: its atomic
write is recorded before its failure-acquire); the Load twin
`plainThenStoreVsLateLoad` (acquire THEN record) green 20/20
(`summary.tsv`). The spin-loop forms first written for this claim
(`plainThenStoreVs{Add,Load}`) do NOT isolate it — a spin RMW or load
landing between the plain write and the store is itself an unordered
atomic beside a plain write, racy by go_mem — and their measurement
(schedule-dependent — RACE 19–20/20 at GOMAXPROCS 8 for BOTH twins
across runs, 0–2/20 at GOMAXPROCS 1) corrected the first prediction; the probe headers and the evidence README record the
correction rather than hiding it.

`racecallatomic`'s ignore path (an address outside the Go heap arena /
data: a non-escaping stack variable) drops the sync effect but keeps
the access — unobservable here (a shared variable escapes; a lone
goroutine cannot race with itself).

## 5. Corpus and evidence

New packages (row counts): `atomics/ops` (25; strict — every op × kind
cell of the 5 × 5 matrix pinned, counting the three frontier rows for
SwapInt32 / CompareAndSwapInt32 / Load-Store-Add Int32+Int64 — the
audit fix round H4 added the six the first cut missed; wrap arithmetic, discarded result, expression position, operand order,
`(*int64)(&definedT)`, nil address ×2), `atomics/typed` (9; strict —
the five wrappers, zero value + copy semantics, empty literal, struct
field, nil receiver), `atomics/counter` (5; confluent — two-goroutine
Add counters incl. typed, CAS retry loop under `backedge=full`, Swap
claim, plain read after join), `atomics/spin` (1; membership under
`nonterm=` accounting — the flag spin-wait, NO termination claim),
`race/atomics-free` (7; 4 confluent + 3 membership — atomic↔atomic,
read/read, the publish/RMW/failed-CAS acquires, sibling words/fields),
`race/atomics-misuse` (5; racy — plain write/read beside Add/Store/
Swap/failed CAS, struct copy beside a typed Add). Frontier flips:
`sync/atomic-frontier/{add-load-store,cas,swap}` FAIL→PASS strict,
`mp-litmus` FAIL→PASS membership; `value` FAIL stays (stage moves).
Probe family: `docs/evidence/2026-09-03_atomics-w1/probes/tsan` (22
subjects — a twin for every race-lane row — `run-tsan.sh`, 20 runs ×
GOMAXPROCS {1, 8}; schedule-dependent subjects reported as ranges).

## 6. Questions NOT decided here (posed, not self-adjudicated)

1. **Q-TRYLOCK's rider — a conflict INSIDE the [USER]-ratified A′
   text itself.** `docs/2026-09-01_qatomic-owner-proposal.md` §6's
   ratified option reads, in one sentence, "fused SC steps, **zero new
   sites**, TSan-realized edges … Q-TRYLOCK rides as a wave-1 rider
   per its pre-ruled envelope" — and that envelope (`docs/2026-08-31_
   qrow-rulings.md` row 5; memo §5) IS a new width-2 `ChoiceSite`
   (mem#locks' spurious-failure member; "the first op that needs a NEW
   ChoiceSite"). The two clauses cannot both hold; the dispatching
   brief inherited the "zero new sites" clause as a hard rule. This is
   the [USER]'s own text to break, one way or the other — not a
   brief-vs-proposal drift — so the lane implemented NEITHER reading:
   TryLock is not in wave 1. The two resolutions on the table: (a) the
   census gains `tryLock` (A′'s "zero new sites" read as "zero new
   sites FOR THE ATOMICS"; one S slice, ~`applySyncOp` arm + site +
   membership rows), or (b) the rider moves off A′ to its own item.
   **RESOLVED [USER] 2026-09-03** («(4) Atomics - agree», relayed — the
   rulings sheet's 2026-09-03 sitting record): (a)+(b) together — its
   own slice adding the `tryLock` site, the A′ sentence amended for
   TryLock only; LANDED on lane `q-trylock` the same day (rulings row
   5's implementation record).
   **RULED [USER] 2026-09-03 (relayed by the [AGENT] coordinator; not
   firsthand): TryLock is its OWN small slice adding the `tryLock`
   ChoiceSite — the A′ zero-new-sites sentence is amended for TryLock
   only** (record: `docs/2026-08-31_qrow-rulings.md` row 5 + its
   2026-09-03 appendix record).
2. **D-002 confirmation** (§2) — owed at dispatch, posed in the report.
   The audit's concurrence, recorded with its caveat: the E5-T shadow
   model is NOT shim injection *precisely because* the method bodies
   are gc's own definitions transcribed, not a re-implementation of
   library behavior — which is why the transcription PIN
   (`tools/nativefrontend/atomics_test.go`
   `TestAtomicShadowModelTranscribesUpstream`: every one of the 25
   modeled method bodies parsed out of the pinned
   `deps/go/src/sync/atomic/type.go` and compared go/printer-normalized
   against `atomicModelSrc`; run by `scripts/ci`'s frontend-unit-tests
   step, red-first tested) is what makes the argument HOLD rather than
   merely be asserted. A pin drift or a model edit that departs from
   upstream turns the argument red.
   **CONFIRMED [USER] 2026-09-03: the typed-wrapper shadow model is NOT
   shim injection under D-002** («(4) Atomics - agree», relayed by the
   [AGENT] coordinator; D-002's row in `docs/discrepancy-backlog.md`
   carries the same note).
3. **Wave 2** (recorded in TODO.md): `atomic.Value` (interface slot;
   gc's nil-store and inconsistent-type panics probed red-first),
   `atomic.Bool`, `And*`/`Or*` (+ the wrappers' `And`/`Or`), and the
   `Pointer` family's vehicle (unsafe policy).

## 7. Records touched

Inventory U-6 (modeled; the surrounding-plain-access envelope is
mem#restrictions/C10 — realized by the atomic access kind); the
language-coverage ledger's `atomic` row and its Q-ATOMIC design-question
row; the coverage ledger (new area); TODO.md's Q-ATOMIC item; BUGS.md
(no new bug: every new row is born-PASS or a stage-moving FAIL already
on the frontier's record); `baselines/native-full.tsv` re-pinned with
the flip list; `Corpus/coverage/exec/sync/atomic-frontier/` header.
