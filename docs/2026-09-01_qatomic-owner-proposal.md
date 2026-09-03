# Q-ATOMIC owner proposal — the atomics arc, post-split (2026-09-01/02)

> **RULING [USER] 2026-09-02** (Mike: "I agree with this approach" —
> the approach as presented is recorded verbatim in
> `docs/2026-08-31_qrow-rulings.md`, appendix "The row-2 ruling
> record"; the quote was relayed to the recording worker by the [AGENT]
> coordinator — citation, not firsthand). **Option A′ RATIFIED. OWNER =
> THIS repo (the semantics product)**: a named lane dispatched from
> TODO.md ("Q-ATOMIC arc"), sequenced into Tier 5 with §5's ordering
> constraints carried. **DECOUPLED: BUG-080's detector atomic-access
> KIND** (§4 wave 1's detector bullet — `RaceAccess := Kind × Loc`,
> atomic↔atomic non-conflicting, atomic↔plain conflicting, recorded at
> the sync cell's path) does NOT ride this arc: it is pulled forward as
> its OWN S–M slice, sequenced BEFORE the arc, with the two costs §4
> names (one `syncData` cell per primitive vs the `locPrefix`
> over-refusal + the `wgSemaAccess` carve-out; gc's per-primitive
> instrumentation differences) checked in that slice — §4's "BUG-080
> rides HERE" sentence and its "Revisable" clause are superseded by
> this header. **OUT OF SCOPE: FairStream / the `Fair`-quantified claim
> class** — reasoning-side future work TO BE BUILT (§2), confirmed by
> the same-sitting fairness doctrine ruling
> (`docs/2026-08-11_essence-of-go-doctrine.md`, "Scheduling and
> fairness"). Ruling of record: `docs/2026-08-31_qrow-rulings.md` row
> 2. The body below is the memo as presented, unchanged.

[AGENT] memo, written on the Tier-4 detector-soundness lane
(`t4-detector-soundness`) as the rider the Q-row ruling sheet asked
for: `docs/2026-08-31_qrow-rulings.md` row 2 holds Q-ATOMIC OPEN
pending "(a) FairStream must read as future work TO BE BUILT, and
(b) the arc has NO live owner post-split — ratifying requires naming
one." This memo supplies both refreshes and returns the row to the
[USER] for ruling. It implements nothing; the design argument of
record stays `docs/2026-08-21_w32-qrow-memos.md` §2, cited below
rather than repeated.

## 1. What is in hand

- **Reds (5, unchanged since slice 6):** `sync/atomic-frontier/
  {add-load-store,cas,swap}` (frontend-export refusals),
  `sync/atomic-frontier/value` (lean-observation), and the model pin
  `sync/atomic-frontier/mp-litmus` (membership: admitted {0, 1, 11},
  SC-excluded 10; gc sample 400/400 → 0). `baselines/native-full.tsv`
  rows 2651–2655 at this tip.
- **The forced point:** mem#atomic (pinned go1.26.5 `go_mem.html`,
  quoted in memo §2 and inventory U-6) — atomics "behave as though
  executed in some sequentially consistent order"; a conforming
  implementation may NOT weaken them. So the machine owes exactly SC:
  no weaker outcomes (too-wide against the text — one of the rare
  direct upper bounds), no missing SC outcomes (too-narrow; the
  mp-litmus set is the executable check).
- **The design of record (memo §2 option A):** fused single-step ops
  at a registry boundary taking B1's `.opDone`, zero new choice sites
  (SC falls out of the L1 interleaving of indivisible steps), value-
  returning op family in the `syncStmt` mold, TSan-realized detector
  edges + an atomic ACCESS KIND that conflicts with plain accesses
  only. F4 non-foreclosure by construction (statement-anchored by the
  ANF hoist; no expression-position atomic step exists to split).
- **Consumers:** none in the raft target — `deps/raft` (etcd raft,
  the north-star subject) imports `sync/atomic` in ZERO non-test
  files at the pin; `raftsubject/` likewise. The demand is the
  whole-language bar (the frontier suite) and the spin-wait idiom
  class, not raft. That bears on sequencing (§5).

## 2. Refresh (a): the FairStream tier is FUTURE WORK TO BE BUILT

Stated plainly, so the ruling cannot rest on a phantom: **no `Fair`
or `FairStream` predicate is a Lean definition** in this tree, on the
parked reasoning branch, or on any branch tip (phase-2 fact claim 7,
verified 2026-08-31; restated at doctrine register #1 residue (ii)).
What EXISTS is the semantics-side precondition only — the `backEdge`
choice site (B2) whose docstring records that a fair scheduler is
EXPRESSIBLE over the widened boundary set. The fairness-precision
note (`docs/2026-08-07_fairness-precision-note.md` §3) records that
the tier is needed for the atomics-FREE spinner idioms too
(select-`default` pollers, closed-channel drains, buffered
self-cycles), so it was never an atomics-arc deliverable in
substance; the memo's "FairStream tier bundled" phrasing predates
the split and must be read as follows post-split:

- The **quantifier and any Fair-conditioned theorem are
  REASONING-SIDE artifacts** (CLAUDE.md: this repo makes no
  verification claims). They belong to the parked line / the future
  reasoning repo, which will pin this one. Nothing here can "ship
  the tier"; the atomics arc in THIS repo cannot bundle it even if
  it wanted to.
- What this repo CAN and should do for spin-wait shapes is what it
  already does for other divergent idioms: run them in the
  membership lane with stage D §5d's `nonterm=N` accounting —
  terminating members certified, fuel-exhausted branches COUNTED and
  never members — and make NO ∀-stream termination claim (the honest
  form the note's §3 already prescribes: such programs are correctly
  outside `TerminatesNormallyC`). That mechanism exists and is
  gate-exercised; it is the executable analogue, not the tier.
- Consequence: memo option (A) "tier bundled" is NOT AVAILABLE as
  written post-split. The live shapes are (A′) — atomics land here,
  spin-wait rows carried honestly under nonterm accounting, the
  Fair-quantified claim class deferred to the reasoning side — or
  (C) defer the family.

## 3. Refresh (b): the owner

Proposal: **the semantics product owns the machine half, dispatched
as its own lane ("atomics arc") from this repo's backlog**; the
reasoning repo owns the Fair-quantified claim class when it exists.
Concretely the owner is a named worktree lane with this memo + memo
§2 as its charter, the five reds as its born-red rows, and the
following deliverables (§4). The [USER] names the dispatch at ruling;
"this owner" below means that lane.

Why not the reasoning side for the whole arc: every deliverable but
the quantifier is executable-semantics work validated by the
differential (frontend lowering, GoCore op family, detector
footprint, corpus rows, the mp-litmus certification) — the trusted
surface of THIS product, gate-covered here and nowhere else.

## 4. Scope and cost (this owner)

Wave 1 — **integer core + mp-litmus** (the 4 non-Value reds):
- Frontend (`tools/nativefrontend` + `GoLean/NativeToIR.lean`): a
  VALUE-RETURNING atomic op family (`Load/Store/Add/Swap/
  CompareAndSwap` over `int32/int64/uint32/uint64` — `uintptr` maps
  to uint64 in this frontend and `unsafe.Pointer` is refused by the
  unsafe policy, so the pointer family is OUT); typed atomics
  (`atomic.Int32` etc., methods) ride the same lowering (the
  ledger's recorded judgment); every other `sync/atomic` symbol
  keeps failing closed at export. Not shim injection under D-002:
  the ops plumb to a machine op family with its own semantics
  argued from mem#atomic, not to hand-modeled stdlib bodies —
  identical in shape to the sync ops, and to be stated so in the
  arc's design note ([USER] confirmation owed at dispatch, as
  Q-SYNCVAL's was).
  Effort S–M.
- GoCore (`Machine.lean`/`StepFn.lean`/`Multi.lean`): one fused
  registry op (`atomicStK`-style frame) that reads-modifies-writes
  the target cell in ONE pool step, at a boundary, wrapped in
  `.opDone .postOp` like every registry op; the nil-pointer panic
  surface probed red-first (gc: "invalid memory address"). No new
  `ChoiceSite` constructor (the census datatype is unchanged; the
  envelope statement goes at the op's docstring).
  Effort M.
- Detector (`Race.lean` + `raceUpdate`): gc's realized edges —
  under -race every `sync/atomic` op is routed to TSan's Go atomic
  hooks (`__tsan_go_atomic32_load/store/...`, reached through the
  `sync∕atomic·{Load,Store,Swap,Add,And,Or,CompareAndSwap}*` TEXT
  symbols of `deps/go/src/runtime/race_amd64.s` — the block headed
  "Atomic operations for sync/atomic package" — via
  `racecallatomic`; `sync/atomic/race.s` is the -race build's
  entry), which realize seq_cst as acquire on
  loads, release on stores, both on RMWs, over the address's own
  clock (so atomics synchronize among themselves — the SC total
  order's HB); plus a new access KIND `atomic` recorded at the loc
  that CONFLICTS with plain reads/writes (mixed atomic/plain =
  refused per C10, exactly as -race reports) and never with other
  atomics. One new arm in the footprint, one per-address clock list
  in the mold of `SyncClocks`. The detector-soundness runner
  (`scripts/detector-soundness`) is the ready-made check that the
  new edges match `-race` in both directions.
  Effort S–M.
  [SUPERSEDED by the ruling header — and LANDED 2026-09-02 on
  `bug080-atomic-kind`: `AccessKind ∈ {read, write, atomicRead,
  atomicWrite}` + `syncEntryKinds`/`syncReleaseTailKinds` in Race.lean;
  this wave CONSUMES the kind (record `sync/atomic` loads as
  `.atomicRead`, stores/RMWs as `.atomicWrite`) and adds only the
  per-address clocks. The paragraph below is the memo as presented.]
  BUG-080 rides HERE by [AGENT] SEQUENCING judgment (audit fix round
  2026-09-02, S4), not by dependency: the atomic access KIND
  (`RaceAccess := Kind × Loc`, atomic↔atomic non-conflicting,
  atomic↔plain conflicting, recorded at the sync cell's path from
  `raceUpdate`'s sync arm) is separable from this wave's lowering
  and could land alone. It is sequenced here because (i) each sync
  primitive is ONE `syncData` cell, so the kind's per-cell access
  must be checked against the `locPrefix` over-refusal and
  reconciled with the `wgSemaAccess` plain-pair carve-out — the same
  per-address footprint design this wave settles for atomics; and
  (ii) gc's per-primitive instrumentation differs (WaitGroup under
  `race.Disable` + the `wg.sema` pair vs Mutex's state CAS), so the
  per-op recorded set is derived primitive by primitive from
  `-race`'s realized set — the `-race` alignment pass this wave
  performs anyway. Revisable: if this arc slips, the kind can be
  its own S slice.
- Enumerator: nothing structural (fused steps branch only through
  L1; no per-op width). `mp-litmus` flips green membership with
  {0, 1, 11} certified and 10 mechanically excluded — the first
  executable check that the SC realization is neither wide nor
  narrow. Effort S.
- Corpus: the 4 reds flip; red-first additions — CAS retry loop
  (nonterm-accounted membership row), atomic/plain mixture racy row,
  typed-atomic twin rows, nil-pointer panic row, an atomic-store
  publish / atomic-load acquire pair (the message-passing edge in
  the detector, confluent). Effort M.
- Gate: full `ci --diff`, re-pin with reasons (FAIL→PASS ×4 + new
  rows), audit ask.
Wave-1 total: **L — 3–5 sessions** (the charter's original sizing
holds).

Wave 2 — **`atomic.Value`** (the 5th red): stores interface values
with gc's panics (nil store; inconsistent dynamic type) — boxing
rules + two panic messages probed; rides wave 1's op family with an
interface-typed slot. Effort M, **1 session**, after wave 1 lands.

NOT in this owner's scope: the Fair quantifier (§2), Q-TRYLOCK's
implementation (memo §5: pre-ruled envelope — TryLock takes
mem#locks' spurious-failure member as a width-2 site — and
"inherits Q-ATOMIC's arc decision": it becomes a rider ON this
arc's wave 1 if the family is ratified, ~S), Q-COND (pre-ruled,
zero demand, its own item).

## 5. Sequencing vs Tier 5

Tier 5 (assessment synthesis §5) is upper-bound realization:
deviation-queue burn-down (E3/E5), the sentence-level latitude sweep,
E9, the frontend-obligation discharge start, NPDRF per decision 1.
The atomics arc is LOWER-bound growth (five frontier reds; a forced
SC point with a direct upper bound from the text) and shares no
files with Tier 5's items except the inventory. Proposal:

1. **After the gotest fix slice** (the [USER]'s "(2) agree" next
   dispatch) and after this lane's merge — the detector-soundness
   runner is the arc's alignment check and should be on main first.
2. **Before or alongside Tier 5's start**, as an independent lane:
   no dependency either way; the only ordering constraint is
   Q-TRYLOCK riding on it and the channel-logic resume (reasoning
   side, parked) wanting atomics modeled before its liveness story.
3. **Not before** the Q-row implementation queue clears its
   frontend-touching items (Q-INITSPAWN `$pkginit` item, Q-SELSEL's
   slot) — the arc edits `emit.go`/`NativeToIR.lean` and re-pins the
   baseline, so sequential beats a merge fight (the Q-SYNCVAL
   precedent).

Priority argument for the [USER]: with raft needing no atomics, the
arc buys the whole-language bar and the spin-wait idiom class (the
liveness story's prerequisite), not the north-star's path. If the
semantics-first goal ranks frontier breadth high, ratify now; if
raft-path items are scarce and urgent, defer with the dependency
recorded — neither choice is a fidelity risk today (the five reds
are honest refusals).

## 6. The ruling options

- **Ratify A′ with this owner** — the atomics arc as scoped in §4
  (fused SC steps, zero new sites — EXCEPT the [USER]-ruled `tryLock`
  site, 2026-09-03 («(4) Atomics - agree», relayed by the [AGENT]
  coordinator; the 2026-09-03 sitting record in
  `docs/2026-08-31_qrow-rulings.md`): Q-TRYLOCK became its OWN slice
  adding that one site, so the atomics' own ops stay at zero —
  TSan-realized edges + atomic access kind, integer core → mp-litmus →
  `atomic.Value`), owned by a semantics-repo lane dispatched per §5;
  spin-wait rows carried under `nonterm=` membership accounting with NO
  termination claim; the Fair-quantified claim class recorded as
  reasoning-side future work TO BE BUILT (not bundled, not cited as
  existing). ~~Q-TRYLOCK rides as a wave-1 rider per its pre-ruled
  envelope~~ (superseded 2026-09-03 as above — the wave-1 lane had
  flagged this sentence's internal conflict, its design note §6; the
  slice LANDED on lane `q-trylock` the same day). *Recommended.*
- **Defer the family (C)** — the five reds stand as honest refusals;
  Q-TRYLOCK's implementation and the liveness story inherit the wait;
  the U-6 forced point stays recorded. Legitimate if raft-path items
  are scarcer than sessions.

Memo §2's original option (A) — "FairStream tier bundled" — is
recorded here as NOT AVAILABLE post-split (§2), so the sheet's
three-way menu (A / A′ / C) collapses to the two above. Option (B)
(weaker-than-SC) stays rejected on the quoted text.

This memo returns to the [USER]; the ruling lands in
`docs/2026-08-31_qrow-rulings.md` row 2 and binds the dispatched lane.
