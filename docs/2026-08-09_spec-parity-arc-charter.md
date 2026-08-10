# The spec-parity arc — charter (2026-08-09)

Status: DECIDED (user sign-off 2026-08-09) — D1 BOTH (triple + readout
twin, the golden precedent); D2 NATIVE (Actris port recorded as future
option, comparison at the export layer); D3 CURATED (one exemplar per
feature class designated + Comparator-replayed; bulk proven +
gate-checked in a tracked manifest); D4 AS STATED (blocking primitives
in; atomics/sync.Map/Cond/Pool out). ADDITION (user 2026-08-09):
slice 1 OPENS with the F15 observation-channel fix (grossmith hunt —
integer kind/width + defined-type identity in the observation JSON,
symmetric encoder change both sides in one commit; see TODO.md entry)
before the laws-spine work. Structure per the 2026-08-08/09 discussion. Basis:
`docs/2026-08-07_goose-comparative-scoping.md` (the rung ladder;
their 376 wp lemmas / 28 proved oracles / ~55 proved channel examples
— the oracle count corrected 2026-08-10 at the S3 audit: this line and
its source doc originally said "37 proved", which counted their 36
`test_fun_ok` lemma STATEMENTS plus the non-oracle `wp_shouldPanic`,
i.e. it counted 7 `Abort`s and 1 `Admitted` as proved),
`docs/goose-perennial-comparison.md` (the standing matrix),
`docs/2026-08-08_goose-parity-end-of-buildout.md` (the imported corpus
this arc proves things about). The buildout delivered corpus parity;
THIS arc delivers SPEC parity: for goose/Perennial's proved examples,
prove our analogues — Iris triples internally, adequacy-exported
first-order corollaries designated — so the comparison becomes
statement-by-statement, and our exports ground in a tested semantics
where theirs quantify an untested model.

## Slice-1 record (2026-08-09, branch `spec-parity-s1`)

DELIVERED, gate green at tip, four commits: (1) the F15 guardrail
corpus (`ints/observation-kind/*`, the BUG-042 right-value/wrong-kind
template); (2) F15 FIXED — both observation encoders emit the integer
kind symmetrically, decode fail-closed (ten concrete kinds,
range-checked; `uintptr` refuses on both sides since the frontend maps
it to uint64), zero corpus drift — no hidden kind divergence existed —
with two tracked observation records legitimately re-pinned
(google-search certified set re-enumerated under `--slow`;
hidden-dep-order deviation pin); (3) BUG-034 + BUG-037 FIXED — the
round-4 spine migration re-applied WITH the anchored WP law families
restated over it (`wp_assign*` incl. the `wp_assign_lit` witness,
`wp_map_lookup` + `wp_map_lookup_start`, the new registered spine step
laws, the `wp_seqCont_nil`/`wp_stores_done_nil` generic-continuation
drain), every consumer re-proved, the five held-open pins flip;
(4) BUG-025 FIXED — call write-back on the storeK spine (TargetRefs
through `Cont.frame`, frame-exit `storeMany` retired), frame-exit law
family restated with unchanged pre/posts, the three call-write-back
pins flip. All EIGHT recorded held-open pins are green; designated
statements untouched (44, byte-identical); no new Choices sites.
Deferred with a reason: the `typeAssert` spine-entry WP law has no
consumer yet and therefore ships with none (a law without a witness is
a scaffold — `Laws/StmtOps.lean` records it; it lands with its first
consumer). The assignment-adjacent frontend-export refusals
(`maps/tuple-assign-key-eval`, imported-goose `multiple-assign-to-map`,
`reverse-assign-ops*`) are FRONTEND coverage gaps, not machine pins —
the machine now supports map-element call targets, so enabling them is
a frontend slice when scheduled.

**S1 audit-fix round (same date, four commits):** (1) BUG-052 red-first
pins — the audit's major: call write-back read target operands
pre-call, gc reads them post-call (spec-unordered latitude, no Choices
consumed; five probe genres + the hoisted-control guard); (2) BUG-052
FIXED — the call evaluates first, the caller-target PLANS ride
`Cont.frame` (+ caller env) and their operands evaluate at frame exit
through the tgtOpK spine (gc's realized point, PINNED at the rule site
with the spec text verbatim, version-tracked), laws restated
(`wp_call_start`, `wp_tgtop_stores`, the frame-exit family with
post-call `hres` premises), the storeK arity refusal made path-neutral,
the sequencing eval pin retuned 901→91 with the reason; (3) the
google-search slow lane re-certified — the spine's step growth had
pushed it past its 40M work cap (RED under `--slow`, invisible to the
default gate); cap raised to 60M and the set re-checked COMPLETE at
exactly the six members; (4) scaffold/prose cleanup — the three
witness-less step cores deleted with tombstones
(`wp_read_store_step₂`, `wp_stmt_op_apply_read_store₂`,
`wp_read₂_store₂_step`), the Audit ledger's stale witness clauses
corrected, the dangling law names in `Laws/Eval` fixed, `assigneesExprs`
+ its lemma removed, this file's "eleven" corrected to the recorded
EIGHT. The audit's refuted finding (granularity ledger) required no
action.

## Slice-2 record (2026-08-09, branch `spec-parity-s2`)

DELIVERED, gate green (`scripts/ci --slow`) at tip. The sync package
is live as a registry growth: Mutex/RWMutex/WaitGroup/Once as machine
primitives (value-semantics cells, one blocked shape, cell-based wake,
ZERO new Choices sites — acquisition order is L1 latitude, envelope
statement at `applySyncOp`), the probed-fatal class (`GoError.fatal` +
`expected_status: fatal`, refuting this charter's "recoverable
unlock-of-unlocked" parenthetical — probe p01), HB edges per the
package-doc sentences (two-clock RWMutex realization, the p14
discriminator; the wg misuse sema pair), interpreter/relation lockstep
throughout (a crash checkpoint 2fc4f4f0 sits honestly mid-branch,
completed by the next commit). 35 red-first guardrail pins: 33 green,
2 permanent out-of-scope markers (Cond/TryLock). Lanes: sync
confluent/membership/racy rows all certified; workers-join strict with
the recorded beyond-caps reason. Phase-2 tail: the FOUR sync-only
goose files land at R1 green (importer `--allow-import` seam); the
other 13 stay blocked by their other imports, recorded per-file.
Full record + parking ledger (5 user-scale items for the check-in):
`docs/2026-08-09_sync-package-design.md` §§11-12. Designated
statements untouched (44, byte-identical); untriaged ledger back to
16; corpus 1458 (1348/110), zero drift on every prior id at all three
re-pins.

## Slice-3 record (2026-08-10, branch `spec-parity-s3`)

DELIVERED, gate green at tip; three build commits + the S3 audit fix
round (slice note `docs/2026-08-10_wp-walk-driver.md`; manifest
`docs/spec-parity-r3-manifest.md`; this record REWRITTEN at the fix
round — the first version carried the "proved-37" denominator and
called all five nil rows upstream-proved, both wrong). Exemplar-first
as chartered: `testCompareNilToNil` (upstream `Qed`, nil.v:31 —
Perennial's measured proved set is 28 of 36 stated `test_fun_ok`
oracles, 7 `Abort`, 1 `Admitted`) hand-proved end-to-end through the
laws spine to the D1 pair — `GoSpecC` at full `InitialSplit` strength
(sequential-degenerate lane, stated so) + the pool-carrier first-order
readout twin — over the staleness-guarded pinned lowering; then the
`go_walk` re-derivation (statement byte-identical, hand walk preserved
as witness); then the scale-out. R3 standing: **6 proved**, split
honestly BOTH directions against upstream: 2 upstream-Qed parity rows
(`testCompareNilToNil`, `testComparePointerWrappedDefaultToNil`),
3 rows upstream ATTEMPTED AND ABORTED that we discharge (their TODOs
name the missing lemmas), 1 same-class row with no upstream statement
(semantics/block); the deltas AGAINST us are FIVE upstream-Qed
oracles (delta-review recount): `testInterfaceNilWithType`
(out-of-class at R3 — short-circuit `Expr.and` has no WP law; the gap
is named, not skipped) plus four frontend-blocked at R1
(`testStructUpdates` + the three type-equality oracles, the recorded
short-circuit-operand quarantine — manifest rows). 5 not-attempted
with reasons; 76
unpinned units (71 with ≥1 R1-green row — recounted at the fix round;
the import-tooling lever, P-S3-2). Shared machinery:
`Specs/GooseParityKit.lean` (the wrapper-shape pin + wrapper/driver
walks + the generic TotalPins-seed readout derivations) and one
general law with same-commit witness (`wp_new_value`, the allocating
apply core's third instance; the fix round wired all three new laws +
their witness walks into the Audit witness registry and instantiated
the R2+R3 composition, `compareNilToNilTerminatesNormally`).
Designation: CANDIDATES only (`compareNilToNilSpecC` +
`compareNilToNilReadoutC`), per D3 — the designation-time def-only
hoist cost is recorded at P-S3-1. Driver policy adopted the hard way:
new laws default to UNREGISTERED in the `go_walk` table (a
registration moved the standing quorum walks' stopping points).
Designated statements untouched (44, byte-identical); proofs-only,
zero corpus drift — all 1465 ids match the tracked baseline on
`result`+`stage` per id, the recorded regression signal (1351 PASS /
114 recorded FAIL; "bit-identical" wording scoped at the delta
review); axioms `[propext, Classical.choice, Quot.sound]`
throughout. Parking ledger P-S3-1..5 in the slice note §6.

## Slice-4 record (2026-08-10, branch `spec-parity-s4`)

DELIVERED, gate green (`scripts/ci`) at tip; the design-note commit,
three build commits, and this record commit (design note first, per
the binding discipline — `docs/2026-08-10_gospecc-decomposition.md`,
whose §§8–10 are the authoritative build log / owed list / parking
ledger). (1) THE DECOMPOSITION PIPE (charter item 4's successor debt):
`LangD.lean` — the per-thread `StepDC` relation (deliberately wider
∃-envelope, recorded), the pairing SIMULATION (`stepM_erasedD`: every
`StepM` step is 1–2 erased one-thread D-Language steps; the O1(a)
whole-delta-on-`pairArrive` choice — predicted by the note's §2
per-arm read — made the anticipated storeLoc round-trips
unnecessary; wording corrected at the S4 audit round: the §2 fact
itself is not consumed by the proof), run erasure, heap-handover pool adequacy, THE EXIT
(`goTripleC_of_wpD` — `GoTripleC` at full `InitialSplit` strength from
a D-Language WP, consuming the pairing simulation generically), the
`wpD_*` law kit, and the witness `spawnNoopTripleC` — the FIRST
frame-quantified `GoTripleC` on a genuinely spawning program (the
debt's TRIPLE half, which was the recorded obstruction), non-vacuity
via the witness PAIR `spawnNoopReadoutC` +
`spawnNoopTerminatesNormallyC` (the completion pin added at the S4
audit round — the readout alone left the run premise unexhibited). The SAFETY half (∀-heap `ProgressExecC`, the
pool-reachability first instance) and the `GoSpecC` assembly are
recorded owed WITH their consumer (P-S4-1), as are the channel WP law
family + protocol layer (P-S4-2). (2) The checker's
non-consuming-select refinement (`selectApplyDone`), witnessed
positive AND negative (golden select-probe cert + the two-ready
refusal control). (3) The CURATED CHANNEL ROWS at the design note's
§6(a) strength: trio + muxer(async, client) + dsp — five kernel
theorems each over three new staleness-guarded pins, manifest feature
class 3 with per-row upstream ground truth at 43d4efa (trio +
`wp_Client` + `wp_DSPExample` Qed with line numbers; `Async` has NO
upstream lemma), deltas recorded BOTH directions with no ordering
claim, and the frame-quantified-triple gap named PER ROW — plus the
uncovered-population paragraph (60 upstream Lemma/Theorem items,
commands cited). Designation: CANDIDATES only (`dspCert` +
`dspAllSchedules`; `spawnNoopTripleC` deliberately not until its
`GoSpecC` assembles); designated statements untouched (44,
byte-identical — verified by `git diff` over the branch range, the
name-list/closure gates green besides); proofs/checker-layer only —
the INTERPRETER untouched, and the slice's one `GoLean/GoCore/` edit
is `MultiStreams.lean`, kernel-checker infrastructure strictly
import-DOWNSTREAM of `Multi.lean` (it cannot alter
`execProg`/`stepFn` — semantically neutral for the corpus, per the S4
audit's verification); zero corpus drift (1465 ids on
`result`+`stage`) — re-established FIRST-HAND at the S4 audit round
by a fresh full `scripts/ci --diff` — PASS, `baseline diff FULL
(1465/1465, no regression)`, no stale marker (the build commits'
figure had inherited the cached pre-base run at 419010a, which the
gate marked "stale"; full run identity in the design note §8);
axioms the classical trio (simulation lane constructive,
`[propext, Quot.sound]`).

## The sync question (asked 2026-08-09), answered

Sync is NOT a prerequisite for spec-parity over the imported corpus
(their proved channel examples and sequential oracles need no sync;
channels are our primitives). But it IS the gating unlock for the 17
phase-2 import files, their idiom libraries, and — decisively — the
north-star target itself (etcd-raft uses sync.Mutex/WaitGroup
throughout). And the channels arc built the exact extension mechanism
sync needs: the synchronization-op registry (D2+D3 growth contract —
a new primitive registers as one scheduling point + one HB edge rule,
nothing revises). So: SYNC IS A SLICE OF THIS ARC, not its own —
slice 2, after the laws spine, unlocking phase-2 imports mid-arc so
the proof slices can cover them.

## Slices

1. **The assignment-spine laws slice** (the recorded prerequisite):
   retire the three eager paths (BUG-025 call write-back, BUG-034
   comma-ok, BUG-037 single-assign) onto the tgtOpK/storeK spine and
   restate the anchored WP law families (`wp_assign*`,
   `wp_map_lookup` + the quorum walk's consumers) over it — one
   machinery retirement, one law rework, three consumers, the EIGHT
   recorded held-open pins flip. (Count corrected at the slice-1
   record + S1 audit: this bullet originally said "eleven"; the
   authoritative owner map records 5 (BUG-034/037) + 3 (BUG-025) = 8.
   If the extra three meant the assignment-adjacent frontend-export
   refusals, those were never machine pins and are out of this
   slice's machine+laws scope — deferred to a frontend slice, per the
   record below.) WP-walking imported programs hits these laws
   constantly; clean foundation first.
2. **The sync package** (registry growth): `sync.Mutex`/`RWMutex`/
   `WaitGroup`/`Once` as machine primitives — each a registry entry
   (scheduling point + HB edge per the memory-model text, quoted at
   the site); real recoverable panics (unlock-of-unlocked etc.);
   guardrails first from the 17 phase-2 goose files + fresh edge
   cases; racy/litmus lanes extended; `FairStream` NOT in scope
   (spin-waits via mutex contention are parked to the atomics arc as
   recorded — sync ops BLOCK, so the blocking-discipline termination
   class still applies; state this precisely in the slice note).
   Unlocks: phase-2 imports land at R1/R2 in this slice's tail.
3. **The WP-walk driver, exemplar-first**: hand-prove ONE feature
   class end-to-end (recommended: their proved sequential oracles —
   the `test_fun_ok` set) to fix the spec shape, then build the
   `go_walk`-driven automation (tactic walking lowered programs,
   applying laws, leaving side-goals) and scale across the imported
   corpus. Proofs stay kernel-checked; the tactic is never trusted.
4. **Channel-spec exemplars**: the frame-quantified `GoSpecC`
   decomposition for spawning programs (the recorded successor debt:
   park/deposit/wake through the one-thread-step Language interface,
   pool-reachability kit), then triples + exports for a curated set
   of their proved channel examples (the select-tricky trio, muxer,
   dsp example — the flagship comparisons).
5. **The parity table + arc closure**: the per-example comparison
   artifact (their lemma ↔ our internal triple ↔ our export ↔
   strength delta) as a standing doc section; matrix rows updated;
   end-of-arc audit (user-asked, pre-merge) + Comparator landmark
   (the designated set WILL grow — see D-item 3).

## Decision items for the user (D1–D4)

**D1 — Exported-spec shape** (the natural-spec question): recommended
BOTH per the `goldenSpecC`+`goldenReturnsTwoC` precedent — the
frame-quantified triple designated AND a first-order readout twin;
pre/posts for stateful examples phrased as operational state
assertions (history predicates only where a channel protocol demands
it). USER CALL — this is the project's spec idiom being set.

**D2 — Concurrent spec style**: mirror their Actris/dsp protocol
layer (weeks-scale port; literal spec-to-spec comparison) vs native
invariant+ghost internally with comparison at the exported level.
Recommended: NATIVE for this arc (the export layer is where our
comparison advantage lives; an Actris-lite port is recorded as a
future option, not taken). USER CALL.

**D3 — Designation policy at scale**: recommended CURATED — per
feature class, one exemplar triple + export joins the designated
list (Comparator-replayed); the bulk are gate-checked (axiom-pinned,
statement-TCB-scanned) but undesignated, listed in a tracked
manifest. Prevents silent list ballooning. USER CALL.

**D4 — Slice-2 scope line**: sync.Mutex/RWMutex/WaitGroup/Once in;
`sync/atomic`, `sync.Map`, `sync.Cond`, `sync.Pool` OUT (atomics are
their own arc — FairStream's gate; the others are library-shaped).
Recommended as stated. USER CALL (cheap to widen later by the same
registry contract).

## Binding discipline (inherited, not open)

Everything from the standing doctrine: guardrails first; relation/
interpreter lockstep for every machine change; envelope statements at
every new registry entry argued from spec text; fail closed; zero
drift on prior ids; designated statements byte-identical except the
declared D3 additions; per-slice sub-branch audits (established
cycle) + the user-directed pre-merge audit at arc end; the
statement-TCB gate extended for every new designated statement;
Iris strictly internal — every designated statement passes the
deletion test; no new Choices sites beyond slice 2's registry
entries. Research-first: slices 2 and 4 open with short design notes
(the sync memory-model rules; the decomposition proof plan) in the
established options format where latitude exists.
