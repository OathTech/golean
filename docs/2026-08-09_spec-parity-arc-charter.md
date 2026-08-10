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

## Slice-5 record + ARC CLOSURE (2026-08-10, branch `spec-parity-s5`)

Slice 5 is RECORDS-ONLY (work-plan item 5): zero Lean edits, zero
corpus edits — the parity table, the matrix brought to arc-end state,
this closure record, the cross-reference sweep. Gate at tip:
`scripts/ci` PASS — every step fresh (proofs + Audit gate, statement-TCB
closure, imported-pins staleness guards, eval tests, negative diff)
EXCEPT the full-differential line, which is the CACHED full run
recorded at 1c0b293f (`baseline diff FULL (1465/1465, no regression)`,
gate-marked stale because HEAD moved) — that cached run is the S4
polish round's FIRST-HAND fresh run at this branch's base content, and
the s5 window cannot drift it by construction: `git diff --name-only
bab76304..tip` is docs/ + TODO.md only (stated per the S4 stale-figure
lesson, not silently inherited). The 44 designated statements are
byte-identical over the slice (no proofs/ path in the diff; name-list
and closure gates green).
Deliverables: **the per-example spec-parity table** as matrix §7
(`docs/goose-perennial-comparison.md` — location choice recorded
there: the standing matrix is the one canonical comparison home;
every upstream status re-measured at 43d4efa with the command cited),
matrix rows T1/T3/T7/T10 + §5/§6 updated with correction notes, the
consolidated agenda below.

### The arc in slices (39 commits before this slice, `git log
--oneline main..spec-parity | wc -l`; each slice's own record above is
the authoritative accounting)

| slice | shipped | audit cycle → outcome |
|---|---|---|
| S1 (laws spine + F15 opener) | F15 fixed symmetrically; BUG-034/037/025 retired onto the tgtOpK/storeK spine, law families restated, all 8 held-open pins flipped | audit round found BUG-052 (call write-back operand timing — a real machine bug, red-first pinned then fixed) + the slow-lane cap miss; 4 fix commits + 2 delta-polish; 1 finding refuted |
| S2 (the sync package) | Mutex/RWMutex/WaitGroup/Once live end-to-end (registry growth, ZERO new Choices sites), probed-fatal class, HB edges, 33/35 pins green (2 permanent out-of-scope: Cond/TryLock), 4 sync-only goose files R1 | audit fix round + delta rounds 2–4; round 4 CRITICAL (the import vet rebuilt on Go's own grammar) + residue cleanup; crash checkpoint 2fc4f4f0 recorded honestly mid-branch |
| S3 (WP-walk driver) | THE EXEMPLAR + 5 more R3 D1 pairs (GoSpecC + readout twin over pinned lowerings), the kit, `wp_new_value` witnessed, the go_walk re-derivation + registration lesson, the tracked manifest | audit fix round (~4 surviving majors, ALL claims/records — the parity denominator corrected 37→28-of-36 at origin and every restatement) + delta polish (zero surviving critical/major) |
| S4 (decomposition + channel rows) | the non-consuming-select checker refinement (witnessed both ways), 6 curated channel rows × 5 kernel theorems, the decomposition pipe through THE EXIT, `spawnNoopTripleC` + witness pair (the debt's TRIPLE half) | one polish round, zero critical/major; the load-bearing minor (stale inherited differential figure) fixed by a fresh full run FIRST-HAND |
| S5 (this) | records only: parity table, matrix arc-end state, this record, sweep | sub-branch audit to follow (records dimension) |

### The standing red set, with owners (measured at this record)

**1465 ids: 1351 PASS / 114 recorded FAIL** (`awk` over
`baselines/native-full.tsv`; zero drift all arc — every slice tip
matched the tracked baseline on `result`+`stage` per id).

- **85 `frontend-export`** — recorded fail-closed frontend coverage
  classes; owner: future frontend slices, scheduled by value. Named
  subsets: the 20 imported-goose rows (dominated by the
  short-circuit-operand quarantine — including the FOUR upstream-Qed
  oracles named in manifest/§7.1, the highest-leverage frontend item
  this arc surfaced), the S1-recorded assignment-adjacent refusals
  (map-element multi-assign targets), the sync Cond/TryLock
  out-of-scope markers (owner: atomics arc / D4 widening).
- **29 fidelity-stage** (23 lean-observation + 4 differential + 1
  nondet + 1 go-run), split per `scripts/check-bugs.sh --list`:
  - **16 untriaged** (the ratchet, `baselines/untriaged-count`) — of
    which the DELIBERATE permanent entries carry their own records:
    floats/to-int-out-of-range ×2 (fail-closed refusals, never flip),
    init/hidden-dep-order (permanent deviation record),
    channels/select-select ×2 (owner: the successor select slice —
    matrix T12b), goroutines/spawn-in-init (init-phase concurrency,
    unowned); the genuine backlog is the strings rune-conversion class
    ×7 + arrays/pointer-array + pointers/nil-array-index-panic +
    structs/tag-pointer-conversion (pre-existing, untouched this arc).
  - **13 explained by a `docs/BUGS.md` entry** — maps *-during-range
    (BUG-005 class), the panic-recover payload-method rows (the parked
    `runtime.Error` scoping, TODO.md G1 entry), nil-literal-values +
    imported-named-key rows, the two race-lane markers,
    spawn-edge/nil-func-fatal (P-S2-2's parked migration).

### The consolidated parked-items agenda (EVERY item ledgered this
arc; grouped as the user's check-in agenda — nothing here was decided
unilaterally)

**A. Designation / spec-idiom calls (D3 curation, user-owned):**
1. **P-S3-1** — designate the sequential exemplar pair? Cost is the
   F4 def-only hoist + Challenge/Solution/judge-config/Audit wiring
   (accounting in the S3 note §6).
2. **S4 candidate** — designate `dspCert`+`dspAllSchedules` (channel
   class exemplar)? Same hoist pattern (P-S4-4's `chanCert_*` move
   rides along).
3. **P-S2-3** — the sync feature class has NO candidate (the arc's
   proof slices never reached sync specs); decide whether the sync
   spec layer opens the successor arc.
4. **P-S3-3** — keep or trim the duplicated hand walk
   (`wp_compareNil_body_hand`). Default keep.
5. **P-S3-5** — the joint sequential "completes-AND-verdict" form:
   ship per-row, ship a pool-carrier `TerminatesNormallyC` variant, or
   leave the two halves as stated.
6. **P-S4-4** — `chanCert_*` hoisting; default keep-local.

**B. Successor-arc machinery (scale/order calls):**
7. **P-S4-1** — `ProgressExecC` at ∀-heap strength (the
   pool-reachability kit's first instance) → assembles
   `spawnNoopSpecC`, the debt's full form. Until then the honest claim
   stays "the TRIPLE half is paid".
8. **P-S4-2** — the channel WP law family + protocol layer (the
   curated rows' D1 form 1; consumer seam built, `LangD.lean`).
9. **P-S3-2** — backfill pinned lowerings: 73 unpinned units at arc
   end (9 pinned — S4 added the three channel pin modules to S3's
   six); whether to promote the `.tmp` mkpins helper to a tracked
   script is part of the call.
10. **P-S4-5** — google-search: bespoke certificate vs wait for the
    decomposition lane (its membership cert + §7.3 row carry it
    meanwhile).

**C. Import/corpus cost calls:**
11. **P-S4-3** — reopen the P2 import parking? Two of its rows
    (`wp_MapClient`, `wp_makeGreeting`) are upstream-Qed parity rows
    we cannot certify until it lands.

**D. Lane/model design calls (S2's ledger, §12 of the sync note):**
12. **P-S2-1** — promote `fatal` into membership/confluent lanes?
13. **P-S2-2** — migrate go-of-nil-func onto `GoError.fatal`
    (re-pins a recorded permanent red).
14. **P-S2-4** — `valueEqFuel` refuses `==` at sync types
    (model-vs-refuse when a target needs it).
15. **P-S2-5** — U4 sync-object data-access race scope.

**E. Recorded deferrals riding along (not P-numbered, ledgered in
slice records):** the `typeAssert` spine-entry WP law (S1 — lands with
its first consumer); the short-circuit `Expr.and`/`Expr.or` WP law
family (S3's out-of-class gap; unblocks `testInterfaceNilWithType`);
the short-circuit-operand FRONTEND quarantine (strictly earlier: 4
upstream-Qed oracles blocked at R1); checker L2 branching (S4 §6(c) —
only if a curated row ever needs a ≥2-ready select); **P-S3-4**
`go_walk_step` ergonomics (tactic infra, soundness-neutral); the
NPDRF reduction obligation (pre-existing metatheory debt, matrix T12
— restated, not new).

**Arc-level asks at the same check-in:** the pre-merge adversarial
audit proposal for the WHOLE arc (protocol step 3 — the ask is
unconditional; scope proposal to accompany it) and merge sign-off;
the Comparator landmark fires if/when curation grows the designated
set (D3); the perennial upstream pin (origin/master has moved past
43d4efa — a rev bump is a deliberate recorded event, matrix
maintenance contract).

### Designation candidates for D3 curation (NOTHING designated this
arc; the 44 designated statements byte-identical at every slice tip)

| candidate | statement file | feature class it exemplifies | cost of designating |
|---|---|---|---|
| `GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC` | `proofs/GoLeanProofs/Specs/GooseParityNilWP.lean` | class 1: imported sequential oracle, internal `GoSpecC` triple over the pinned lowering | the F4 def-only hoist (P-S3-1's accounting): the statement's defs live in the Iris-importing kit module and `ImportedGooseNil.lean` carries theorems — a core-import-only statement module must be split out (`ForkJoinTargets` pattern), plus Challenge/Solution/judge-config/Audit wiring and the statement-TCB closure extension |
| `…compareNilToNilReadoutC` | same file | class 1: first-order pool-carrier export twin | shared with the row above (one hoist covers the pair) |
| `GoLean.ImportedGoose.ChannelActris.dspCert` | `proofs/GoLeanProofs/Specs/GooseParityChannels.lean` | class 3: curated channel exemplar, kernel ∀-schedule certificate (upstream `wp_DSPExample` Qed beside it) | same hoist pattern: `chanSeed`/`cellIsInt`/driver/readout defs into a def-only module (P-S4-4's `chanCert_*` derivations move with them) + the same wiring |
| `…dspAllSchedules` | same file | class 3: ∀-schedule verdict readout | shared with the row above |

Deliberate NON-candidates, recorded: `spawnNoopTripleC` (curate the
assembled `spawnNoopSpecC` when P-S4-1 pays the safety half, not the
half-form); the sync class (no theorem exists yet — P-S2-3).

### The exit-criterion walk (the charter's opening deliverable
sentence + the five work-plan items + D1–D4 + the binding discipline;
deferring with an honest log is success — each DEFERRED names its log)

1. **"For goose/Perennial's proved examples, prove our analogues"** —
   DONE at recorded strength, split honestly BOTH directions: 2
   sequential upstream-Qed parity rows at the full D1 pair; 3
   upstream-Abort discharges; 5 upstream-Qed channel lemmas with
   kernel ∀-schedule families beside them; the against-us set NAMED (5
   sequential oracles they prove and we don't — 1 law gap + 4
   frontend-blocked; the channel D1 form open on all six rows).
   Evidence: matrix §7; `docs/spec-parity-r3-manifest.md`.
2. **"Iris triples internally"** — DONE for the sequential class
   (`GoSpecC` through the laws spine, hand + `go_walk`); DEFERRED for
   the channel class — log: manifest FC3's "NOT the D1 pair" paragraph
   + P-S4-2 (the ∀-schedule family shipped instead, gap named per
   row).
3. **"Adequacy-exported first-order corollaries"** — DONE: every
   proved row ships its deletion-test-clean readout/corollary twin
   (readout twins; no-deadlock/no-race/termination corollaries).
4. **"…designated"** — DEFERRED BY DESIGN to the user's D3 curation
   (that is what D3 CURATED decided): candidates recorded above,
   nothing designated by the arc. Log: slice notes §5/§10 + this
   record.
5. **"The comparison becomes statement-by-statement"** — DONE this
   slice: matrix §7, one row per covered example, deltas both
   directions, no ordering claims.
6. **"Our exports ground in a tested semantics where theirs quantify
   an untested model"** — DONE with the S4-corrected wording (their
   Go model PACKAGE is well tested; the Rocq/GooseLang model and the
   translation step are executed by no test — matrix §7 shared-delta
   text carries the accurate form).
7. **Work-plan items**: 1 DONE (S1 record), 2 DONE (S2 record), 3
   DONE (S3 record), 4 DONE at recorded strength — the TRIPLE half of
   the successor debt paid, the `GoSpecC` assembly deferred with its
   named consumer (log: S4 note §9, P-S4-1) — and 5 is this record.
   Item 5's "end-of-arc audit + Comparator landmark" tail is
   USER-OWNED: the audit ask is merge-protocol step 3 (never skipped,
   never self-granted); the landmark fires only if curation grows the
   designated set.
8. **D1–D4 honored as decided**: D1 BOTH (every proved R3 row is the
   pair); D2 NATIVE (no Actris port; comparison at the export layer;
   protocol layer recorded as future work with its consumer); D3
   CURATED (tracked manifest + candidates, zero designations); D4 AS
   STATED (sync scope exactly Mutex/RWMutex/WaitGroup/Once; the outs
   recorded at their sites).
9. **Binding discipline, checked**: guardrails first (F15 corpus, 35
   sync pins, BUG-052 red-first, the negative checker control);
   interpreter/relation lockstep (S2); zero drift at every slice tip;
   designated statements byte-identical throughout (44 — `git diff`
   over the branch range at S4/S5, name-list + closure gates green);
   per-slice sub-branch audits held (trail above — every slice had at
   least one round; two rounds surfaced a CRITICAL or a real machine
   bug, which is the cycle working); no new Choices sites anywhere
   (S2's registry entries consumed none); Iris strictly internal to
   proofs (deletion test on every export). Honest deviations ON the
   record: the S2 crash checkpoint (2fc4f4f0, red mid-branch,
   completed next commit); S4's build commits briefly carrying an
   inherited stale differential figure (caught by its audit, fixed
   first-hand same round).

**Verdict: the arc closes DELIVERED-WITH-NAMED-REMAINDERS.** The
remainders are exactly items 7–11 of the agenda (the D1 channel form,
the safety half, the pinning lever, P2) — none silent, each with an
owner and a consumer. Nothing in this record is a merge request; the
merge conversation starts at the check-in with the audit ask.
