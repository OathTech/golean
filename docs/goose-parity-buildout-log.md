# Goose-parity buildout — batch log

Charter: `docs/2026-08-07_goose-parity-charter.md`. One section per
landed batch: units, rungs reached per unit, R2/R3 skips with one-line
reasons, counts, gate status. Setup notes precede batch 1.

Upstream pins for every import in this buildout: goose @
`3be88bbb4982f58e5813b6f0344302d5582c8e8a`, perennial @
`43d4efabc22eb148eb239ebee89d1dd2ee54c900` (the scoping note's Part B
revs; `deps/goose` is READ-ONLY throughout).

## Setup (pre-batch)

- Parking ledger + this log created.
- Charter header gained the grossmith re-pin addendum (the charter's own
  instruction: re-pin at buildout launch).
- `scripts/import-goose` + `scripts/test-import-goose` (reject-shape
  fixtures per the lane-validation mold). FLAG for the checkpoint
  reviewer: the charter gates commits touching `scripts/` behind an
  audit checkpoint; the coordinator's launch instruction explicitly
  ordered this helper built as setup with the checkpoint after ~3
  batches, so the script commit is flagged here for that review rather
  than checkpointed in advance.
  **RESOLVED at the phase-A checkpoint (2026-08-08):** the review
  covered the setup helper commit (confirmed as a disclosed, bounded,
  note-severity process deviation whose retro-review was that
  checkpoint), and the coordinator ruled the `scripts/` changes of the
  checkpoint FIX ROUND (ci wiring of test-import-goose, the standing
  verbatim guard check-imported-goose, the zero-oracle fail-closed
  flag) likewise covered by the same checkpoint's review.
- `imported_goose` feature tag joins `Corpus/coverage/tags.tsv` in the
  SAME commit as the first cases carrying it (batch 1) — the ci
  dead-tags gate (`scripts/check-coverage`) rejects an unexercised tag,
  so it cannot land at setup time. (Part C: "features gain an
  `imported_goose` tag; no schema change".)
- Starting gate: `scripts/ci` PASS at a9ad607 (baseline 1205 cases,
  1107 pass / 98 fail, recorded at 968142a; a9ad607 is doc-only atop
  it).

---

## Batch 1 (2026-08-08) — semantics tree, scalar ops & control flow

Units (10, all imported self-contained, no sibling assembly needed;
upstream `testdata/examples/semantics/*.go` @ 3be88bb):

| unit | rows | R1 | notes |
|---|---|---|---|
| semantics/comparisons | 5 | 5 PASS | |
| semantics/operations | 11 | 7 PASS, 4 frontend-export | quarantine: call in short-circuit operand (`ok && f(...)` oracle style) |
| semantics/precedence | 4 | 4 PASS | |
| semantics/shortcircuiting | 4 | 0 PASS, 4 frontend-export | same quarantine class — the unit's whole point is side-effecting `&&`/`\|\|` operands |
| semantics/int-conversions | 5 | 5 PASS | |
| semantics/conversions | 1 | 1 PASS | |
| semantics/loops | 10 | 10 PASS | |
| semantics/switch | 4 | 4 PASS | |
| semantics/block | 1 | 1 PASS | + R2 pilot pin |
| semantics/vars | 3 | 3 PASS | |

Totals: 48 rows — 40 R1 PASS, 8 FAIL, every FAIL at stage
`frontend-export` in the ONE recorded fail-closed class
"call/allocation in short-circuit operand (would change evaluation
order)" (`tools/nativefrontend/emit.go` `emitGuarded`). NO new refusal
reason surfaced (the Part-B acceptance condition); no divergence, no
suspected GoLean bug.

Rungs:
- **R2**: pilot `proofs/GoLeanProofs/Specs/ImportedGooseBlock.lean`
  (semantics/block): ∀-streams `Terminates` via `allStreamsOk`
  `decide +kernel` + canonical-stream `.normal` readout `= 1`; builds
  in ~0.4 s under the 16 GiB kernel cap. R2 SKIPPED for the other 9
  units: pending the P1 parked decision (staleness-guard wiring for
  generated Program terms — docs/goose-parity-parked.md); the pilot
  proves the route.
- **R3**: skipped batch-wide — no existing automation discharges a
  GoSpec instance for an arbitrary imported program; per-oracle WP
  walks are new per-program proof effort (attempt-or-skip judgment).

Gate: full `scripts/ci --diff` green; baseline re-pinned same-commit
(1205 → 1253 ids; all 1205 pre-existing ids unchanged — zero drift).

## Batch 2 (2026-08-08) — semantics tree, functions / closures / allocation

Units (10, all self-contained; upstream `testdata/examples/semantics/*.go`
@ 3be88bb):

| unit | rows | R1 | notes |
|---|---|---|---|
| semantics/closures | 1 | 0 PASS, 1 frontend-export | short-circuit-operand quarantine (oracle style) |
| semantics/first-class-function | 1 | 1 PASS | |
| semantics/function-ordering | 2 | 2 PASS | BOTH are upstream `failing_test*` — programs goose's own translation gets wrong vs Go (the file's own "right-to-left … incorrect" comment, function_ordering.go:79-80, and the mechanized `failing_` convention, test_gen/main.go:134,166; goose.go:1901 citation corrected at the phase-A checkpoint — that is the sendStmt site F12 ruled misattributed); we match `go run`. Parity delta logged in the matrix. |
| semantics/multiple-assign | 3 | 2 PASS, 1 frontend-export | "map element as assignment target outside a single assignment" (emit.go:4558) |
| semantics/multiple-return | 4 | 4 PASS | |
| semantics/defer | 2 | 2 PASS | + R2 pins (both oracles) |
| semantics/new | 2 | 2 PASS | incl. Go 1.26 `new(expr)` (`new(3)`) |
| semantics/allocator | 2 | 2 PASS | map-iteration allocator |
| semantics/copy | 3 | 2 PASS, 1 frontend-export | "builtin copy in statement position" (emit.go:1601) |
| semantics/builtin | 2 | 2 PASS | min/max uint64 |

Totals: 22 rows — 19 R1 PASS, 3 FAIL, all stage `frontend-export`, all
in EXISTING `unsup(...)` fail-closed classes (cited above); the two
classes new to the BASELINE (copy-in-statement-position, map-element
multi-assign target) are existing frontend quarantine sites first
exercised by this corpus — not new refusal reasons. No divergence, no
suspected GoLean bug.

Rungs:
- **R2**: `proofs/GoLeanProofs/Specs/ImportedGooseDefer.lean` — both
  defer oracles: ∀-streams `Terminates` + canonical-stream readout `1`
  each (1.6 s build under the 16 GiB cap). Same P1 staleness caveat as
  the pilot. R2 skipped for the other 9 units (P1 pending; route
  demonstrated).
- **R3**: skipped batch-wide (same reason as batch 1).

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1253 → 1275 ids; zero drift on all 1253 prior ids).

## Batch 3 (2026-08-08) — semantics tree, data structures

Units (8; interfaces-complex needed sibling assembly of interfaces.go —
the one non-self-contained file so far; its 5 sibling-oracle skeleton
rows were trimmed to avoid duplicating the interfaces unit's rows,
bodies verbatim as always):

| unit | rows | R1 | notes |
|---|---|---|---|
| semantics/structs | 9 | 8 PASS, 1 frontend-export | struct-updates: short-circuit-operand quarantine |
| semantics/struct-pointers | 1 | 1 PASS | |
| semantics/maps | 2 | 1 PASS, 1 frontend-export | iterate-map: same quarantine |
| semantics/slices | 6 | 6 PASS | |
| semantics/nil | 6 | 6 PASS | + R2 pins (all 6 oracles) |
| semantics/type-equality | 3 | 0 PASS, 3 frontend-export | same quarantine |
| semantics/interfaces | 5 | 4 PASS, 1 frontend-export | binary-expr-interface: same quarantine |
| semantics/interfaces-complex | 11 | 11 PASS | assembled with interfaces.go |

Totals: 43 rows — 37 R1 PASS, 6 FAIL, all stage `frontend-export`,
ALL in the one call-in-short-circuit-operand quarantine class. No new
refusal reason, no divergence, no suspected GoLean bug.

Rungs:
- **R2**: `proofs/GoLeanProofs/Specs/ImportedGooseNil.lean` — all 6
  nil-comparison oracles (∀-streams `Terminates` + canonical readout
  each, 12 kernel theorems; generated by the `.tmp` mkpins helper,
  same P1 staleness caveat). OOM-convention note: under
  `ulimit -v 16777216` this module intermittently dies with "failed to
  create thread" (Lean's thread VA reservation, not memory pressure);
  measured uncapped it builds in 1.6 s at ~1.0 GiB max RSS — far under
  the 16 GiB intent. Recorded so the checkpoint can decide whether the
  convention should cap RSS instead of address space. Skipped for the other 7 units (P1
  pending; slices/interfaces programs also hit `allStreamsOk`'s
  fail-closed `appendSlice` arm where they append).
- **R3**: skipped batch-wide (same reason as batches 1-2).

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1275 → 1318 ids; zero drift on all 1275 prior ids).

## Phase-A checkpoint fix round (2026-08-08)

Checkpoint verdict: clean substantively (verbatim discipline 28/28
byte-verified by the reviewer, MUST-PARK held, zero divergences, zero
drift confirmed by independent baseline join) with confirmed minors,
all fixed here:

1. (minor) `scripts/test-import-goose` wired into `scripts/ci`
   (step 1c3, beside its declared mold), and a STANDING verbatim
   re-check guard added: `scripts/check-imported-goose` (check-golden
   mold, ci step 1c4) walks every landed imported-goose unit's
   above-marker region against `deps/goose` @ the pinned rev — byte
   drift, wrong-rev provenance, or a missing checkout all fail loud.
   Negative-fixtured both (tamper / wrong-rev / missing-checkout /
   zero-oracle fixtures; suite now 25 green).
2. (minor) zero-oracle landings are FAIL-CLOSED in import-goose; the
   explicit `--allow-no-oracles` opt-in exists for the unittest
   wrapper lane (recorded in the helper header; fixtured both ways).
3. (minor) the goose.go:1901 citation in matrix §6 and batch-2's log
   row re-anchored to the true support (function_ordering.go:79-80's
   own comment + the mechanized `failing_` convention,
   test_gen/main.go:134,166) — the old anchor was the sendStmt site
   the matrix's F12 record had already ruled misattributed.
4. (note) matrix §6 gained the two-sided claim-strength caveat on the
   9-pins-vs-37-test_fun_ok comparison (our readouts canonical-stream;
   their proofs termination-free partial correctness).
5. (note) §6 "Last-reviewed" stamp bumped (was stuck at batch 1).
6. (note) the setup-commit scripts-gating deviation: resolution
   recorded above (checkpoint-covered, including this fix round's
   scripts/ changes, per coordinator ruling).

Refuted (no action): the ulimit-note-belongs-in-ledger claim.

## Batch 4 (2026-08-08) — channel tree (the 7 concurrency-clean files)

Zero upstream boolean oracles in this tree: every subject is an
authored wrapper below the marker (`--allow-no-oracles` lane, first
use). Lane assignment per row (MAY-DECIDE), whys recorded in cases.tsv:

| unit | rows | R1 | lanes | notes |
|---|---|---|---|---|
| channel/actris-example | 1 | 1 PASS | confluent | DSPExample = 42 (rendezvous handoff); certified 36 leaves |
| channel/google-search | 1 | 1 PASS | membership | arrival-order code, certified members=6 (all 3! orders), 4/6 exhibited by go-run samples; work=40000000 (~10× prior corpus max; ~2-4 min recurring per full run — FLAG for next checkpoint) |
| channel/muxer | 2 | 2 PASS | confluent | async + client; client-old/make-greeting rows PARKED (P2) |
| channel/muxer-unverified | 2 | 2 PASS | strict | single-threaded select paths (drained/done); assembled with muxer.go |
| channel/select-tricky-examples | 3 | 3 PASS | 1 confluent + 2 strict | their wp-proved trio incl. the no-2-NB-rendezvous shape and the guaranteed-ready closed-recv |
| channel/fibonacci | — | — | — | PARKED whole unit (P2: append-spill × schedule tree >20M) |
| channel/higher-order | — | — | — | PARKED whole unit (P2: >8M at sites=96) |

Totals: 5 units landed, 9 rows, 9 R1 PASS (5 confluent-certified,
1 membership-certified, 3 strict); 2 units + 2 rows parked (P2). The
red-first loop here was the enumerator's own author-assertion checks
(width refuted mechanically at fibonacci's spill bound; sites bounds
raised until measured) — every failure was a loud bound refutation,
never a silent truncation. Parity note: this covers goose's verified
channel-example surface for actris_example (wp_DSPExample), the
select-tricky trio (incl. their proved-unreachable-default example),
and muxer's Async/Client (wp lemmas in their channel examples); their
Google example is UNVERIFIED upstream while ours ships with a
machine-certified 6-member observation set.

Rungs: R2/R3 skipped batch-wide — concurrent programs are outside the
sequential `allStreamsOk` checker (R2), and GoSpecC's spawning form is
the recorded T7 successor debt (R3).

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1318 → 1327 ids; zero drift on all 1318 prior ids).

## Batch 5 (2026-08-08) — storage-clean + generics

All wrapper-authored (`--allow-no-oracles`); whys in the wrappers'
comments. Units:

| unit | rows | R1 | notes |
|---|---|---|---|
| storage/comments | 1 | 1 PASS | 0consts.go + 1doc.go assembled (one upstream package) |
| storage/interfacerecursion | 1 | 1 PASS | goose REJECTS this package ("// ERROR cycle in dependencies"); valid Go — parity delta. Methods deliberately uncalled (divergent by construction); observable = lowering + interface assignment |
| storage/mapliteral | 1 | 1 PASS | + R2 pin (readout 21) |
| storage/mutualrec | 1 | 1 PASS | goose REJECTS ("cycle"); valid Go — parity delta. Function values taken, not called |
| generics/constraints | 1 | 1 PASS | `~[]int` underlying constraint + generic Clone (append+spread) |
| generics/helpers | 1 | 1 PASS | AnyPointer[T any] |
| generics/generic-conversion | 1 | 0 PASS, 1 frontend-export | short-circuit-operand quarantine (assert's `&&`). NOTE: the upstream `genericConversions()` PANICS in real Go ("index out of range [0] with length 0" — `&(nilConvert[[]int]()[0][0])` indexes a nil slice); their unittest tree never RUNS it (translation-only), so the row is classified expected_status=panic — a latent upstream bug surfaced by executing their corpus |

Totals: 7 units, 7 rows — 6 R1 PASS, 1 frontend-export (recorded
class). Parity deltas: two whole packages goose rejects as
untranslatable cycles (interfacerecursion, mutualrec) run green here;
their generic_conversion example is latently panicking Go.

Rungs: R2 = storage/mapliteral (Terminates + readout 21; 0.6 s,
~0.7 GiB RSS). R2 skipped elsewhere (P1 pending; constraints hits the
`allStreamsOk` fail-closed appendSlice arm). R3 skipped batch-wide.

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1327 → 1334 ids; zero drift on all 1327 prior ids).
