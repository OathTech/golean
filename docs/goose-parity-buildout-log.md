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
| channel/google-search | 1 | 1 PASS | membership | arrival-order code, certified members=6 (all 3! orders), 4/6 exhibited by go-run samples; work=40000000 (magnitude corrected at the phase-C fix round: ~2.7× the prior corpus max work param — worker-pool/sum's 15M, not "10× sb-chan's 4M" — and ~1.3× the prior heaviest wall time, ~84 s vs ~65 s; recurring-cost FLAG stands) |
| channel/muxer | 2 | 2 PASS | confluent | async + client; client-old/make-greeting rows PARKED (P2) |
| channel/muxer-unverified | 2 | 2 PASS | strict | single-threaded select paths (drained/done); assembled with muxer.go |
| channel/select-tricky-examples | 3 | 3 PASS | 1 confluent + 2 strict | their wp-proved trio incl. the no-2-NB-rendezvous shape and the guaranteed-ready closed-recv |
| channel/fibonacci | — | — | — | PARKED whole unit (P2: append-spill × schedule tree >20M) |
| channel/higher-order | — | — | — | PARKED whole unit (P2: >8M at sites=96) |

Totals: 5 units landed, 9 rows, 9 R1 PASS (4 confluent-certified,
1 membership-certified, 4 strict — split corrected at the phase-C fix
round; the first version said 5/1/3, contradicting the table above);
2 units + 2 rows parked (P2). The
red-first loop here was the enumerator's own author-assertion checks
(width refuted mechanically at fibonacci's spill bound; sites bounds
raised until measured) — every failure was a loud bound refutation,
never a silent truncation. Parity note (corrected at the phase-C fix
round — "their Google example is UNVERIFIED upstream" was FALSE): this
covers goose's verified channel-example surface for actris_example
(wp_DSPExample), the select-tricky trio (incl. their
proved-unreachable-default example), and muxer's Async/Client; for
Google the honest delta is METHOD, not coverage — upstream proves
`wp_Google` (channel_google.v, Qed, 0 Admitted, permutation
postcondition `xs ≡ₚ google_expected q`) on the byte-identical
program, while ours adds machine-certified reachability of all 6
arrival orders + the executable differential.

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
| storage/interfacerecursion | 1 | 1 PASS | valid coverage of interface-recursion lowering; NOT a parity delta (corrected at the phase-C fix round: at the pinned rev this is a POSITIVE gold-translated goose example — the "// ERROR cycle" comment is vestigial, TestExamples passes it). Methods deliberately uncalled (divergent by construction); observable = lowering + interface assignment |
| storage/mapliteral | 1 | 1 PASS | + R2 pin (readout 21) |
| storage/mutualrec | 1 | 1 PASS | valid coverage of mutual-recursion lowering; NOT a parity delta (same correction: POSITIVE gold-translated goose example, vestigial ERROR comment). Function values taken, not called |
| generics/constraints | 1 | 1 PASS | `~[]int` underlying constraint + generic Clone (append+spread) |
| generics/helpers | 1 | 1 PASS | AnyPointer[T any] |
| generics/generic-conversion | 1 | 0 PASS, 1 frontend-export | short-circuit-operand quarantine (assert's `&&`). NOTE: the upstream `genericConversions()` PANICS in real Go ("index out of range [0] with length 0" — `&(nilConvert[[]int]()[0][0])` indexes a nil slice); their unittest tree never RUNS it (translation-only), so the row is classified expected_status=panic — a latent upstream bug surfaced by executing their corpus |

Totals: 7 units, 7 rows — 6 R1 PASS, 1 frontend-export (recorded
class). Parity delta (corrected at the phase-C fix round: the claimed
interfacerecursion/mutualrec delta was FALSE — both are POSITIVE
gold-translated goose examples at the pinned rev; the units stand as
ordinary valid coverage): their generic_conversion example is
latently panicking Go — that delta stands.

Rungs: R2 = storage/mapliteral (Terminates + readout 21; 0.6 s,
~0.7 GiB RSS). R2 skipped elsewhere (P1 pending; constraints hits the
`allStreamsOk` fail-closed appendSlice arm). R3 skipped batch-wide.

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1327 → 1334 ids; zero drift on all 1327 prior ids).

## Batch 6 (2026-08-08) — unittest wrapper lane, first slice

11 small unittest-tree files (translation-golden upstream: NO oracles
by construction; every subject an authored checksum wrapper per the
scoping's B.3 oracle-mapping shape; `--allow-no-oracles` lane):

| unit | rows | R1 | notes |
|---|---|---|---|
| unittest/empty-functions | 1 | 1 PASS | empty/void/unnamed/anonymous params |
| unittest/returns | 1 | 1 PASS | every named-return shape, length checksum |
| unittest/reassign | 1 | 1 PASS | |
| unittest/vars | 1 | 1 PASS | local var/const blocks |
| unittest/ints | 1 | 1 PASS | defined-type chains (my_u32/also_u32) |
| unittest/trailing-call | 1 | 1 PASS | |
| unittest/type-alias | 1 | 1 PASS | alias vs defined-type conversions |
| unittest/enum | 1 | 1 PASS | both iota blocks, multi-name const lines |
| unittest/const | 1 | 1 PASS | full const-arithmetic surface + R2 pin |
| unittest/literals | 1 | 1 PASS | incl. a struct FIELD named `int` and unkeyed literals |
| unittest/operators | 1 | 1 PASS | incl. `&^` and `&^=` |

Totals: 11 units, 11 rows, 11/11 R1 PASS — zero frontend REFUSALS in
this slice. **Corrected at the phase-C fix round (2026-08-08): "zero
frontend refusals" was true but concealed a COMPLIANCE LAPSE.** The
const wrapper's `sum := int(useUntypedInt())` triggers a real frontend
wrong-answer class (conversion-of-call double emission, now
docs/BUGS.md BUG-047) that ran GREEN only because the callee is pure
— and it went unparked at batch time, against the charter's MUST-PARK
for suspected GoLean bugs. The phase-B checkpoint review caught it,
not the batch discipline; the miss's root cause was inspecting only
FAILs. Filed as BUG-047 (with the six-shape repro matrix), red-first
pinned by `assign-order/conversion-call-eval-once/{define,assign}`,
triaged in ledger P3; the const R2 pin and the copy/const cases carry
true-of-term / green-by-luck annotations. Remaining unittest files
needing MORE than mechanical wrapper authorship are untouched (next
slices or park per charter).

Rungs: R2 = unittest/const (Terminates + readout 2139, the
differentially-agreed checksum; 0.6 s / ~0.7 GiB RSS). R2 skipped
elsewhere (P1 pending). R3 skipped batch-wide.

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1334 → 1345 ids; zero drift on all 1334 prior ids).

## Phase-B checkpoint fix round (2026-08-08, opening phase C)

Checkpoint verdict: three MAJORS + two minors confirmed, one refuted.
All fixed here; the two majors' substance:

1. (major, M1) **BUG-047 filed** — conversion-of-call double emission
   (pre-existing frontend defect surfaced by batch 6's const wrapper;
   verifier's six-shape matrix in the BUGS.md entry; root cause
   emit.go:2112). Red-first pinned by the fresh canonical case
   `assign-order/conversion-call-eval-once/{define,assign}` (both
   FAIL/differential, Lean 202 vs Go 101 — joins the baseline as the
   bug's mechanical pin). NOT fixed (charter forbids frontend changes;
   maintenance round). Landed-corpus sweep: the only in-corpus
   instances are semantics/copy (green by idempotence) and
   unittest/const (green by purity) — both annotated, plus the
   ImportedGooseConst pin docstring (true-of-term). Additional
   controls recorded: `return T(f())`, `var x T = T(f())`, and
   `len(f())` shapes are unaffected. The COMPLIANCE LAPSE (unparked at
   batch time) is recorded in the batch-6 section and ledger P3 —
   honestly, not cleaned.
2. (major, M2) the "goose REJECTS interfacerecursion/mutualrec" parity
   claim was FALSE (both are positive gold-translated examples; the
   ERROR comments are vestigial — verified against examples_test.go
   and the gold files directly). Struck/re-characterized in all four
   locations (matrix §6, batch-5 log ×2, both wrapper comments).
3. (major, M3) "their Google example is UNVERIFIED upstream" was FALSE
   — `wp_Google` is Qed with 0 Admitted at the pinned perennial rev
   (verified directly). Restated as a METHOD delta (their partial-
   correctness permutation triple vs our certified 6-member
   reachability + differential) in matrix §6 and the batch-4 log.
4. (minor) batch-4 lane totals corrected to 4 confluent / 1
   membership / 4 strict (re-verified directly from cases.tsv lane
   columns — the flagged verifier's evidence held).
5. (minor) the work=40000000 magnitude framing corrected in the log
   and P2 (~2.7× worker-pool/sum's 15M, ~1.3× its wall time — not
   "10× sb-chan's 4M").

Refuted (no action): the P2 wrappers-remain understatement claim.

## Batch 7 (2026-08-08) — panic pair + unittest small files

11 units, 12 rows (unittest/copy carries its 2 upstream `test*` bool
oracles; everything else wrapper-authored):

| unit | rows | R1 | notes |
|---|---|---|---|
| semantics/panic | 1 | 1 PASS | shouldPanic → expected_status=panic "bad" |
| unittest/panic | 1 | 1 PASS | PanicAtTheDisco → panic "disco" |
| unittest/rune | 1 | 1 PASS | + R2 pin (readout 98) |
| unittest/higher-order | 1 | 1 PASS | closure passed as func-typed arg mutates a local |
| unittest/copy | 2 | 1 PASS, 1 frontend-export | copy-simple: builtin-copy-in-statement-position (recorded class); copy-different-lengths green with a BUG-047 idempotence annotation |
| unittest/multiple | 1 | 1 PASS | multi-value pass-through calls |
| unittest/repeat-vars | 1 | 1 PASS | block-scoped redeclaration + panic-on-failure body |
| unittest/recursive | 1 | 1 PASS | divergent recursions taken as values; the mutually-embedded type cycle lowers |
| unittest/float | 1 | 1 PASS | float consts + int/float comparisons |
| unittest/topsort | 1 | 1 PASS | type-order test (0 upstream funcs); wrapper constructs the pair |
| unittest/strings | 1 | 1 PASS | |

Totals: 12 rows — 11 R1 PASS, 1 frontend-export (recorded class). One
new BUG-047 green-by-idempotence instance found and annotated at
import time (unittest/copy — the class watch from the fix round).

Rungs: R2 = unittest/rune (Terminates + readout 98; 0.4 s). R3
skipped batch-wide.

Gate: full `scripts/ci --diff`; baseline re-pinned same-commit
(1347 → 1359 ids; zero drift on all 1347 prior ids).

## Batch 8 (2026-08-08) — unittest wrapper lane, second slice (+ BUG-048)

9 units, 13 imported rows (conversions carries 2 upstream bool oracles
+ a wrapper row; embedded 3 rows), plus the 2-row canonical BUG-048
pin case:

| unit | rows | R1 | notes |
|---|---|---|---|
| unittest/array | 1 | 1 PASS | keyed array literal ([...] with const keys), [100] param, elem refs |
| unittest/slices | 1 | 1 PASS | slice alias type, &elem through method |
| unittest/nil | 1 | 1 PASS | |
| unittest/control-flow | 1 | 1 PASS | incl. else-if init-statement chains with shadowing |
| unittest/loops | 1 | 1 PASS | FOUR upstream loop demos DIVERGE by construction (ImplicitLoopContinue{,2}, nestedConditionalInLoopImplicitContinue, nestedLoops) — taken as values only, wrapper comment records it. First authoring attempt CALLED them: the Go-side case binary ran unbounded and SURVIVED the harness's go-run timeout kill (orphaned child; killed by hand) — harness-robustness observation, no scripts change |
| unittest/switch | 1 | 1 PASS | |
| unittest/conversions | 3 | 3 PASS | incl. the map[any]any/any-key oracle |
| unittest/globals | 1 | 1 PASS | effectful global initializers + two init() funcs |
| unittest/embedded | 3 | 2 PASS + 1 red BUG-048 pin | TWO latent upstream panic paths pinned green-as-panic (useEmbeddedField writes through a fresh zero &embedD{}'s nil *embedB for ANY argument; useEmbeddedValField same via returnEmbedValWithPointer) — their translation-only tests never run either. The `live` row is the in-corpus BUG-048 pin (stays red) |

**BUG-048 filed** (docs/BUGS.md; ledger P4): the machine wrong-STUCKS
calling a VALUE-receiver method through a pointer-typed VARIABLE
(`p := &x; p.get()` — Go auto-derefs). Surfaced by embedded.go's
`d.embedB.Foo()`; minimized by an 8-shape probe matrix (notable: the
PROMOTED-through-embedding path via a pointer variable works; the
direct call does not). Canonical red-first pin
`methods/value-receiver-via-pointer-var/{addr-of-var,addr-of-literal}`
(FAIL/lean-observation) + the imported `embedded/live` row — all three
in BUG-048's Cases. An unexercised-path find: the methods lane never
covered this exact cell. NOT fixed (charter).

Totals: 13 imported rows — 12 PASS, 1 deliberate red (BUG-048 pin);
+2 canonical deliberate reds (BUG-048 pins). Two new latent upstream
panics pinned. R2/R3 skipped batch-wide (P1 pending; batch prioritized
the bug triage).

Gate: batches 8 and 9 land in ONE commit with ONE full
`scripts/ci --diff` + same-commit re-pin (1359 → 1381 ids; zero drift
on all 1359 prior ids; check-bugs green with BUG-048's three pins).
Reason, recorded: the batch-8 gate run went PARTIAL (1374/1381)
because batch 9's imports landed in the tree mid-run — the corpus
manifest is a filesystem walk, so the final baseline-diff saw 7 ids
the run predated. Rather than re-run two full gates, the two batches'
final state takes one full gate (batch composition is the worker's
call; the discipline's substance — full run, zero drift, same-commit
re-pin — holds for the union). Process lesson for the retrospective:
import nothing while a full gate is in flight.

## Batch 9 (2026-08-08) — unittest wrapper lane, final slice

7 units, 7 rows (all wrapper-authored):

| unit | rows | R1 | notes |
|---|---|---|---|
| unittest/varargs | 1 | 1 PASS | incl. variadic pass-through of a multi-value call |
| unittest/struct-method | 1 | 1 PASS | method on literal receiver, blank receiver |
| unittest/comments | 1 | 1 PASS | Coq-comment-hostile doc comments |
| unittest/type-switch | 1 | 1 PASS | incl. the init-statement fancy type switch with nil case |
| unittest/interfaces | 1 | 0 PASS, 1 frontend-export | recorded class "implicit interface conversion in multi-value assignment (interfaces campaign, deferred)" (emit.go:2039/2266) — testMultiReturn's `*x, y = returnConcrete()` |
| unittest/struct-pointers | 1 | 1 PASS | wrapper avoids the BUG-048 shape (`s.readBVal()` via pointer var) — noted in the wrapper comment; the class stays pinned by its canonical case |
| unittest/replicated-disk | 1 | 1 PASS | the dummy-disk replicated read/write/recover (1000-iteration recover loop runs green) |

Totals: 7 rows — 6 PASS, 1 frontend-export (recorded class). R2/R3
skipped batch-wide (P1 pending).

## Check-in response round (2026-08-08; user rulings, coordinator-relayed)

Per-item disposition:
1. **P1 ruling implemented**: `scripts/check-imported-pins` (check-golden
   mold; fresh decoded(frontend(source)) diffed directly against each R2
   pin's term) — ci step 1c5, fixtured (real-pin pass + tampered-copy
   drift reject). Ledger P1 closed.
2. **P2 closed as ruled-parked** (units stay parked; measurements stand
   as the POR backlog's motivating cases).
3. **BUG-047 FIXED** (assign-site speculative-emit guard extended to
   conversions): drift = exactly the two pin flips; constLowered
   regenerated — the DRIFT WAS CAUGHT BY THE NEW STALENESS GUARD, the
   designed sequence; green-by-luck annotations removed.
   **BUG-048 FIXED** (frontend value-receiver auto-deref through
   pointer operands, mirroring the promoted arm — no machine change):
   drift = exactly five flips — the three pins PLUS two pre-existing
   tracked-untriaged backlog reds of the same class (untriaged ratchet
   18 → 16). Record correction: BUG-048's "unexercised cell" claim was
   wrong — the class sat pinned in the tracked untriaged backlog.
   Both fixes: own commits, own full `ci --diff`, same-commit re-pins,
   zero drift beyond the explained flips, designated statements
   byte-identical.
   Process slip, recorded: the BUG-047 gate was first invalidated by
   editing emit.go (the 048 fix) mid-run — the exact batch-8 lesson;
   killed, sequenced properly (048 stashed, 047 gated+committed clean,
   048 re-applied and gated). Two orphaned harness binaries from the
   killed run cleaned by hand.
4. **Tiered checking implemented** (user directive; design:
   membership-lane note 2026-08-08 addendum + nondet-doctrine caption):
   `tier=slow` lane param (membership-only, manifest+harness validated,
   fixtured), tracked certified-set records under `baselines/certified/`
   (wire-sha staleness-guarded), quick runs report visible
   CERTIFIED-CACHED (~10 s vs ~2-4 min for google-search, the first
   tier member) with samples + driver-coupling still checked against
   the recorded set, `scripts/ci --slow` re-certifies fully and fails
   loud on any set/hash movement (verified live both directions:
   missing-record and stale-sha refuse; slow re-certification matches).
   Full quick-mode `ci --diff`: PASS, 1381/1381, zero drift.
5. **OOM convention**: kept; RSS-fallback note added to
   docs/agent-sandbox.md per the ruling.
