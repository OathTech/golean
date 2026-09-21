# Evidence — Stage E of the evaluation-order model v2.1: family migration (lane `core/unseq-stage-e-0921`, 2026-09-21)

[AGENT] worker. Design record `docs/2026-09-21_unseq-stage-e-design.md` (per family), handoff
`docs/2026-09-21_unseq-stage-e-handoff.md`. Small tables and gate tails only (caps 256 KiB / 4 MiB —
`scripts/check-evidence-size`); bulk runs are reproduced by the commands named per file. Every gate is
`scripts/capped scripts/ci …` under the box-wide lock; captured exits; a killed or timed-out command
decided nothing.

## E1 — package-level variables as occurrences (closes BUG-113)

| file | what | producer |
|---|---|---|
| `census-e1.txt` | the whole-sweep census BEFORE (main `74d084ad`'s frontend, built from `git archive`) and AFTER (the E1 frontend) over the 1356 corpus packages + the raft twin assembly: 107 943 sweeps; admitted 136 → 146 (+10 in 4 packages, 0 lost); the twin 10 203 sweeps, 0 admitted on both; the per-package table, the newly admitted sweeps by former reason and form, the still-legacy package-level TYPE reasons | `.tmp/census/run.sh <frontend> <out.tsv>` (`nativefrontend --unseq-census --dir <pkg>` over every `Corpus/coverage/exec/**/cases.tsv` directory and the twin assembled as `scripts/check-frontend-pins` assembles it), `summarize.py`, `diff.py` |
| `census-newly-admitted-e1.tsv` | the 10 sweeps that enter the grammar at E1 (package, unit, file:line, function, form, counts, the reason the BEFORE census printed) | `diff.py` |
| `diff-one-e1.txt` | the focused differential on all 13 affected rows (the 3 BUG-113 rows, the 4 born `evalorder/unseq-globals` rows, `spec-examples-decl/select-forms` ×3, `panic-recover/repanic-collapse/index-two-faults`, `init/stdlib-initializer-dependent`) on the E1 frontend + the E1 binary: the two flips, the four births, everything else unchanged (the init row's pre-existing frontend-export red) | `scripts/diff-one <ids…>` (the per-row `wide=` / `enumerated=` details are in `artifacts/coverage/latest.tsv` of that run and quoted in the design note §E1) |
| `choice-trace-main-vs-e1.txt` | the whole-corpus choice trace, main vs E1 (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 5` per side from export trees + `trace-compare.py` |
| `ci-slow-e1.tail.txt` | the full gate's tail (the paragraph below) | `scripts/capped scripts/ci --slow`, ANSI stripped: the step / verdict / drift lines + the 5a-class row's detail |
| `gc-draws-e1.txt` | gc's draws for `evalorder/unseq-globals` (all four subjects) and `evalorder/legacy-logical-vs-call` (all three): 5 runs × GOMAXPROCS 1 / 8 × default / `-gcflags=all='-N -l'` = 20 per package, every draw inside the derived sets (2 · 11 · `wit 1` 2 · `wit 1` 2; `logical false 0` · `logical false 0` · `logical 0 true`) | `GOMAXPROCS=… go run [-gcflags=all='-N -l'] Corpus/coverage/exec/<pkg>/main.go`, go1.26.5 |

Reference sets: `docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py` E1a/E1c/E1b (regenerated
`outcomes.txt`, `RESULT: PASS`); over the wire: `Tests/UnseqWire.lean` (65 ok; 20 mutants refused by
name — `mut-deref-hidden` new), `scripts/check-unseq-wire` PASS (63 fixtures byte-identical to the
generator; 20 mutants through the CLI), `scripts/check-wire-boundary` PASS (11 byte-level + 11
unseq-node controls — the global-read positive control and the hidden-read refusal new). Frontend:
`go test ./tools/nativefrontend/...` ok (E1 witnesses admitted with their counts; `globalTypeOut`
refused by name), `go test ./tools/lowerdiag/...` ok. Explicit-target Lean builds under the lock rule:
`GOLEAN_MEM_MAX=32G scripts/capped lake build GoLean.NativeToIR golean UnseqWireTests` EXIT=0 (99
jobs).

**The full gate: `scripts/capped scripts/ci --slow` at the E1 tree** (main `14006270` + the E1 edits, the
worktree dirty with exactly them; the box-wide lock acquired 02:10:26Z after merge train r45's `ci --diff`
released it, released 02:28:29Z): **EXIT=1 in 1083 s, K=80 (`membership_draws 80`); 3709 rows 3464 PASS /
245 FAIL in the run = the pinned 3465 / 244 with the one 5a-class row red; RESULT FAIL on EXACTLY the two
5a-class items** — `certificate provenance` («STALE certification: changed dependency
build/files/GoLean/NativeToIR.lean» — the `deref` head) and the `baseline diff` DRIFT block's ONE line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the same item — the
row's detail in the run: «certification: STALE certification: changed dependency build/files/GoLean/NativeToIR.lean\nFresh certification: unchanged set; seconds=169.697; candidate=/home/dev/projects/golean/.claude/worktrees/unseq-stage-e/artifacts/coverage/membership/imported-goose/channel/google-search/certification-candida»; the train installs the fresh candidate at step 5a, not a re-pin here).
Every other step ok: core build, escape-hatch scans, core totality audit (45 modules, 51 required theorems,
classical trio only — its compiled poison controls fire as designed), engine isolation, check-mem-callsites,
admission proofs, declaration + wire boundaries (11 + 11 unseq-node controls), method identity, unseq
scheduler (Stage B), unseq wire (Stage C + E1: 20 mutants), frontend pins (twin wire = pinned bytes),
frontend / lowerdiag / harness unit tests, eval tests 274 ok, differential run, lane-validation fixtures incl.
the go half, negative corpus 394 matched, FloatVectors + inittask-std byte-exact, re-pin guard 0
PASS→non-PASS, executed library coverage. `ci-slow-e1.tail.txt` is the tail (step lines, the provenance
verdict, the drift block, the row's detail). The seven rows of this family reproduce their pinned states in
the run: `or-vs-call` / `and-vs-call` PASS strict, `call-first-control` PASS, `unseq-globals/read-vs-call` and
`compound-vs-call` PASS/membership, `read-vs-unrelated-call` and `plain-target-call` PASS strict.

**Whole-corpus choice trace, main vs E1** (`choice-trace-main-vs-e1.txt`; run after the E1 commit from export trees —
main `14006270` and the E1 commit `0fe7bdce`, each with `deps/`; `scripts/choice-trace-corpus --dump --jobs 5`, the
two standing exclusions; Stage D's `trace-compare.py` per row): **3673 ids, 3664 byte-identical, 5 DIFFER, 4 only on
the E1 side** — the 5 are EXACTLY the E1-admitted rows (`evalorder/legacy-logical-vs-call/{or-vs-call,and-vs-call,
call-first-control}`, `spec-examples-decl/select-forms/{ready,default}`), the 4 the born `evalorder/unseq-globals`
rows; `index-two-faults`' new sweep is data-forced (its read is `idx`'s argument — no wide pick, no record) and the
init row refuses on both sides. Site census: `unseqNext` 555 → 616, every other site's count identical. The
tracer exits 1 on BOTH sides for the summarizer's standing findings (187 baseline-red ids refusing under some
stream; the over-budget export refusal) — 0 menu-invariant violations, 0 self-check alarms, 0 driver-agreement
mismatches on each side.

## E2 — pointers, fields and maps as occurrences (closes BUG-104's map-key-beside-a-call row)

| file | what | producer |
|---|---|---|
| `census-e2.txt` | the census AFTER E1 (the E1 frontend) vs AFTER E2 (the E2 frontend): admitted 146 → 176 (+27 from the widening in 17 packages, 0 lost; +3 from the E1 package born after the E1 census; 107 943 → 107 963 sweeps); the twin 10 203 / 0 on both; the per-package table, former reasons, forms | `.tmp/census/run.sh`, `summarize.py`, `diff.py` (tolerating the born package's rows) |
| `census-newly-admitted-e2.tsv` | the 27 sweeps that enter at E2 | `diff.py` |
| `diff-one-e2.txt` | the focused differential on the 38 affected rows on the E2 frontend + binary: the 1 flip, the 5 lane moves, the 8 births, the 4 E13 deref/map sets unchanged at 2 members, everything else unchanged; the one width/sites correction on `len-nil-only-none` and its re-run | `scripts/diff-one <ids…>` (the per-row details are in the run's `artifacts/coverage/latest.tsv` and quoted in the file) |
| `choice-trace-main-vs-e2.txt` | the whole-corpus choice trace, main vs E2 | the same method |
| `ci-slow-e2.tail.txt` | the E2 full gate's tail (the paragraph below) | `scripts/capped scripts/ci --slow`, ANSI stripped |
| `gc-draws-e2.txt` | gc's draws for the born package (all eight subjects) and the six moved/flipped subjects (`derefVsCall`, `mapCompoundCallMutates`, `mapCompoundCallDeletes`, `derefTargetRhsCallOrder`, `lenNilOnly(0)`, `mapCompoundIndexKeyVsCall` under a recovering driver): 5 × GOMAXPROCS 1/8 × default / `-N -l` = 20 per subject, every draw inside its derived set | `GOMAXPROCS=… go run [-gcflags=all='-N -l'] .` on a driver copy per row (`.tmp/gc-e2/`), go1.26.5 |

References: `enumerate.py` E2a/E2c/E2d/E2e/E2f/E2g (regenerated `outcomes.txt`, `RESULT: PASS`); over the wire:
`Tests/UnseqWire.lean` 72 ok, 22 mutants refused by name (`mut-map-target-key`, `mut-deref-target-nonatom` new);
`scripts/check-unseq-wire` PASS (70 fixtures byte-identical; 22 mutants through the CLI); `scripts/check-wire-
boundary` PASS (11 + 14 unseq-node controls — the map-plan positive and the two mutants new). Machine:
`Tests/UnseqScheduler.lean` 70 ok — the Stage B «frozen map-element plan (Stage E)» REFUSAL test flipped to the
set test «map replacement (frozen map VALUE)»: {`old 11 m 100`, `old 10 m 101`} exact; `scripts/check-unseq-
scheduler` PASS (35 theorems, classical trio only); `scripts/check-mem-callsites` PASS (70 rows, inventory
unchanged — the map arm reads through the emitting `mapLookupValue`). Frontend: `go test ./tools/nativefrontend/
./tools/lowerdiag/` ok (the E13 guard test's two map-target shapes moved to the graph's truth: one graph, no
probe). Lean build (explicit targets): `GOLEAN_MEM_MAX=32G scripts/capped lake build golean UnseqWireTests
UnseqSchedulerTests` EXIT=0 (102 jobs, 119 s).

**The full gate: `scripts/capped scripts/ci --slow` at the E2 tree** (main `14006270` + E1 `0fe7bdce` + the E2
edits; the box-wide lock 02:45:52–03:02:50Z): **EXIT=1 in 1018 s, K=80 (`membership_draws 80`); 3717 rows 3473
PASS / 244 FAIL in the run = the pinned 3474 / 243 with the one 5a-class row red; RESULT FAIL on EXACTLY the two
5a-class items** — `certificate provenance` («STALE certification: changed dependency
build/files/GoLean/GoCore/Machine.lean» — the map-element read arm) and the `baseline diff` DRIFT block's ONE line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the row's detail: STALE
for `Machine.lean`; «Fresh certification: unchanged set; seconds=169.317» — the train installs the candidate at 5a).
Every other step ok (core build warning-free, totality audit, engine isolation, check-mem-callsites, admission
proofs, declaration + wire boundaries (11 + 14 unseq-node controls), method identity, unseq scheduler (Stage B +
the map-replacement set), unseq wire (22 mutants), frontend pins (twin = pinned bytes), frontend / lowerdiag /
harness unit tests, eval tests 274 ok, differential run, lane-validation fixtures incl. the go half, negative
corpus 394 matched, FloatVectors + inittask-std byte-exact, re-pin guard 0 PASS→non-PASS, executed library
coverage). `ci-slow-e2.tail.txt` is the tail. Every row of this family reproduces its pinned state in the run:
the flip `map-compound-index-key-vs-call` PASS/membership, the five moves PASS/membership, the eight births in
their lanes.

**Whole-corpus choice trace, main vs E2** (`choice-trace-main-vs-e2.txt`; the E2 side = this worktree at the E2 commit
`6960697f`, the E2 binary `7920d88e…`): **3681 ids, 3644 byte-identical, 25 DIFFER, 12 only on the E2 side** — the 25 are
EXACTLY the rows whose sweeps E1 or E2 admitted (the E1 five; the four E13 deref/map rows and BUG-104's map row; the six
`len-vs-call-order` rows; `maps/compound-assign-eval-once`; `noodler/evalorder/{elided-pointer-literal,map-index-before-
rhs}`; `noodler/latitude/deref-vs-call`; `noodler/maps/compound-call-{deletes,mutates}`; `noodler/methods/method-
expressions`; `pointers/deref-target-rhs-call-order`; `spec-examples-decl/conversion-parse-forms`), the 12 the born E1 +
E2 rows; every other id byte-identical. Site census: `unseqNext` 555 → 925, `unseqPanic` 288 → 246 (the E2 rows that
left the legacy probe), every other site identical. The same standing exit-1 findings on both sides.

## E3 — receives and method calls as occurrences; the observability trigger (closes BUG-104)

| file | what | producer |
|---|---|---|
| `census-e3.txt` | the census AFTER E2 (the E2 frontend) vs AFTER E3 (the E3 frontend, the tree at the E3 commit): admitted 176 → 110 = 176 + 18 (11 receives with a read unordered against them, 7 concrete method calls) − 94 (RETURNED to the legacy path by the observability trigger — every edge forced) + 6 (the E2 package born after the E2 census) + 4 (the born E3 package; `recv-after-call` all-forced = legacy, the control); 107 963 → 108 045 sweeps; the twin 10 203 / 0 on both; the per-package table, forms, the lost sweeps per package | `.tmp/census/run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e3.tsv` | the 18 sweeps that enter at E3 (function, form, former reason) | `diff.py` |
| `census-lost-e3.tsv` | the 94 sweeps that return to the legacy path (the fmt shim helpers ×44, the imported-goose `ok = ok && …` chains ×28, `slices/slice-elided-high-eval-once` ×5, …) | `diff.py` |
| `diff-one-e3.txt` | the focused differential on the 164 affected rows on the E3 frontend + binary, both runs: the first surfaced the decoder's missing `ref` argument arm (the five born rows refused «hidden read in an argument») and the two lane budgets REFUSED by name (`nil-receiver-recursion`: 6 wide picks after the fixed streams, w=16; `two-workers-own-chans`: the DFS work cap); the second (after the decoder arm and the two lane/engine moves) is the 164-row table — 145 PASS / 19 pre-existing frontend-export FAIL | `scripts/diff-one <ids…>` |
| `gc-draws-e3.txt` | gc's draws for the born package (all five subjects), BUG-104's three flipped subjects (under a recovering driver), `receiverVsArgCall`, and the two moved subjects (`nilReceiverRecursion` 10, `forkJoinTwoWorkersOwnChans` 34): 5 × GOMAXPROCS 1/8 × default / `-N -l` = 20 per subject, every draw inside its derived set | `GOMAXPROCS=… go build [-gcflags=all='-N -l']` + run on a driver copy per row (`.tmp/gc-e3/`), go1.26.5 |
| `choice-trace-main-vs-e3.txt` | the whole-corpus choice trace, main vs E3 (the paragraph below) | the same method as E1/E2 |
| `ci-slow-e3.tail.txt` | the E3 full gate's tail (the paragraph below) | `scripts/capped scripts/ci --slow`, ANSI stripped |

References: `enumerate.py` E3a/E3c/E3d/E3e (regenerated `outcomes.txt`, `RESULT: PASS`); over the wire:
`Tests/UnseqWire.lean` 77 ok, 24 mutants refused by name (`mut-recv-nonatom`, `mut-recv-two-binds` new);
`scripts/check-unseq-wire` PASS (75 fixtures byte-identical; 24 mutants through the CLI); `scripts/check-wire-
boundary` PASS (11 + 17 unseq-node controls — the recv positive and the two mutants new). Machine:
`Tests/UnseqScheduler.lean` 72 ok — X3/X3e re-run on `x3graphRecv` (the receive as a `recv` body: the same set,
the same `deadlock` refusal on the empty channel); `scripts/check-unseq-scheduler` PASS; `scripts/check-mem-
callsites` PASS (70 rows, inventory unchanged — the recv body runs the statement's own `chanRecv`). Frontend:
`go test ./tools/nativefrontend/ ./tools/lowerdiag/` ok (the E13 guard test's recv/method target shapes moved
to the graph's truth). Lean build (explicit targets): `GOLEAN_MEM_MAX=32G scripts/capped lake build golean
UnseqWireTests UnseqSchedulerTests` EXIT=0 (102 jobs; the last rebuild after the decoder's `ref` argument arm
11 s). `scripts/check-bugs.sh` PASS at the re-pinned baseline (BUG-104 fixed: its three rows PASS).

**The full gate: `scripts/capped scripts/ci --slow` at the E3 tree** (main `14006270` + E1 `0fe7bdce` + E2 `6960697f` +
the E3 edits; the box-wide lock 03:42:41–03:59:42Z): **EXIT=1 in 1021 s, K=80 (`membership_draws 80`); 3722 rows 3481
PASS / 241 FAIL in the run = the pinned 3482 / 240 with the one 5a-class row red; RESULT FAIL on EXACTLY the two
5a-class items** — `certificate provenance` («STALE certification: changed dependency
build/files/GoLean/GoCore/AdmissionIndices.lean» — the `recv` constructor's index arm; the changed core inputs) and the
`baseline diff` DRIFT block's ONE line `imported-goose/channel/google-search baseline[PASS/membership] ->
now[FAIL/membership]` (the row's detail: STALE for `AdmissionIndices.lean`; «Fresh certification: unchanged set;
seconds=147.396» — the train installs the candidate at 5a). Every other step ok (core build warning-free, totality
audit, engine isolation, check-mem-callsites, admission proofs, declaration + wire boundaries (11 + 17 unseq-node
controls), method identity, unseq scheduler (Stage B + the recv body), unseq wire (24 mutants), frontend pins (twin =
pinned bytes), frontend / lowerdiag / harness unit tests, eval tests 274 ok, differential run, lane-validation fixtures
incl. the go half, negative corpus 394 matched, FloatVectors + inittask-std byte-exact, re-pin guard 0 PASS→non-PASS
with the 3 GREENED rows noted, executed library coverage). `ci-slow-e3.tail.txt` is the tail. Every row of this family
reproduces its pinned state in the run: BUG-104's three flips PASS/membership, `receiver-vs-arg-call` PASS/membership,
`nil-receiver-recursion` and `two-workers-own-chans` PASS/confluent, the five births in their lanes.

