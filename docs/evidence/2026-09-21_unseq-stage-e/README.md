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

## E2 — pointers, fields and maps as occurrences (closes BUG-104's map-key-beside-a-call row)

| file | what | producer |
|---|---|---|
| `census-e2.txt` | the census AFTER E1 (the E1 frontend) vs AFTER E2 (the E2 frontend): admitted 146 → 176 (+27 from the widening in 17 packages, 0 lost; +3 from the E1 package born after the E1 census; 107 943 → 107 963 sweeps); the twin 10 203 / 0 on both; the per-package table, former reasons, forms | `.tmp/census/run.sh`, `summarize.py`, `diff.py` (tolerating the born package's rows) |
| `census-newly-admitted-e2.tsv` | the 27 sweeps that enter at E2 | `diff.py` |
| `diff-one-e2.txt` | the focused differential on the 38 affected rows on the E2 frontend + binary: the 1 flip, the 5 lane moves, the 8 births, the 4 E13 deref/map sets unchanged at 2 members, everything else unchanged; the one width/sites correction on `len-nil-only-none` and its re-run | `scripts/diff-one <ids…>` (the per-row details are in the run's `artifacts/coverage/latest.tsv` and quoted in the file) |
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
