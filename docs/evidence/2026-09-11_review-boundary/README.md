# Review-boundary fix lane (BUG-108/109/110) — gate lines, red-first records, measurements (2026-09-11)

[AGENT] lane `fix/review-boundary-0911`, worktree `.claude/worktrees/fix-review-boundary`,
cut from main `a461ed8b`. Authority: [USER] Mike 2026-09-11, verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «Great, go ahead and land this, then launch the lanes», on the
sequence of `docs/2026-09-11_review-dispositions.md` §4 step 1; BUG-109's policy: «Yes, refuse
non-1.26». Consuming docs: `docs/BUGS.md` BUG-108/109/110, `HANDOFF.md` at the worktree root
(until landed), the baseline header of `baselines/native-full.tsv`.

Host: linux/amd64, the shared 32-core / 125 GiB development box, other lanes' gates running
concurrently (load not controlled; wall times are indicative only). Toolchains: `go version
go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`), `leanprover/lean4:v4.32.2` (`lean-toolchain`).
Every lake/lean/ci invocation ran through `scripts/capped` at `GOLEAN_MEM_MAX=48G` (→
`LEAN_NUM_THREADS=6`), under the box-wide build lock (`artifacts/build-lock.d` in the primary
checkout; owner file; released after each run).

## Files

| file | what | produced by |
|---|---|---|
| `red-first-bug108-109-probes.txt` | the review's F1/F2 probes re-run at the cut through `go run`, the freshly built frontend and `golean native-json-run` | `.tmp/nativefrontend --dir <probe> --out …; golean native-json-run --input … --function probe` over the dirs recreated from `docs/evidence/2026-09-11_project-review/probe-inputs.json` |
| `red-first-bug110-mutations.txt` | the review's F3 wire mutations (absent `resultTypes`, forged leading `schema`) plus an unpaired-surrogate mutation, through the real CLI at the cut | python byte mutations of the `discard_call` probe's wire (the recipe is `scripts/check-wire-boundary`, S3) |
| `s1-red-first-focused-run.txt` | `scripts/coverage run --prefix source-selection/` at the cut: the 11 born rows through the real runner | focused run, capped 48G |

## Stage S1a — BUG-108 red-first rows (records: rows + baseline + Cases line)

Rows: `Corpus/coverage/exec/source-selection/{excluded-init,excluded-conflict,excluded-import,
included-suffix}` (11 rows). Predicted and observed at the cut: 5 FAIL/differential (GoLean 2, gc
1 — an excluded sibling's `init` ran), 2 FAIL/frontend-export (`conflict redeclared in this block`;
`stdlib-qualified selector os.Args … (package "os")`), 4 PASS controls.

Gate (full): `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `a461ed8b` + the uncommitted
rows/BUGS.md (dirty=2 paths) → **EXIT=1, wall 952 s**, jobs: core build 202 (no-op on the copied
cache), differential fan-out `jobs 32`, membership K=32, tier=slow row CERTIFIED-CACHED. The ONLY
reds: `bug-index cross-check` (BUG-108's Cases ids not yet in the baseline) and `baseline diff
(DRIFT)` = exactly the 11 `NEW id (not in baseline)` lines (7 FAIL, 4 PASS); all 3665 prior
result/stage rows reproduced; negatives 394 matched. Re-pin from that run's `latest.tsv`
(ran=3676 = manifest 3676): `3676 = 3421 PASS / 255 FAIL`; `coverage-baseline-diff --full` exit 0;
`check-alternation-survival` exit 0 (`channels/select-select/beside-loop` kept verbatim);
`check-bugs.sh` ok (110 bugs; backlog 14 = coverage 10 / latitude 4 / wrong-answer 0, unchanged).

Re-judgement (fast): `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci` on the re-pinned tree →
see the S1a line in the gate table below.

## Stage S1b — BUG-108 fix (frontend file selection from go/build under the pinned target; wire `buildContext`; decoder pin)

Code: `tools/nativefrontend/fileselect.go` (new; `selectPackageFiles`, `pinnedBuildContext`,
`buildContextRecord`), `main.go` + `load.go` (both selection sites), `langversion.go`
(`judgeBuildConstraintLine` factored out — policy text unchanged), `emit.go` (the `buildContext`
record beside `fileOrder`), `GoLean/NativeToIR.lean` (`pinnedSelectionTarget`, `decodeBuildContext`
— REQUIRED, refuses any other target), `Tests/GoCoreEval.lean` (+4 pins; 9 hand-built envelopes
carry the field), `Tests/MethodIdentity.lean` (its envelope), `tools/nativefrontend/
fileselect_test.go` (new), `tools/lowerdiag/causes.tsv` (+3 cause rows classifying the new refusal
formats: `cgo-file`, `non-go-sources` out-of-language; `gc-refuses-directory` by-design) and
`unclassified-formats.txt` (regenerated; coverage 358/401 → 364/401).

Records moved with it: `baselines/pins/twin-chdriver.wire.json` 13d8b659… → e1a87725… (ONLY the
added key; `twin-repin/structural-diff.txt`), the certified TSV header's `wire-sha256` 2f1d639f… →
736f1730… with the reason, the certified `.json` re-minted (below), the baseline re-pinned (7 flips
FAIL → PASS), BUG-108 `Status: fixed`.

Local checks before the gates: `go build` / `go vet` / `go test ./tools/nativefrontend` ok;
`scripts/coverage run --prefix source-selection/` → 11/11 PASS; `lake exe gocore-eval-tests` 211 ok
(4 new BUG-108 pins); the twin wire byte-identical after the policy-site move; `go test
./tools/lowerdiag` ok after the cause rows.

Gates (all `GOLEAN_MEM_MAX=48G scripts/capped`, lock held), tree = `6264f152` + the S1b edits:

- run #1 `scripts/ci --slow`: EXIT=1, 1033 s. Reds: `bug-index` (BUG-108 marked fixed while the
  baseline still held the 7 reds — resolves at the re-pin), `certificate provenance` (STALE: the
  inventory moved with the edited files — the expected F8 signal), `lowering-diagnostic tables`
  (UNEXPECTED: `TestVocabularyCoverageIsTracked` 358/401 < 90% — six new `unsup` formats
  unclassified; fixed by the three cause rows above), `baseline diff` (the 7 predicted flips + the
  google-search row FAIL/membership: `STALE certification claim: changed dependency wire_sha256`
  while the enumerator minted `Fresh certification: unchanged set; seconds=171.018`). Candidate
  reviewed: claim differs ONLY in `wire_sha256`; inputs differ exactly in the touched files
  (+`fileselect.go`, +`fileselect_test.go`); `observations_sha256` identical; installed.
- run #2 `scripts/ci --slow` (after the lowerdiag classification — a `tools/` edit re-stales the
  record, so a second fresh certification was needed; ordering lesson recorded in HANDOFF.md):
  EXIT=1, 1006 s. Reds: `bug-index`, `certificate provenance` (STALE by exactly
  `tools/lowerdiag/{causes.tsv,unclassified-formats.txt}`), `baseline diff` (the same 7 flips +
  google-search stale). `lowering-diagnostic tables` ok. Candidate: set and claim identical to the
  installed record; inputs differ in the two lowerdiag files only; installed. Enumeration 162.413 s.
- run #3 `scripts/ci --diff` (cache mode against the installed record): EXIT=1, 887 s. Reds: `bug-index` (resolves at the re-pin below) and `baseline diff` = EXACTLY the 7 predicted flips; `certificate provenance` ok; google-search PASS CERTIFIED-CACHED against the installed record (inputs 1a853c96…); 3676 = 3428 PASS / 248 FAIL; 394 negatives match.
- re-pin from run #3's `latest.tsv`: 3676 = 3428 PASS / 248 FAIL; body diff = exactly the 7 BUG-108 rows FAIL → PASS; `coverage-baseline-diff --full` 0, `check-alternation-survival` 0, `check-bugs.sh` 0 (BUG-108 fixed, its 7 cases PASS — the symmetric rule holds).
- re-judge `scripts/ci` (fast) on the exact committed tree: see the gate table (S1b re-judge).

## Stage S2 — BUG-109 fix (the module's `go` directive; RULED [USER] «Yes, refuse non-1.26»)

Code: `tools/nativefrontend/modfile.go` (new; `findGoMod` walks up like the go command,
`goDirective` strict scanner, `refuseForeignModuleVersion`), wired in `main.go` run() and
`load.go` parseLocal; `modfile_test.go` (new; 13 directive shapes, the walk-up, an imported
package's nested module); `tools/lowerdiag/causes.tsv` +1 row `foreign-module-version`
(by-design) and `unclassified-formats.txt` regenerated (372/409).

WHY NO CORPUS ROW (said plainly): the runner's oracle is `GO111MODULE=off go run .` inside a
harness-generated copy that holds `*.go` only (`scripts/diff-coverage` `go_run_oracle`;
`tools/coverageharness` `packageFiles`), so a `go.mod` in a row directory is never seen by the
oracle — a `go 1.21` row would have gc answering the 1.26 program (3) against a frontend refusal,
and a `go 1.26` twin would test nothing about the directive. Either would be a fake row. The pin is
the unit tests plus the transcripts here:

| file | what |
|---|---|
| `s2-bug109-module-directive.txt` | the review's `module1.21` / `module1.26` probes: `GO111MODULE=on go run .` (9 / 3), the frontend built from `60874ada` (BEFORE S2: both accepted, exit 0), the S2 frontend (AFTER: `…/go.mod declares go 1.21; GoLean implements the Go 1.26 language only (…)`, exit 1; `go 1.26` accepted) |
| `s2-lower-diagnose-module1.21.txt` | `scripts/lower-diagnose` (the real tool) on the `go 1.21` probe after S2 — the dynamic pass shows the refusal by name; DIAGNOSTIC output, trimmed |

Movement: none expected (zero `go.mod` under `Corpus/`; the raft twin wire byte-identical).

Gates (`GOLEAN_MEM_MAX=48G scripts/capped`, lock held), tree = `60874ada` + the S2 edits:

- run #1 `scripts/ci --slow`: EXIT=1, 995 s. Reds: `certificate provenance` (STALE — the expected
  F8 signal; candidate minted, `Fresh certification: unchanged set`, 168.9 s) and `baseline diff` =
  the google-search row alone (`STALE certification` on the record while the enumerator re-derived
  the identical set); 3676 rows, no other movement (3427 PASS / 249 FAIL with that one stale red).
  Candidate reviewed: set and claim identical to the installed record; inputs differ exactly in
  `modfile.go` (+), `modfile_test.go` (+), `main.go`, `load.go`, `tools/lowerdiag/{causes.tsv,
  unclassified-formats.txt}`; installed.
- run #2 `scripts/ci --diff` (cache mode against the installed record, the tree committed as S2): EXIT=0, 885 s, RESULT: PASS — no drift (3676 rows reproduce; 394 negatives), certificate provenance ok, google-search CERTIFIED-CACHED; no baseline re-pin.

## Stage S3 — BUG-110 fix (strict byte parser at the production wire boundary; `resultTypes` required)

Code: `GoLean/CLI.lean` (`native-json-run`, `coverage-observations`: `IO.FS.readBinFile` +
`GoLean.StrictJson.parseBytes`), `GoLean/ChoiceTrace.lean` (`loadProgram`, same),
`GoLean/StrictJsonParse.lean` (header note: it IS the production byte boundary now),
`GoLean/NativeToIR.lean` (`decodeResultTypes` / `requireResultTypes`: the vector is required on
every call-shaped node — `call`, `call-value`, `atomic-op`, `sync-op` — and arity-checked where
consumed; the two `resultTypes[i]?.getD .int` sites and the expression-statement "absent →
targetless" fallback are gone; TODO.md's F5 item discharged), `scripts/check-wire-boundary` (new
`scripts/ci` step) + `Tests/wire-boundary/main.go` (the review's discard-call probe).

| file | what |
|---|---|
| `s3-check-wire-boundary.txt` | the gate script's transcript: 10 byte-level controls through the real CLI — positive control 42, valid surrogate pair 42; forged leading duplicate `schema`, duplicate key deep in a call node, absent `resultTypes`, mis-sized `resultTypes`, absent `buildContext`, unpaired high/low surrogate in an UNREAD field, raw invalid UTF-8 — each refused naming its cause |
| `s3-decode-timing.txt` | decode wall time before/after, then an interleaved A/B of the two binaries (pre-S3 rebuilt from `07bc55cb`, sha `b130c4f4…` = the S1b binary; S3 `dae23a5c…`) on the raft twin wire (11.4 MB), the largest corpus wire (3.5 MB, `stdlib-source/frontier/*`) and a 1.5 KB fixture wire; 7 runs each, medians |

Timing verdict (medians, A/B interleaved; `native-json-run --function <nonexistent>` = read +
parse + `decodeProgram` + subject lookup, verified to reach `GoCore function not found`): twin
0.124 s → 0.055 s (FASTER — the byte read replaces `IO.FS.readFile`'s `String` build; a
hypothesis, not isolated); largest corpus wire 0.052 s → 0.075 s (+0.023 s, +44% — the strict
parser's own cost); 1.5 KB wire 0.021 → 0.020 s (process startup dominates). Against the runner's
30 s per-case budget the fast path is unaffected in practice; the parser is not weakened.

FINDING at run #1 (fixed before run #2): the strict parser's `maxNestingDepth := 64` is the
DECLARATION envelope's resource bound; program wires nest with their syntax (the fmt shim's
verb-dispatch `else` chain alone is ~20 statement levels × ~3 JSON levels), and run #1 refused
105 real wires (`JSON nesting deeper than 64`; ~100 rows PASS → FAIL/lean-observation). Measured
over every corpus wire + the twin (3634 files; bracket depth outside strings): maximum 120
(`init/library-var-type-*`), twin 73, histogram 0–15: 2172, 16–31: 1200, 32–47: 146, 48–63: 11,
64–111: 100, 112+: 5. Fix: `parse`/`parseBytes` take the bound as a parameter (declaration
default 64 unchanged; its tests still pin 64/65/10000), the production wire path passes
`wireNestingDepth = 1024` (8.5× the deepest observed; still a finite, by-name refusal — the gate's
11th control wraps `buildTags` in 1100 arrays and is refused). Focused re-runs of every regressed
prefix (`fmt/`, `noodler/strings/`, `init/library-var-type*`, `panic-recover/
shim-refusal-unrecoverable/`, `spec-examples-decl/timezone-stringer`; 96 PASS / 23 FAIL): every
remaining FAIL is the baseline's own FAIL/frontend-export row (set difference empty).

Gates (`GOLEAN_MEM_MAX=48G scripts/capped`, lock held), tree = `07bc55cb` + the S3 edits:

- run #1 `scripts/ci --slow` (before the depth fix): EXIT=1, 995 s. `wire boundary` ok;
  `certificate provenance` STALE (candidate minted, set unchanged, 162.9 s — superseded by run #2's);
  `baseline diff`: the ~100 depth regressions above + google-search stale. NOT installed.
- run #2 `scripts/ci --slow` (with the depth fix): EXIT=1, 1149 s. `wire boundary` ok (11
  controls); `certificate provenance` STALE (the expected F8 signal; candidate minted, `Fresh
  certification: unchanged set`, 150.8 s); `baseline diff` = the google-search row alone (stale
  record); 3676 rows, no other movement (3427 PASS / 249 FAIL with that one stale red). Candidate
  reviewed: set and claim identical; inputs differ exactly in `GoLean/{CLI,ChoiceTrace,NativeToIR,
  StrictJsonParse}.lean`, `scripts/ci`, `scripts/check-wire-boundary` (+); installed.
- run #3 `scripts/ci --diff` (cache mode against the installed record, the tree committed as S3): EXIT=0, 888 s, RESULT: PASS — no drift (3676 rows reproduce; 394 negatives), certificate provenance ok, wire boundary ok (11 controls), google-search CERTIFIED-CACHED; no baseline re-pin.

## Gate table

| stage | command | tree | exit | wall | notes |
|---|---|---|---|---|---|
| S1a measure | `scripts/ci --diff` | a461ed8b + rows/BUGS.md (dirty) | 1 | 952 s | reds = bug-index (ids not yet pinned) + baseline drift (11 NEW ids) only |
| S1a re-judge 1 | `scripts/ci` (fast) | + re-pinned baseline, first form (set-identical, rows reordered to run order) | 0 | 569 s | RESULT: PASS; notes only (dirty-tree caveat on both baseline diffs, reconciler report-only) |
| S1a re-judge 2 | `scripts/ci` (fast) | + re-pinned baseline, order-preserving form (body diff = exactly the 11 born rows) | 0 | 575 s | RESULT: PASS — the tree committed as S1a (`6264f152`) |
| S1b run #1 | `scripts/ci --slow` | 6264f152 + S1b edits | 1 | 1033 s | reds: bug-index, certificate provenance (STALE → candidate minted, set unchanged, 171 s), lowering-diagnostic tables (six unclassified formats — fixed), baseline drift (7 flips + google-search stale) |
| S1b run #2 | `scripts/ci --slow` | + lowerdiag cause rows | 1 | 1006 s | reds: bug-index, certificate provenance (STALE by the two lowerdiag files → candidate, set unchanged, 162 s), baseline drift (7 flips + google-search stale) |
| S1b run #3 | `scripts/ci --diff` | + installed record | 1 | 887 s | reds: bug-index, baseline drift = exactly the 7 flips; certificate provenance ok; google-search CERTIFIED-CACHED |
| S1b re-judge | `scripts/ci` (fast) | + re-pinned baseline, BUG-108 fixed | 0 | 554 s | RESULT: PASS — the tree committed as S1b (`60874ada`) |
| S2 run #1 | `scripts/ci --slow` | 60874ada + S2 edits | 1 | 995 s | reds: certificate provenance (STALE → candidate, set unchanged, 169 s), baseline drift = google-search stale only |
| S2 run #2 | `scripts/ci --diff` | + installed record (the tree committed as S2, `07bc55cb`) | 0 | 885 s | RESULT: PASS |
| S3 run #1 | `scripts/ci --slow` | 07bc55cb + S3 edits (declaration depth bound 64 on the wire path) | 1 | 995 s | reds: certificate provenance (STALE), baseline drift = ~100 rows refused `JSON nesting deeper than 64` + google-search stale — the depth FINDING; not installed |
| S3 run #2 | `scripts/ci --slow` | + `wireNestingDepth = 1024`, 11th control | 1 | 1149 s | reds: certificate provenance (STALE → candidate, set unchanged, 151 s), baseline drift = google-search stale only |
| S3 run #3 | `scripts/ci --diff` | + installed record (the tree committed as S3) | 0 | 888 s | RESULT: PASS |
