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

## Gate table

| stage | command | tree | exit | wall | notes |
|---|---|---|---|---|---|
| S1a measure | `scripts/ci --diff` | a461ed8b + rows/BUGS.md (dirty) | 1 | 952 s | reds = bug-index (ids not yet pinned) + baseline drift (11 NEW ids) only |
| S1a re-judge 1 | `scripts/ci` (fast) | + re-pinned baseline, first form (set-identical, rows reordered to run order) | 0 | 569 s | RESULT: PASS; notes only (dirty-tree caveat on both baseline diffs, reconciler report-only) |
| S1a re-judge 2 | `scripts/ci` (fast) | + re-pinned baseline, order-preserving form (body diff = exactly the 11 born rows) | 0 | 575 s | RESULT: PASS — the tree committed as S1a (`6264f152`) |
| S1b run #1 | `scripts/ci --slow` | 6264f152 + S1b edits | 1 | 1033 s | reds: bug-index, certificate provenance (STALE → candidate minted, set unchanged, 171 s), lowering-diagnostic tables (six unclassified formats — fixed), baseline drift (7 flips + google-search stale) |
| S1b run #2 | `scripts/ci --slow` | + lowerdiag cause rows | 1 | 1006 s | reds: bug-index, certificate provenance (STALE by the two lowerdiag files → candidate, set unchanged, 162 s), baseline drift (7 flips + google-search stale) |
| S1b run #3 | `scripts/ci --diff` | + installed record | 1 | 887 s | reds: bug-index, baseline drift = exactly the 7 flips; certificate provenance ok; google-search CERTIFIED-CACHED |
| S1b re-judge | `scripts/ci` (fast) | + re-pinned baseline, BUG-108 fixed | 0 | 554 s | RESULT: PASS — the tree committed as S1b |
