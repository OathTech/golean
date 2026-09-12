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

## Gate table

| stage | command | tree | exit | wall | notes |
|---|---|---|---|---|---|
| S1a measure | `scripts/ci --diff` | a461ed8b + rows/BUGS.md (dirty) | 1 | 952 s | reds = bug-index (ids not yet pinned) + baseline drift (11 NEW ids) only |
| S1a re-judge 1 | `scripts/ci` (fast) | + re-pinned baseline, first form (set-identical, rows reordered to run order) | 0 | 569 s | RESULT: PASS; notes only (dirty-tree caveat on both baseline diffs, reconciler report-only) |
| S1a re-judge 2 | `scripts/ci` (fast) | + re-pinned baseline, order-preserving form (body diff = exactly the 11 born rows) | 0 | 575 s | RESULT: PASS — the tree committed as S1a |
