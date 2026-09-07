# Gate tail for landing chunk L6 `land/sprint-records` — `scripts/ci --diff` at the clean committed tip (2026-09-07)

[AGENT] landing worker, lane `land-sprint-records`, 2026-09-07. Consuming
record: `docs/2026-09-07_land-sprint-records.md` §5.

## What this is

The result lines and run meta of the merge-protocol gate for chunk L6 — a
DOCS-ONLY chunk (no code, corpus, baseline or gate-script change), run
because the protocol runs it and because a fresh worktree's `scripts/ci`
without `--diff` fails closed (no coverage records to judge).

## Reproduction

```
git worktree add .claude/worktrees/land-sprint-records land/sprint-records
cd .claude/worktrees/land-sprint-records && scripts/setup-deps --from <primary checkout>
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=4 GOLEAN_COVERAGE_JOBS=8 scripts/capped scripts/ci --diff
```

- Commit: `0c9c6d6ae062955ddaac238e1cbb2af581a3502e` (the records commit of
  this chunk, rebased onto main `29f77b43` after round 24 landed), CLEAN
  (`git_dirty false` in the run meta; `git status --short` empty before and
  after). The final landing commit differs from it ONLY by this directory
  and §5 of the chunk note (the documentation-only amend of the landing
  practice, as L1/L2/L3/L4 did); the gate was not re-run at the amended tip
  — the three steps that read those files were (`scripts/check-evidence-size`,
  `scripts/check-bugs.sh`, `tools/reconcile-records`; each recorded in §5).
- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`;
  the ci's `oracle toolchain (go1.26.5 = pin)` step ok); Lean per
  `lean-toolchain`; every Lean/Lake invocation via `scripts/capped`.
- Host: linux/amd64, 32 cores, 125 GiB; load ≈ 1 at start (the concurrent
  round-24 gate had finished); `jobs 8` (the brief's cap was 12).
- Date: 2026-09-07, 20:04–20:38 local.

## Result (the tail is `ci-diff-tail.txt`, verbatim)

`differential coverage summary: cases=3654 pass=3403 fail=251 export_status=0`
— identical to main `29f77b43`'s pin (3654 = 3403 / 251, re-derived by awk
from the baseline's data rows); `ok   evidence-on-main size gate`;
`ok   negative baseline diff (no regression)`; `ok   baseline diff FULL
(3654/3654, no regression)`; `note reconciler: 2 finding(s), 0 HIGH`;
`RESULT: PASS`; wrapper `exit=0`. Zero drift: no row moved, no re-pin owed,
no re-pin-guard note (the baseline file is untouched by this chunk).
`scripts/ci --slow` is not owed (no `wire.go`/`NativeToIR.lean` change).

## The two earlier attempts, for the record

1. At `ee23f302` on main `dd636996` (before round 24): `RESULT: PASS`,
   3618 = 3362 / 256 = that main's pin — but recorded on a DIRTY tree
   (`git_dirty true`): this worker edited three records (the manifest
   README's cap-violation counts, one deviation sentence in §7.8.2, one
   round attribution in the handoff) WHILE the run was in progress, so the
   ci demoted both baseline-diff lines to «certifies that worktree state,
   not a commit». Not the protocol's gate; superseded. Log kept in the
   lane's `.tmp/` only.
2. At `b06df2c2` (the same records, clean) on `dd636996`: STOPPED by this
   worker (by the background task's own id — never by pattern) when the
   coordinator reported round 24 landed (`29f77b43`), since the gate had to
   run at the rebased tip. No result.
3. This run, at `0c9c6d6a` on `29f77b43`: the record above.

## Conclusion

The docs-only chunk changes nothing the gate measures: the differential
reproduces main's post-round-24 pin exactly, the evidence-size gate accepts
the manifest (the largest file 55,511 B; the directory ≈ 0.54 MB), and the
reconciler reports only the two pre-existing MEDIUMs (C13 off-pin Go-version
citations; C5 FR-7's `=` case id).
