# Landing chunk L2 `land/gate-tooling` — the evidence-size gate's own record (2026-09-07)

[AGENT] landing worker under the coordinator's brief; [USER] ruling of
2026-09-07 (relayed) quoted in `docs/2026-09-07_land-gate-tooling.md`, the
consuming doc.

## Conclusion

Main `47195683` already carries 18 offenders of the proposed caps (16 files
over 256 KiB, one 10.4 MB directory, one byte copy of a tracked source file,
no archives); they are frozen in `docs/evidence/SIZE-ALLOWLIST.tsv`, the
checker passes on the landed tree with 0 new offenders, and its self-test
passes 18/18. The gate is a `scripts/ci` step; the baseline did not move.

## Files

| file | producer |
|---|---|
| `check-evidence-size.main-no-allowlist.txt` | `scripts/check-evidence-size --allowlist .tmp/no-such-allowlist` on this tree (index == main's evidence set + the allowlist itself): the raw 18 offenders, exit 1 |
| `check-evidence-size.tip.txt` | `scripts/check-evidence-size --verbose` with the allowlist: every allowlisted entry named, PASS, exit 0 |
| `test-check-evidence-size.txt` | `scripts/test-check-evidence-size`: 18 cases, PASS |
| `ci-diff-tail.txt` | `GOLEAN_COVERAGE_JOBS=2 scripts/capped scripts/ci --diff` at the pre-amend commit `485c5b7f` (design note §7): RESULT: PASS, baseline diff FULL 3598/3598, no regression; the recorded meta's provenance lines are included |

## Toolchain, commit, host

- go1.26.5 linux/amd64 (`baselines/go-oracle-pin`, unchanged); Lean toolchain
  per `lean-toolchain`, built with `scripts/capped lake build`.
- Commit: the `--diff` gate ran at `485c5b7f`
  (`refs/snapshots/land-gate-tooling-pre-amend`), a clean tree
  (`git_dirty false` in the recorded meta); the final commit is its amend,
  differing only by this directory's tail file and the §7 wording of the
  design note and this README (`git diff refs/snapshots/land-gate-tooling-pre-amend HEAD --stat`).
- Host: linux/amd64, the shared agent box under concurrent lane load;
  `GOLEAN_COVERAGE_JOBS=2` (the ruled concurrency).
