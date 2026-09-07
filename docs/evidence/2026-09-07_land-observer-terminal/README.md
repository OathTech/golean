# Gate tail and moved-row table for landing chunk L4 `land/observer-terminal` — the typed-consumer sprint's crash-channel observer and terminal classifier on main (2026-09-07)

[AGENT] landing worker, 2026-09-07. Consuming doc:
`docs/2026-09-07_land-observer-terminal.md` (§2 the observation-schema
compatibility statement, §7 the gate), which cites this directory. Per the
coordinator's brief this directory holds ONLY the gate tail and the moved-row
measurement table (plus this README, which the evidence convention requires);
every full-run table, raw descriptor and source hash stays out of `docs/evidence/`
([USER] ruling of 2026-09-07, relayed, `AGENTS.md` "Evidence on main").

Contents (no archives, no source copies, every file far under 256 KiB):

- `moved-rows.tsv` — the SIX rows this chunk moves in
  `baselines/native-full.tsv` (5 PASS → FAIL/go-observation, 1 FAIL stage
  change), each with its baseline verdict, its new verdict, the `docs/BUGS.md`
  entry whose `Cases:` line carries it (BUG-106 / BUG-107), and the run's named
  refusal. Measured by the focused slice named in its header (76 rows: the two
  born families plus every `init/`, `noodler/initpanic/` and
  `sync/mutex-unlock-fatal/` row, `GOLEAN_COVERAGE_JOBS=16`) and re-verified
  by the full gate below.
- `ci-diff-tail.txt` — the tail of `scripts/capped scripts/ci --diff` at the
  tested commit (the RESULTS block: every step's ok/bad line, the baseline
  diff, the re-pin guard, the RESULT line) plus the run's meta record
  (`git_commit`, `git_dirty`, `go_toolchain`, `go_traceback`,
  `go_crash_channel`, `jobs`).

Tested commit: see the first lines of `ci-diff-tail.txt` (`git_commit`,
`git_dirty false`). The final landing commit (the one carrying this directory)
differs from the tested commit ONLY by this directory's tail file and the
gate section of the landing note — the documentation-only amend practice of
`../2026-09-07_land-gate-tooling/` and `../2026-09-07_land-typed-core-proofs/`;
the pre-amend tip is kept reachable as `refs/snapshots/land-observer-terminal-gated`.

Reproduce from the repository root at the tested commit (Go `go1.26.5
linux/amd64` = the pin in `baselines/go-oracle-pin`; Lean per
`lean-toolchain`; host linux/amd64, 32 cores / 125 GiB, other landing lanes
active on the box; every Lean/Lake/ci invocation via `scripts/capped`):

```sh
scripts/setup-deps
GOLEAN_COVERAGE_JOBS=16 scripts/capped scripts/coverage run --prefix panic-recover/panic-controls --prefix panic-recover/panic-markers --prefix sync/mutex-unlock-fatal --prefix init/ --prefix noodler/initpanic
scripts/coverage-baseline-diff artifacts/coverage/latest.tsv      # the six moves + 20 NEW ids against the previous pin
GOLEAN_COVERAGE_JOBS=16 scripts/capped scripts/ci --diff
```

Conclusion (the one the landing note relies on): with the same-run crash
channel MANDATORY, the full corpus moves by exactly the six rows in
`moved-rows.tsv` plus twenty born rows (14 PASS, 6 red at main's renderer on
BUG-004's line); every other row, the certified set, the K=32/80 sampling
rule and the stage alternations are unchanged; the machine (`GoLean/`) is
byte-identical to main.
