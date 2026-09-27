# Window packet A — the contract: gate tails and checks (2026-09-27)

[AGENT packet A worker], branch `window/packet-a-contract-0927` off `main` @ `5946adfa` (train r49 close; the
coordinator's override of the brief's `3fb4a0d1`). Consuming docs: `docs/2026-09-24_packet-A-report.md`,
`docs/2026-09-24_execution-statement.md`. Host: linux/amd64, 32 cores; the box-wide lock held for the gates.
Toolchains: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); `leanprover/lean4:v4.32.2`.
Tree: clean at each named commit — the first gate at `60251b78`, the second at `0317b64a`: pre-amend WIP commits,
kept reachable as local refs `refs/snapshots/packet-a-0927/pregate-{1,2}`; the branch tip's tree = `0317b64a`'s plus
only this dir's README/tails and the report.

**Conclusion.** `BridgeSet.lean` pins 24 statements (`#check` = the brief's table on every row); a two-row
mutant fails the build (`controls-and-checks.txt`). `lake build GoLean` EXIT=0, no warning. `ci --diff`
EXIT=1 red on EXACTLY the 5a pair — `certificate provenance` (STALE: `build/files/GoLean.lean`) and
`imported-goose/channel/google-search` PASS→FAIL/membership (its tier=slow certificate STALE for the same
reason) — 3768 run = 3531 PASS / 237 FAIL; every other step ok. The fast `ci` at `60251b78` was ALSO red at
`check-mem-callsites` (a NEW `loadMany` row from `program_bridge_stmt`) — resolved by HOLDING that statement
(`held-program-bridge-stmt.lean.txt`), not by editing `scripts/`; and at the two baseline-diff steps (a fresh
worktree has no recorded run), resolved by running `--diff`. `check-core-audit` PASS, 45 → 47 modules.

| File | What |
|---|---|
| `checks.txt` | `#check @<name>` output for the 24 members |
| `controls-and-checks.txt` | the drift mutant, `lake build GoLean`, `check-spec-anchors`, `reconcile-records` (verbatim) |
| `ci-fast-first.tail.txt` | fast `scripts/ci` at `60251b78` (the mem-callsites block + summary) |
| `ci-diff.tail.txt` | `scripts/ci --diff` at `0317b64a` (certification line, drift block, summary) |
| `core-audit.tail.txt` | `scripts/check-core-audit` at `0317b64a` |
| `held-program-bridge-stmt.lean.txt` | the held statement's exact elaborated text |

## Reproduction (from the worktree root)

```sh
scripts/setup-deps --from /home/dev/projects/golean      # goose, raft, go at their pins
GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean
GOLEAN_MEM_MAX=48G scripts/capped lake env lean .tmp/Checks.lean    # the 24 `#check @<name>` lines, imports
                                                                    # GoLean.GoCore.{Trace,ProgramTrace,MultiSound}
scripts/capped scripts/ci --diff            # under the box-wide lock (artifacts/build-lock.d at the primary root)
scripts/capped scripts/check-core-audit
scripts/check-spec-anchors; python3 tools/reconcile-records
git grep -n -E "sorry|admit|native_decide|axiom|partial" -- GoLean/GoCore/BridgeSet.lean GoLean/GoCore/ExecutionStatement.lean
```
