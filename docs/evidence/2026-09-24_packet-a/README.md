# Window packet A — the contract: gate tails and checks (2026-09-27)

[AGENT packet A worker], branch `window/packet-a-contract-0927` off `main` @ `5946adfa` (train r49 close; the
coordinator's override of the brief's `3fb4a0d1`). Consuming docs: `docs/2026-09-24_packet-A-report.md`,
`docs/2026-09-24_execution-statement.md`. Host: linux/amd64, 32 cores; the box-wide lock held for the gates.
Toolchains: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); `leanprover/lean4:v4.32.2`.
Tree: clean at each gated commit. First fast `ci` at `60251b78`, the first `--diff` at `0317b64a` (pre-amend WIP
commits, kept as local refs `refs/snapshots/packet-a-0927/pregate-{1,2}`); the dispositions gates at `c3a351ac`
(rebased onto `main` @ `7d2a62e5`); the audit-round gates at `92aaab2a`; the FINAL gates at `36d8571b` — the
branch rebased onto `core/stray-panic-refusal-0927` @ `05d0dbd4` (F1 resolved; `F1Witness.lean`/`.out`).

**Conclusion.** `BridgeSet.lean` pins 24 statements (`#check` = the brief's table on every row); a two-row
mutant fails the build (`controls-and-checks.txt`). At `36d8571b` (same results at `92aaab2a`, `c3a351ac`): `lake build GoLean` EXIT=0, no warning;
`check-mem-callsites` PASS (the one «NO EXECUTION» row for `program_bridge_stmt`, per the disposition);
`GOLEAN_MEM_MAX=48G ci --diff` EXIT=1 in 948 s, red on EXACTLY the 5a pair — `certificate provenance` (STALE:
`build/files/GoLean.lean`) and `imported-goose/channel/google-search` PASS→FAIL/membership (its tier=slow
certificate STALE, same cause) — 3768 = 3531 / 237; every other step ok. `check-core-audit` PASS, 45 → 47
modules. History: the fast `ci` at `60251b78` was also red at `check-mem-callsites` (`program_bridge_stmt`,
then held; resolved by the disposition's inventory row) and at the two baseline-diff steps (a fresh worktree has
no recorded run; resolved by `--diff`). The fatal boundary controls' witness was pre-checked by `#eval`.

| File | What |
|---|---|
| `checks.txt` | `#check @<name>` output for the 24 members |
| `controls-and-checks.txt` | the drift mutant, `lake build GoLean`, `check-spec-anchors`, `reconcile-records` (verbatim) |
| `ci-fast-first.tail.txt` | fast `scripts/ci` at `60251b78` (the mem-callsites block + summary) |
| `ci-diff.tail.txt` | `GOLEAN_MEM_MAX=48G scripts/ci --diff` at `36d8571b` (certification, drift, mem-callsites, summary) |
| `core-audit.tail.txt` | `scripts/check-core-audit` at `36d8571b` |
| `F1Witness.lean`, `F1Witness.out` | the audit's F1 witness: `#eval` = the named refusal; proved `ClassRefusal`, not `ClassTerminal` |

## Reproduction (from the worktree root)

```sh
scripts/setup-deps --from /home/dev/projects/golean      # goose, raft, go at their pins
GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean
GOLEAN_MEM_MAX=48G scripts/capped lake env lean .tmp/Checks.lean    # the 24 `#check @<name>` lines, imports
                                                                    # GoLean.GoCore.{Trace,ProgramTrace,MultiSound}
GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff   # under the box-wide lock (artifacts/build-lock.d at the primary root)
scripts/capped scripts/check-core-audit
scripts/check-spec-anchors; python3 tools/reconcile-records
git grep -n -E "sorry|admit|native_decide|axiom|partial" -- GoLean/GoCore/BridgeSet.lean GoLean/GoCore/ExecutionStatement.lean
```
