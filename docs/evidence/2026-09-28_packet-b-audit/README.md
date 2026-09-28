# Packet B (the bridges) pre-merge audit — evidence (2026-09-28)

[AGENT] auditor. Consuming doc: `docs/2026-09-28_packet-b-audit.md`. Tree: `window/packet-b-bridges-0928` @
`ae37e5b8` (clean; audit branch `review/packet-b-bridges-0928`), `.lake` warmed from the packet-b worktree after a
byte-compare of every tracked `.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` (no difference).
Host linux/amd64, the shared 125 G box, every build/gate under the box-wide lock. Toolchain: go1.26.5 (=
`baselines/go-oracle-pin`, checked by the gate's oracle step); Lean `leanprover/lean4:v4.32.2`.

| File | What |
|---|---|
| `ci-diff-tail.txt` | `ci --diff` from the baseline diff to the end: EXIT=1, red on exactly the 5a pair |
| `axioms.txt` | `#print axioms` for all 150 theorems of the three new modules + `stepThread_privateStep_label` |
| `scratch-checks.txt` | exit codes of the scratch checks; the three BridgeSet mutations (diff + the error); core-audit tail |
| `Witnesses.lean`, `witnesses-out.txt` | `#eval` witnesses for `stepFn`'s error classes; the no-stray-panic lemma applied; a written-out pin |

Reproduction (from the worktree root; scratch files live in `.tmp/`, which is gitignored):

```
GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff
scripts/capped lake env lean .tmp/Axioms.lean        # generated: one `#print axioms` line per `^theorem` name
scripts/capped lake env lean .tmp/Witnesses.lean     # = Witnesses.lean here minus its first line
scripts/capped lake env lean .tmp/BridgeSetCtl.lean  # verbatim copy of GoLean/GoCore/BridgeSet.lean: EXIT 0
scripts/capped lake env lean .tmp/BridgeSetMut{1,2,3}.lean   # the mutations shown in scratch-checks.txt: EXIT 1 each
scripts/capped scripts/check-core-audit
```
