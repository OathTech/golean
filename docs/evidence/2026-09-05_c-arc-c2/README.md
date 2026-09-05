# C-arc C2 evidence — the well-founded, index-keyed type table, lane `c-arc-c2` (2026-09-05)

[AGENT] records for `docs/2026-09-05_c-arc-c2-design.md` (§7 cites this
dir; gate G-C2 RULED [USER] 2026-09-04 / CONFIRMED 2026-09-05, both
relayed by the coordinator and cited as relayed).

## Toolchain, tree, host

- Go `go1.26.5 linux/amd64` = `baselines/go-oracle-pin`.
- Lean `leanprover/lean4:v4.32.2`; the `golean` binary built by
  `scripts/capped lake build` in the lane worktree.
- Tree: branch `c-arc-c2` off `main @ b77f3298`; code commit `3a229bae`,
  refusal-class fix `f33d3092` (a Go refusal STRING only); the gate ran
  at the tip named in `ci-diff.txt`'s header line below. Trees were
  clean at every recorded run unless a file says otherwise.
- Pre-change binary: `main @ b77f3298` sources via `git archive`, built
  in the lane's `.tmp/before` with `scripts/capped lake build golean`
  (log: exit 0). Host `linux/amd64`, 32 cores, shared with other lanes'
  builds (no timing numbers are claimed here).

## Files

| file | what | conclusion |
|---|---|---|
| `ci-diff.txt` | tail of `scripts/capped scripts/ci --diff` at the tip | see §Gate below |
| `twin-repin/structural-diff.txt` | JSON comparison old pin `4ee39f73…` vs fresh emit `d2bcb07b…` | `types` is a permutation of the 92 entries (36 moved; the pinned order had 12 order-contract violations, the new one 0); every other table byte-identical |
| `twin-repin/new-pin.sha256` | sha256 of the re-pinned `baselines/pins/twin-chdriver.wire.json` | `d2bcb07b…` |
| `choice-trace/` | `scripts/choice-trace-corpus` over the whole executable corpus × 6 streams with the PRE-change binary and with the tip binary, on the SAME (dependency-ordered) wires; `trace-diff.txt` = the a-series `trace-diff.sh` verdict | see §Readout identity below |
| `eval-tests.txt` | `gocore-eval-tests` output | 165 ok, 0 fail (12 new `C2:` pins) |
| `frontend-tests.txt` | `go test -v -run 'TypeDefOrder|TypeOrder|Determin' ./tools/nativefrontend` | all PASS |
| `lean-line-delta.txt` | `git diff --numstat` per Lean file vs `main` | GoLean/ +1763 −1466 (net +297); not a reduction, not claimed as one |

## Reproduction (from the worktree root, at the SHAs above)

```sh
scripts/capped lake build && scripts/capped lake build gocore-eval-tests
.lake/build/bin/gocore-eval-tests > docs/evidence/2026-09-05_c-arc-c2/eval-tests.txt 2>&1
GO111MODULE=off GOCACHE="$PWD/.tmp/go-build-cache" go test -v -run 'TypeDefOrder|TypeOrder|Determin' ./tools/nativefrontend
# twin re-pin (the check-frontend-pins assembly, then the JSON comparison the file's header names)
mkdir -p .tmp/twin/prog && for pkg in quorum raftpb tracker proto confchange raft; do cp -r raftsubject/$pkg .tmp/twin/prog/; done
for f in twin-lib.go twin-chdriver.go twin-chdriver-main.go; do cp tools/raftsubject/$f .tmp/twin/prog/; done
GO111MODULE=off go run ./tools/nativefrontend --dir .tmp/twin/prog --out .tmp/twin/twin.wire.json
# pre-change binary
mkdir -p .tmp/before && git archive b77f3298 | tar -x -C .tmp/before && (cd .tmp/before && scripts/capped lake build golean)
# readout identity + choice-trace delta (types consume nothing)
scripts/choice-trace-corpus --jobs 8 --out artifacts/choice-trace-before --golean .tmp/before/.lake/build/bin/golean --exclude goroutines/send-then-spin > artifacts/choice-trace-before.log 2>&1
scripts/choice-trace-corpus --jobs 8 --out artifacts/choice-trace-after  --golean .lake/build/bin/golean            --exclude goroutines/send-then-spin > artifacts/choice-trace-after.log 2>&1
docs/evidence/2026-09-03_hygiene-a-series/choice-trace/trace-diff.sh artifacts/choice-trace-before artifacts/choice-trace-after
# the gate
scripts/capped scripts/ci --diff
```

## Gate

GATE-TAIL-PLACEHOLDER

## Readout identity and the choice trace

TRACE-PLACEHOLDER

## Provenance

- The gate ruling and its confirmation are [USER]; this lane executed
  under the coordinator's relay ([AGENT]) and records the reading, not
  a ruling (`docs/2026-09-04_c-arc-gu-design.md` §0 convention).
- The twin re-pin is [AGENT] under the ruled gate; its reason is the
  gate's ("typeDefs dependency-ordered") and its structural diff is
  above.
- The reserved-prefix contract (`TypeEnv.reserved`) is an [AGENT]
  design decision inside G-C2, disclosed in the design note §2/§8 for
  the audit.
