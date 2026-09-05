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
| `eval-tests.txt` | `gocore-eval-tests` output at the audit-fix-round tip | 170 ok, 0 fail (12 `C2:` pins + 5 audit fix pins `C2/R1`, `C2/R2`) |
| `frontend-tests.txt` | the FULL `go test -v ./tools/nativefrontend` run with its command line in the header (audit fix R8; the first record was a 5-test `-run` subset) | 100 PASS, 0 FAIL, incl. the 9 `typeorder_test.go` tests |
| `corpus-slice.txt` | `scripts/coverage run --prefix structs/decl-order-reversed` at the audit-fix-round tip (R11 rows) | 4 PASS + 1 FAIL red-first on BUG-103 (`conversion-array-target`, `unsupported: conversion to Ty.array 3 (Ty.defined 2)`; gc 104) |
| `choice-trace/excluded.tsv` | the two rows excluded from the trace on both sides, each with its REASON (audit fix R8/R9) | `send-then-spin` (nonterm by design), `repeat-bound-refused` (16 MiB materialization; identity UNMEASURED, result gate-covered) |
| `lean-line-delta.txt` | `git diff --numstat` per Lean file vs `main` | GoLean/ +1763 −1466 (net +297); not a reduction, not claimed as one |

## Reproduction (from the worktree root, at the SHAs above)

```sh
scripts/capped lake build && scripts/capped lake build gocore-eval-tests
.lake/build/bin/gocore-eval-tests > docs/evidence/2026-09-05_c-arc-c2/eval-tests.txt 2>&1
GO111MODULE=off GOCACHE="$PWD/.tmp/go-build-cache" go test -v ./tools/nativefrontend
# twin re-pin (the check-frontend-pins assembly, then the JSON comparison the file's header names)
mkdir -p .tmp/twin/prog && for pkg in quorum raftpb tracker proto confchange raft; do cp -r raftsubject/$pkg .tmp/twin/prog/; done
for f in twin-lib.go twin-chdriver.go twin-chdriver-main.go; do cp tools/raftsubject/$f .tmp/twin/prog/; done
GO111MODULE=off go run ./tools/nativefrontend --dir .tmp/twin/prog --out .tmp/twin/twin.wire.json
# pre-change binary
mkdir -p .tmp/before && git archive b77f3298 | tar -x -C .tmp/before && (cd .tmp/before && scripts/capped lake build golean)
# readout identity + choice-trace delta (types consume nothing)
scripts/choice-trace-corpus --jobs 8 --out artifacts/choice-trace-before --golean .tmp/before/.lake/build/bin/golean --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused > artifacts/choice-trace-before.log 2>&1
scripts/choice-trace-corpus --jobs 8 --out artifacts/choice-trace-after  --golean .lake/build/bin/golean            --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused > artifacts/choice-trace-after.log 2>&1
docs/evidence/2026-09-03_hygiene-a-series/choice-trace/trace-diff.sh artifacts/choice-trace-before artifacts/choice-trace-after
# the gate
scripts/capped scripts/ci --diff
```

## Gate

`scripts/capped scripts/ci --diff` at the CLEAN tip `166244f7` (records
commit on top of code `3a229bae` + `f33d3092`): **RESULT: PASS**, every
step ok — core build warning-free; frontend pins ok (twin wire = the
re-pinned bytes `d2bcb07b…`); frontend unit tests ok; lowering-diagnostic
tables ok; eval tests 165 ok; differential `cases=3498 pass=3252 fail=246`,
baseline diff FULL 3498/3498 **no regression**; negative 394 match; the
differential record made on a clean tree (`git_dirty false`). ZERO
baseline drift beyond the twin pin: no result flip, no stage move outside
the one recorded stage ALTERNATION (`channels/select-select/beside-loop`,
`lean-observation|differential`, [USER]-ruled 2026-09-03 — the run
landed on its `lean-observation` member). Reconciler: 3 report-only
findings, 0 HIGH; C9 says what merge-protocol step 5a says — the wire
schema moved (`emit.go`/`NativeToIR.lean`), so the train runs `ci
--slow` and refreshes the certification record. Full tail:
`ci-diff.txt` (an earlier run at `3a229bae` failed ONLY the lowerdiag
vocabulary step — a refusal string's class — and is kept at the end of
the file).

## Readout identity and the choice trace

Both binaries traced the whole executable corpus × 6 streams on the SAME
wires (the tip frontend's, dependency-ordered; the old decoder is
order-agnostic): 3458 ids, 20749 (id,stream) lines each side, 37 frontend
refusals (identical sets), 2 rows EXCLUDED and recorded
(`choice-trace/excluded.tsv`): `goroutines/send-then-spin` (the a-series
precedent: nonterm=200 spins to the fuel cap) and
`strings/trimspace-repeat/repeat-bound-refused` (a RED-BY-DESIGN baseline
row that the gate stops at `LEAN_TIMEOUT_SECONDS=30s`; the tracer has no
timeout and ran its first stream for 30+ minutes under the old binary
before this lane stopped it — by PID — and excluded it on both sides).

`trace-diff.sh` verdict (`choice-trace/trace-diff.txt`, re-recorded in the
audit fix round from the SAME two artifact dirs after the script learned
to print BOTH sides' per-site totals untruncated — audit fix R8; the
verdict is unchanged): **20737 of 20749
lines byte-identical on every column including `obsHash`; the 12
differing lines are the 6 streams of two baseline-FAIL rows**
(`panic-recover/panic-defined-payload-methods/{error,stringer}`) whose
status is `unsupported` on BOTH binaries with identical consumption
columns — only the refusal MESSAGE changed, because it `repr`s the
payload's dynamic type: `Ty.defined { key := "main.payloadCode" }` before,
`Ty.defined 2` after (`choice-trace/delta-observations.txt`; design note
§4). Per-site consumption totals identical (`l1Sched=9443 appendSpill=4868
postOp=4534 backEdge=2404 mapIter=1307 l5ExitWindow=325 tryLock=101
nilValueMethodText=84 l2Entry=24 l4Waiter=22 l2Arrival=3` on both sides):
the choice trace has ZERO delta — types consume nothing. Menu-invariant
violations 0 and self-check alarms 0 on both sides; the 6 driver-agreement
MISMATCH lines (`builtins/float-bits/roundtrip-payloads`) and the 1 tracer
ERROR (`arrays/materialization-budget/over-budget`, BUG-078's DESIGNED
decode-time refusal — the tracer has no program to run) are IDENTICAL on
both binaries — pre-existing on `main`, not this lane's. The mismatch is a
tracer fail-open (the enumerator's refusal compared with an EMPTY output
field), ROWED AND FIXED by the `c-arc-b4` lane's audit fix round
(`docs/2026-09-05_c-arc-b4-design.md` §7 item 6; `TODO.md` C-arc section) —
cross-referenced, not duplicated (audit fix R7; design note §7). The
whole-corpus identity claim is MINUS the excluded `repeat-bound-refused`
row (design note §7, audit fix R9).

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
