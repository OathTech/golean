# Atomics arc wave 1 — TSan probes, membership records, gate tail (2026-09-03)

[AGENT] evidence directory for `docs/2026-09-03_atomics-w1-design.md`
(the `atomics-w1` lane; Q-ATOMIC RULED [USER] 2026-09-02 option A′,
`docs/2026-08-31_qrow-rulings.md` row 2). Convention:
`docs/evidence/README.md` (all eight rules below). Consuming docs: the
design note (§4 cites `probes/tsan-runs/`, §3 cites `mp-litmus/`);
`GoLean/GoCore/Race.lean`'s section "sync/atomic — the per-address
clocks and access kinds" cites the probe subjects by name.

## What is here

- `probes/tsan/main.go` — 15 probe subjects, one per claim of the
  detector derivation table (Race.lean; design note §4): atomic↔atomic
  contention, plain-beside-atomic misuse (write vs Add, read vs Store,
  read vs FAILED CAS, struct copy vs typed Add), the publish idioms
  (store-release / load-acquire, RMW-acquire, CAS-spin), the
  store-OVERWRITE discriminator, the record-then-acquire isolating
  shapes (`plainThenStoreVsLate{Add,Load}`) and their confounded spin
  twins (kept, headers corrected), the nil address, the typed
  sibling-field control. Each header states the EXPECTED `-race`
  verdict and why. NOT corpus cases (`scripts/coverage-manifest` does
  not scan this tree); the shapes that became corpus rows live in
  `Corpus/coverage/exec/race/atomics-{free,misuse}/`.
- `probes/run-tsan.sh` — the runner: `go build -race`, N runs per
  subject at GOMAXPROCS 1 and 8, RACE / green / other counts ("other"
  = non-zero exit with no race report and no recovered-panic line —
  the 20 s timeout in practice).
- `probes/tsan-runs/summary.tsv` — the 13-subject run (N=20);
  `summary-late.tsv` — the two isolating shapes (N=20), run after the
  first run's headers were corrected (see "Measured" below);
  `<subject>.procs<P>.first.txt` — the first transcript per cell;
  `go-version.txt` — the toolchain line.
- `mp-litmus/` — the `sync/atomic-frontier/mp-litmus` membership
  record at the flip (`observations.txt` = the enumerated set,
  `enum-stats.txt`, `samples.txt`): exactly {0, 1, 11}.
- `gate-tail.txt` — the `scripts/ci --diff` tail at the branch tip;
  `baseline-drift.txt` — the re-pin's drift list (every moved row with
  its reason).

## Reproduction (repo root)

```
# probes (writes ONLY under the evidence dir's tsan-runs/)
docs/evidence/2026-09-03_atomics-w1/probes/run-tsan.sh 20
SUBJECTS="plainThenStoreVsLateAdd plainThenStoreVsLateLoad" \
  SUMMARY=docs/evidence/2026-09-03_atomics-w1/probes/tsan-runs/summary-late.tsv \
  docs/evidence/2026-09-03_atomics-w1/probes/run-tsan.sh 20
# the litmus membership record
scripts/capped scripts/coverage run --prefix sync/atomic-frontier/mp-litmus
cp artifacts/coverage/membership/sync/atomic-frontier/mp-litmus/{observations,enum-stats,samples}.txt \
   docs/evidence/2026-09-03_atomics-w1/mp-litmus/
# the gate
scripts/capped scripts/ci --diff
```

## Toolchain, commit, host

- Go: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`;
  `probes/tsan-runs/go-version.txt`). The `-race` runtime is the
  toolchain's `race_linux_amd64.syso` (LLVM compiler-rt TSan, Go glue
  `tsan_go.cpp` — cited by name in Race.lean; not vendored).
- Lean: `leanprover/lean4:v4.32.2` (`lean-toolchain`); the machine
  binary is `.lake/build/bin/golean` built from this tree.
- Commit: the probe run and the membership record were made on the
  lane's working tree BEFORE its final commit (the machine files were
  at their final content; docs were still being written — recorded
  here rather than re-run, per rule 4's dirty-tree note); the gate tail
  names the SHA it ran at.
- Host: linux/amd64, 32-core shared agent box under concurrent lane
  load. The GOMAXPROCS=1 timeouts of the spin subjects (below) are
  scheduler-load-sensitive numbers.

## Measured (conclusions the design note relies on)

`summary.tsv`, N=20 per cell, GOMAXPROCS 1 / 8:

| subject | expected | measured (race/green/other @1 ; @8) |
|---|---|---|
| contend | green | 0/20/0 ; 0/20/0 |
| plainWriteVsAdd | RACE | 20/0/0 ; 20/0/0 |
| plainReadVsLoad | green | 0/20/0 ; 0/20/0 |
| plainReadVsFailedCas | RACE (a failed CAS is an atomic WRITE) | 20/0/0 ; 20/0/0 |
| publish | green | 0/20/0 ; 0/20/0 |
| casSpinPublish | green | 0/20/0 ; 0/20/0 |
| rmwPublish | green | 0/20/0 ; 0/20/0 |
| storeOverwrite | RACE on the A-store-then-B-store schedules (overwrite drops A's clock; a merge model would be green) | 9/0/11 ; 3/17/0 — the discriminator fires; the 11 "other" at GOMAXPROCS=1 are 20 s timeouts (the reader's tight atomic-load spin starves the writers under the race runtime's un-preemptible atomic stubs) |
| plainThenStoreVsAdd (spin) | header first said RACE-from-record-order; CORRECTED: racy by go_mem on executions where a spin RMW lands between A's plain write and its store | 2/18/0 ; 20/0/0 |
| plainThenStoreVsLoad (spin) | header first said green; CORRECTED: racy by go_mem for the same reason (a spin LOAD between the plain write and the store) | 0/20/0 ; 20/0/0 — the measurement corrected the prediction |
| nilAddress | the ordinary nil-deref panic, no race report | 0/20/0 ; 0/20/0 (recovered: true) |
| structCopyVsTypedAdd | RACE | 20/0/0 ; 20/0/0 |
| typedSiblingField | green | 0/20/0 ; 0/20/0 |

`summary-late.tsv` (the isolating shapes, sleep-based, N=20):

| subject | expected | measured (race/green/other @1 ; @8) |
|---|---|---|
| plainThenStoreVsLateAdd | RACE (TSan records the RMW's atomic write BEFORE acquiring — the over-refusal vs literal go_mem the machine shares) | 20/0/0 ; 20/0/0 |
| plainThenStoreVsLateLoad | green (a Load acquires THEN records) | 0/20/0 ; 0/20/0 |

Conclusion: every row of the derivation table's realized set matches
gc's `-race` in both directions on these shapes; the store OVERWRITE
(not a merge) is the realization; a failed CAS is an atomic write. The
two spin "record-then-acquire" probes turned out NOT to isolate the
order (they are go_mem-racy on their own), which the corrected headers
and the late shapes record — an [AGENT] prediction falsified and kept
visible, not deleted.
