# Atomics arc wave 1 — TSan probes, membership records, gate tail (2026-09-03)

[AGENT] evidence directory for `docs/2026-09-03_atomics-w1-design.md`
(the `atomics-w1` lane; Q-ATOMIC RULED [USER] 2026-09-02 option A′,
`docs/2026-08-31_qrow-rulings.md` row 2). Convention:
`docs/evidence/README.md` (all eight rules below). Consuming docs: the
design note (§4 cites `probes/tsan-runs/`, §3 cites `mp-litmus/`);
`GoLean/GoCore/Race.lean`'s section "sync/atomic — the per-address
clocks and access kinds" cites the probe subjects by name.

## What is here

- `probes/tsan/main.go` — 22 probe subjects, one per claim of the
  detector derivation table (Race.lean; design note §4), a twin for
  EVERY `race/atomics-{free,misuse}` corpus row (audit fix H3):
  atomic↔atomic contention, plain-beside-atomic misuse (write vs Add,
  read vs Store / Swap / FAILED CAS, struct copy vs typed Add), the
  publish idioms (store-release / load-acquire, RMW-acquire, CAS
  success-acquire, the ISOLATED CAS failure-acquire — H5), sibling
  words/fields, the store-OVERWRITE discriminator, the
  record-then-acquire isolating shapes (`plainThenStoreVsLate{Add,
  Swap,CasSuccess,CasFail,Load}` — L3f) and their confounded spin twins
  (kept, headers corrected), the nil address. Each header states the EXPECTED `-race`
  verdict and why. NOT corpus cases (`scripts/coverage-manifest` does
  not scan this tree); the shapes that became corpus rows live in
  `Corpus/coverage/exec/race/atomics-{free,misuse}/`.
- `probes/run-tsan.sh` — the runner: `go build -race`, N runs per
  subject at GOMAXPROCS 1 and 8, RACE / green / other counts ("other"
  = non-zero exit with no race report and no recovered-panic line —
  the 20 s timeout in practice). The `-race` binary is built under
  `$TMPDIR`, never in this directory (L3d: the first round committed
  a 3 MB `probe.race` here; removed).
- `probes/tsan-runs/summary.tsv` — the 22-subject run of the audit fix
  round (N=20); `summary-late.tsv` — the first round's run of the two
  original isolating shapes (N=20), kept as the earlier record;
  `<subject>.procs<P>.first.txt` — the first transcript per cell;
  `go-version.txt` — the toolchain line.
- `mp-litmus/` — the `sync/atomic-frontier/mp-litmus` membership
  record at the flip (`observations.txt` = the enumerated set,
  `enum-stats.txt`, `samples.txt`): exactly {0, 1, 11}.
- `gate-tail.txt` — the `scripts/ci --diff` tail at the CLEAN
  committed tip of the audit fix round (its header names the SHA), plus
  the tail of the fast gate that followed; `gate-tail-first-run.txt` —
  the FIRST full run's tail, made on the DIRTY working tree at base
  main `b5abacc1` (`latest.meta.tsv`: git_dirty=true) BEFORE the
  wave-1 commit — kept as the record of what the re-pin was derived
  from (audit fix H1 corrected the first README's "at the branch tip"
  claim about it). `baseline-drift.txt` — that first run's drift list
  (every moved row with its reason).
- AUDIT FIX H2 — the reconciler line in the first run's tail reads "6
  finding(s), 3 HIGH": that tail was captured at an INTERMEDIATE tree,
  after the baseline rows were re-pinned but before the header and the
  ledger §8 arithmetic were re-derived. The three HIGHs were C1H (the
  baseline's `# cases:` header still said 2580 / 2403 / 177 against
  2626 / 2453 / 173 rows), C4 (the language-coverage ledger §8 "All
  numbers at the current tracked baseline" line still said 2580 / 2403
  / 177) and C4 (§8's red-bucket total 177 vs 173 baseline FAILs). All
  three were fixed in the same wave-1 commit `7252b593` by re-deriving
  the header (with its derivation line) and §8 (§8d, the Q-* bucket
  14 → 10, total 173); `tools/reconcile-records` at that commit and at
  this round's tip reports 0 HIGH (3 pre-existing MEDIUMs: C13 version
  mentions, C5 the FR-7 `=` citation identical on main, C9 the
  certified-set wire sha). The clean-tip `gate-tail.txt` supersedes the
  first run's reconciler line; both are kept.

## Reproduction (repo root)

```
# probes (writes ONLY under the evidence dir's tsan-runs/)
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
- Commit: the probe runs and the membership record were made on the
  lane's DIRTY working tree (wave 1: before commit `7252b593`, machine
  files at their final content; the audit fix round's probe run: on the
  round's working tree before its commit, `main.go` at its committed
  content) — recorded per rule 4's dirty-tree note. The FIRST full
  `ci --diff` (`gate-tail-first-run.txt`) ran on the dirty tree at base
  main `b5abacc1`; the CLEAN-tip run is `gate-tail.txt`, whose header
  names the SHA (audit fix H1).
- Host: linux/amd64, 32-core shared agent box under concurrent lane
  load. The GOMAXPROCS=1 timeouts of the spin subjects (below) are
  scheduler-load-sensitive numbers.

## Measured (conclusions the design note relies on)

`summary.tsv` — the audit-fix-round run of the full 22-subject family
(N=20 per cell, GOMAXPROCS 1 / 8; `race/green/other`). The first
round's 13-subject run (numbers in the previous README, superseded) and
the auditor's independent re-measurement are quoted for the
schedule-DEPENDENT subjects so the run-to-run spread is visible.

| subject | corpus twin | expected | measured @1 ; @8 |
|---|---|---|---|
| contend | race/atomics-free/atomic-vs-atomic | green, every run | 0/20/0 ; 0/20/0 |
| plainWriteVsAdd | race/atomics-misuse/plain-write-vs-add | RACE, every run | 20/0/0 ; 20/0/0 |
| plainReadVsStore | race/atomics-misuse/plain-read-vs-store | RACE, every run | 20/0/0 ; 20/0/0 |
| plainReadVsSwap | race/atomics-misuse/plain-read-vs-swap | RACE, every run | 20/0/0 ; 20/0/0 |
| plainReadVsLoad | race/atomics-free/plain-read-vs-load | green, every run | 0/20/0 ; 0/20/0 |
| plainReadVsFailedCas | race/atomics-misuse/plain-read-vs-failed-cas | RACE, every run (a failed CAS is an atomic WRITE) | 20/0/0 ; 20/0/0 |
| publish | race/atomics-free/publish-acquire | green, every run | 0/20/0 ; 0/20/0 |
| casSpinPublish | — (the SUCCESS acquire; header corrected) | green, every run | 0/20/0 ; 0/20/0 |
| casFailureAcquireIsolated | race/atomics-free/cas-failure-acquires (H5 shape) | green, every run | 0/20/0 ; 0/20/0 |
| rmwPublish | race/atomics-free/rmw-acquire | green, every run | 0/20/0 ; 0/20/0 |
| siblingWords | race/atomics-free/sibling-words | green, every run | 0/20/0 ; 0/20/0 |
| storeOverwrite | — (discriminator) | SCHEDULE-DEPENDENT: RACE (A-then-B store, reader missed the 1), green (reader caught the intermediate 1 — acquires A's clock directly; NOT merge evidence), timeout "other" (B-then-A: flag stuck at 1 BY CONSTRUCTION) | this run 14/0/6 ; 6/14/0 — first run 9/0/11 ; 3/17/0 — auditor 15/0/5 ; 5/14/1. A merge model would show 0 RACE; the RACE cell's presence is the discriminator |
| plainThenStoreVsAdd (spin) | — | SCHEDULE-DEPENDENT, racy by go_mem (spin RMW between the plain write and the store) | 1/19/0 ; 20/0/0 — first run 2/18/0 ; 20/0/0 — auditor 10/10 @8 |
| plainThenStoreVsLoad (spin) | — | SCHEDULE-DEPENDENT, racy by go_mem (spin LOAD between the plain write and the store); first header predicted green — corrected | 0/20/0 ; 19/1/0 — first run 0/20/0 ; 20/0/0 |
| plainThenStoreVsLateAdd | — (isolating shape) | RACE, every run (record-then-acquire on the RMW) | 20/0/0 ; 20/0/0 |
| plainThenStoreVsLateSwap | — | RACE, every run | 20/0/0 ; 20/0/0 |
| plainThenStoreVsLateCasSuccess | — | RACE, every run | 20/0/0 ; 20/0/0 |
| plainThenStoreVsLateCasFail | — | RACE, every run (the failed CAS's atomic-write record precedes its acquire) | 20/0/0 ; 20/0/0 |
| plainThenStoreVsLateLoad | — | green, every run (a Load acquires THEN records) | 0/20/0 ; 0/20/0 |
| nilAddress | atomics/ops/nil-address | the ordinary nil-deref panic, no race report | 0/20/0 ; 0/20/0 (`recovered: true`) |
| structCopyVsTypedAdd | race/atomics-misuse/struct-copy-vs-typed-add | RACE, every run | 20/0/0 ; 20/0/0 |
| typedSiblingField | race/atomics-free/typed-sibling-field | green, every run | 0/20/0 ; 0/20/0 |

Scope of the "gc `-race` red/green 20/20 at GOMAXPROCS 1 and 8" claims
made in the design note, the baseline header and the corpus headers:
they hold for exactly the shapes with a probe twin above — now every
`race/atomics-misuse` row (5/5) and every `race/atomics-free` row (7/7;
`publish-acquire`/`rmw-acquire`/`cas-failure-acquires` through their
spin-form twins, whose non-spin corpus forms are membership rows). The
schedule-dependent subjects are reported as ranges, never as "N/N".

Conclusion: every row of the derivation table's realized set matches
gc's `-race` in both directions on these shapes; the store OVERWRITE
(not a merge) is the realization; a failed CAS is an atomic write; the
record-then-acquire over-refusal vs literal go_mem holds for Add, Swap
and BOTH CAS outcomes (the Late* family, 20/20 each) and not for Load.
The two spin "record-then-acquire" probes turned out NOT to isolate the
order (they are go_mem-racy on their own), which the corrected headers
and the Late* shapes record — an [AGENT] prediction falsified and kept
visible, not deleted.
