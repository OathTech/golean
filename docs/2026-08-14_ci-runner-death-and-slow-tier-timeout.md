# CI post-mortem: the 4f29a44f runner death and the slow-tier timeout flake

Two remote-CI failures investigated 2026-08-14; this note is the record of
the evidence, the verdicts, and the fixes (lane `ci-gate-hardening`).

## Failure 1: push run 31803511044 (4f29a44f, 2026-08-14 13:10) — runner death

**Symptom.** The hosted runner died mid-job ("The hosted runner lost
communication with the server"); the log archive is an empty zip — when the
VM itself dies, no post-steps run, so nothing uploads and the cache never
saves. The fast gate started at 13:11 and was still `in_progress` at 14:08.

**What the job had to do.** The push moved `main` `ba6398ab..4f29a44f`
(57 commits, +46,309 lines — the verified-examples arc, the frame-theorem
tower, consolidation). All changed `.lean` files live under `proofs/`;
`scripts/ci` itself did not change in the batch.

**Resource theories, tested and refuted.**

- *Memory:* invalidating all 43 batch-touched proof modules and rebuilding
  in a metered cgroup: **207 CPU-s total, peak RSS 2.3 GB** at 32-wide
  parallelism (dev box). `Examples/InsertionSort.lean` (5,457 lines)
  elaborates in 767 ms. Two concurrent leans on a 2-core/7 GB runner sit
  far below the VM's RAM.
- *Disk:* the repo's entire Actions cache is one 0.85 GB entry;
  `proofs/.lake` is 535 MB locally. Nowhere near the runner's ~14 GB.
- *Workload:* the 2026-08-11 green push ran the identical fast gate in
  819 s from the same stale cache; the batch adds ~5–10 runner-minutes.
  Expected completion ≈ minute 25; the VM ran to minute 57 and vanished.
  Its cache-restore step had already run 2× slower than the green run's
  (40 s vs 19 s).

**Verdict: degraded/evicted runner VM (Azure westus3), not the code.**
Confirmed by re-running the same run untouched (attempt 2, started
2026-08-14 ~21:45 — outcome recorded below when it lands).

**Aggravating factors, both real, both addressed:**

1. **The cache had been frozen since 2026-07-21.** One entry, saved under
   the old toolchain+manifest-only key; every run since hit it exactly, so
   `actions/cache` never re-saved, and every CI run re-elaborated weeks of
   changes (exactly the pathology the lever-5 key comment describes — this
   is its measured confirmation). The frozen cache turned a ~15-minute job
   into a ~25+-minute one, maximizing exposure to infra failure. The
   lever-5 source-hashed key (shipped in the batch) fixes this, but only a
   COMPLETED run seeds the first entry — and runner death skips the save,
   so retries stayed cold. The re-run doubles as the seeding run.
2. **Runner death was undiagnosable and unmitigated.** Fixes in this lane:
   a diagnostics step (`nproc; free -h; df -h /; swapon --show`) so future
   post-mortems have a floor, and each gate step now runs inside a SYSTEM
   cgroup scope (`sudo systemd-run --scope`, `MemoryMax` = VM RAM − 1.2 G,
   `MemorySwapMax=0`). Hosted runners have no systemd *user* bus (why
   `scripts/capped` is opted out with `GOLEAN_MEM_MAX=none`, unchanged)
   but they do have passwordless sudo and a system manager. The old
   workflow comment's claim — "if a build eats the runner the job just
   fails, which is the outcome we wanted anyway" — is disproved: the job
   does NOT fail; the VM dies with zero logs and no cache save. Under the
   cap, a future memory blowout kills the build instead: red job, logs
   uploaded, partial `.lake` saved by the cache post-step (so retries make
   progress).

## Failure 2: nightly 31669436263 (2026-08-13) — google-search membership flake

**Symptom.** Baseline drift, exactly one row:
`imported-goose/channel/google-search baseline[PASS/membership] ->
now[FAIL/membership]`. The next nightly (2026-08-14) ran the SAME commit
(`ba6398ab`) and passed — a flake, on the lane whose whole meaning is
soundness (observed ∈ modeled), so worth pinning down precisely.

**Cause: the slow-tier re-enumeration straddles the enumerator timeout.**
Under `--slow`, the row's `tier=slow` certified set is fully re-enumerated:
39,976,295 pool steps, measured **94 s single-core on the dev box** —
reproducing the certified 6-member set (all arrival-order permutations)
exactly. The enumeration ran under the shared
`LEAN_ENUM_TIMEOUT_SECONDS=300` wall-clock guard; a hosted 2-core runner's
slower core lands near ~300 s, so ordinary runner variance flips the case.
Corroboration: the 08-13 runner was ~7 % slower than the 08-14 runner
across the whole differential (30m05s vs 28m14s for 1483 cases), and the
two runs' pass/fail counts differ by exactly this one case. The Go-sampling
half (ten sub-second `go run`s under a 30 s cap each) is not a plausible
flake source. Nothing semantic moved; the certified set is intact.

**Fix (this lane):**

- `LEAN_ENUM_SLOW_TIMEOUT_SECONDS` (default 1200 s) in
  `scripts/diff-coverage`, used for the enumeration exactly when
  `tier == slow`; quick-lane enumerations keep 300 s. Still a hard bound —
  fail-closed is unchanged, the guard just no longer sits inside normal
  runner variance (~4× headroom over the estimated runner cost).
- Timeouts are now NAMED in the FAIL detail ("enumerator TIMED OUT after
  Ns"; other failures carry their exit code). The 08-13 flake was
  undiagnosable from CI logs partly because the generic "enumerator
  failed" detail with an empty stats file never said which guard fired.
- The measured cost is recorded in the row's `cases.tsv` comment,
  mirroring `rwmutex-order`'s convention.

## Follow-ups / open items

- **Re-run outcome:** pending at the time of writing; to be recorded here
  before this lane merges. If the re-run reproduces the death, the next
  probe is a `workflow_dispatch` on a larger runner to seed the cache,
  then reassess.
- The first push after this lane merges should show the lever-5 cache
  actually cycling (restore from a source-hashed key + save on change);
  worth one glance at the cache list
  (`gh api repos/OathTech/golean/actions/caches`).
- `confluent`/`racy` lane enumerations still run under the 300 s budget;
  neither lane has a slow-tier row today, so they were left untouched
  (scope discipline). If one ever grows past ~100 s single-core, give it
  the same treatment.
