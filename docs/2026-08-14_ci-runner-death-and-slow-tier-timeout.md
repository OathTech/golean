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

**Verdict: platform-side VM shutdowns, not the code — twice.** Attempt 2
(same commit, untouched, started 21:41 UTC, Azure centralus vs attempt 1's
westus3) died again in the SAME phase — ~7.5 min into the proofs build —
but with grace this time: `scripts/ci` exited 143 (SIGTERM), the log ends
with the verbatim runner error "The runner has received a shutdown
signal. This can happen when the runner service is stopped, or a manually
started runner is canceled.", and the agent still completed the job and
uploaded logs. A clean external TERM is not an OOM kill (that would be
SIGKILL/137 inside the step) and not a gate failure (a failed lake build
surfaces as a red `scripts/ci` summary exiting 1) — consistent with the
resource refutations above. Two shutdowns in different regions on the
same afternoon (the morning nightly and the 08-12 lane pushes were fine;
githubstatus.com showed no open incident at 21:19 UTC) reads as a
hosted-runner capacity/maintenance event. If the post-merge push dies the
same way, the next probe is a `workflow_dispatch` on a larger-runner
label (different VM pool).

**Attempt 2 also falsified a load-bearing assumption:** plain
`actions/cache@v4` does NOT save on a failed job — its post-step ran only
on success, so "Post Cache" was skipped and the failed run banked
nothing. That is why retries never converge on a failing state. Fixed in
this lane: the cache is split into `actions/cache/restore@v4` + an
explicit `actions/cache/save@v4` at the end of the job with
`if: always()`, AND saved keys carry a per-attempt suffix
(`-r<run_id>.<attempt>`, audit F3: with a plain source-hash key a retry
exact-hits the failed attempt's entry and convergence stops after one
generation), guarded so a run whose gate never started does not bank a
thin entry (audit F4). A red-but-alive gate now saves its build progress
and each retry resumes from the previous attempt's. (A runner that dies
outright still saves nothing — no step outlives the VM.)

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
   a diagnostics step (`nproc; free -h; df -h /; swapon --show`, placed
   before the cache restore) so surviving runs record the machine shape,
   and each gate step now runs inside a SYSTEM cgroup scope
   (`sudo systemd-run --scope`, `MemoryMax` = VM RAM − 1.2 G,
   `MemorySwapMax=0`). Hosted runners have no systemd *user* bus for
   `scripts/capped` itself, but they do have passwordless sudo and a
   system manager — and the cap is PROVEN, not asserted (audit F2): the
   workflow passes `GOLEAN_CAPPED=1` + the real size, routing `scripts/ci`
   through `capped`'s untrusted-token readback, which refuses (exit 3) if
   systemd accepted-and-ignored the property. Passing the real size also
   feeds ci's cap-scaled `LEAN_NUM_THREADS` heuristic (audit F6). The old
   workflow comment's claim — "if a build eats the runner the job just
   fails, which is the outcome we wanted anyway" — is disproved: the job
   does NOT fail; the VM dies with zero logs and no cache save. Under the
   cap, a future memory blowout of OURS kills the build instead: red job,
   logs uploaded, progress banked by the `always()` save step. To be
   explicit about scope (audit F5): the cap does NOT prevent the
   platform-side shutdowns actually observed — nothing in a workflow
   does; it removes the one death mode we could cause ourselves and makes
   every surviving failure legible. An `always()` dmesg step
   discriminates a cgroup OOM kill from a semantic failure (audit
   F1b/F7). Recorded cost (audit F1): `MemorySwapMax=0` forbids the ~4 GB
   of swap the old uncapped runs could thrash into, and the cold 2-thread
   runner peak is unmeasured — if a legitimate gate peak exceeds
   RAM − 1.2 G, the first post-merge run goes red at the cgroup; the
   remedy is revisiting the constant with the diagnostics numbers, never
   deleting the readback.

## Failure 2: nightly 31669436263 (2026-08-13) — google-search membership flake

**Symptom.** Baseline drift, exactly one row:
`imported-goose/channel/google-search baseline[PASS/membership] ->
now[FAIL/membership]`. The next nightly (2026-08-14) ran the SAME commit
(`ba6398ab`) and passed — a flake, on the lane whose whole meaning is
soundness (observed ∈ modeled), so worth pinning down precisely.

**Cause (best explanation): the slow-tier re-enumeration straddles the
enumerator timeout.** Under `--slow`, the row's `tier=slow` certified set
is fully re-enumerated: 39,976,295 pool steps, measured **94 s
single-core on the dev box** — reproducing the certified 6-member set
(all arrival-order permutations) exactly. The enumeration ran under the
shared `LEAN_ENUM_TIMEOUT_SECONDS=300` wall-clock guard; a hosted 2-core
runner plausibly lands near ~300 s (ESTIMATED, not measured — the ~300 s
figure is inferred from the flake itself: >300 s on 08-13, <300 s on
08-14), so ordinary runner variance flips the case. Corroboration: the
08-13 runner was ~7 % slower than the 08-14 runner across the whole
differential (30m05s vs 28m14s for 1483 cases); the two runs' pass/fail
counts differ by exactly this one case; and the enumeration is a
deterministic DFS over a wire-hash-pinned input, so a *semantic* failure
could not flip between two runs of the same commit. The one
load-dependent alternative the CI logs could not exclude (the 08-13
detail never said which guard fired) is an enumerator OOM kill — exit
137 rather than the wrapper's 124 — which the new exit-code naming makes
distinguishable if it ever recurs. The Go-sampling half (ten sub-second
`go run`s under a 30 s cap each) is not a plausible flake source.
Nothing semantic moved; the certified set is intact.

**Fix (this lane):**

- `LEAN_ENUM_SLOW_TIMEOUT_SECONDS` (default 1200 s) in
  `scripts/diff-coverage`, used for the enumeration exactly when
  `tier == slow`; quick-lane enumerations keep 300 s. Still a hard bound —
  fail-closed is unchanged, the guard just no longer sits inside normal
  runner variance (~4× headroom over the ~300 s estimate; if the true
  contended runner cost is higher the real margin is smaller — the number
  to trust is the 94 s single-core measurement, not the estimate).
- Timeouts are now NAMED in the FAIL detail ("enumerator TIMED OUT after
  Ns"; other failures carry their exit code) — in ALL three enumerating
  lanes (membership, confluent, racy; the empty-detail nit was originally
  recorded against the confluent lane in `docs/goose-parity-parked.md`,
  muxer/make-greeting, and is closed there too). The 08-13 flake was
  undiagnosable from CI logs partly because the generic "enumerator
  failed" detail with an empty stats file never said which guard fired.
- All five timeout knobs are validated as positive integers at startup
  (audit F1, 2026-08-15): perl's `alarm` numifies a non-numeric value to
  0, which CANCELS the alarm — so `LEAN_ENUM_SLOW_TIMEOUT_SECONDS=20m`
  or the repo's `=none` idiom would have silently disabled the guard.
  Malformed values now exit 2 with nothing published.
- The measured cost is recorded in the row's `cases.tsv` comment,
  mirroring `rwmutex-order`'s convention.
- Composition caveat, recorded: per-row budgets do not compose with the
  job-level `timeout-minutes: 120`. Today's two slow rows run
  concurrently under the pool and fit comfortably; if slow rows ever
  multiply past core count, a hung enumeration could push the nightly
  into the job timeout, which kills the step with nothing published —
  re-check this arithmetic when adding slow rows.

## Pre-merge audit record (2026-08-15: two Opus reviewers, findings verified then fixed)

**Reviewer A (gate half, scripts/diff-coverage + corpus row).** F1
(confirmed by probe): timeout knobs were silently disableable — perl
`alarm` numifies `20m`/`none` to 0, which CANCELS the guard; fixed with
startup validation of all five knobs, exit 2 loud, after the
gate-integrity `rm`. F4: timeout naming extended to the confluent and
racy lanes (the nit was originally recorded against confluent). F2/F5:
flake diagnosis restated as best-explanation with its evidence basis;
~300 s runner figure marked estimated; composition caveat recorded. F3
(partially refuted on verification): the parked goose-parity rows are
confluent-lane, their 300 s bound untouched — clarifying addendum +
stale-figure corrections added to the parked note. Cleared explicitly:
slow-budget scoping is exactly tier=slow re-certification; no
non-timeout failure can become a pass; the comment block is safe for
every cases.tsv consumer; the certified record is untouched.

**Reviewer B (workflow half).** F2: the cap was asserted without a
readback — the exact fail-open `scripts/capped` was written against;
fixed by passing `GOLEAN_CAPPED=1` + the real size so ci re-execs
through capped's readback inside the scope. F6: `GOLEAN_MEM_MAX=none`
fed the cap-scaled parallelism heuristic a lie; fixed by the same
change. F3: cache convergence stopped after one generation (retry
exact-hits the failed attempt's entry, save skipped); fixed with
per-attempt key suffixes. F4: an early setup failure could bank a thin
poisoning entry; fixed with the skipped-gate save guard. F5/F7: comment
overclaims (cap framed as fixing the observed platform-side deaths;
diagnostics "before anything heavy" while sitting after the restore)
fixed; diagnostics moved pre-restore; `always()` dmesg OOM-discriminator
step added (also answers F1b: a cgroup kill in the differential would
otherwise read as baseline drift). F8: env-allowlist drops were
invisible; an in-scope probe line (user/pwd/go/lake versions) now prints
from inside the wrapper. F1 (accepted, not fully closeable offline): the
cap value is a hard ceiling derived from an unmeasured cold-runner peak
and removes the swap old runs could thrash into — mitigated with a
`free -m` sanity guard, the recorded remedy path, and the diagnostics
numbers to re-derive the constant from real runs. Cleared explicitly: no
greenwash path through the wrapper; no dropped env var changes today's
gate behavior; cache paths/keys in lockstep; sudo/runuser/PAM mechanics
probed on a same-family Ubuntu 24.04 box.

**Residual, observable only on a real runner:** the VM's actual
`free`/swap numbers, the cold 2-thread gate peak, whether the image's
system manager honors `MemoryMax` on transient scopes (the readback now
refuses if not), and `actions/cache/save` warning-vs-failure semantics.
The first post-merge push is the live validation for all four.

## Follow-ups / open items

- **The lever-5 cache is still unseeded** (both attempts died before any
  save; the frozen 2026-07-21 entry is still the only one). The first
  COMPLETED run after this lane merges — even a red one, thanks to the
  always() save — seeds it; worth one glance at the cache list
  (`gh api repos/OathTech/golean/actions/caches`) to confirm cycling.
- If the post-merge push dies the runner-shutdown way again, probe with
  `workflow_dispatch` on a larger-runner label (different VM pool), and
  the new diagnostics step gives each attempt's machine shape.
- `confluent`/`racy` lane enumerations still run under the 300 s budget;
  neither lane has a slow-tier row today, so they were left untouched
  (scope discipline). If one ever grows past ~100 s single-core, give it
  the same treatment.
