[AGENT] coordinator, merge train r32 (2026-09-15): moved here from the lane worktree root so that the tracked root `HANDOFF.md` on main is left unchanged by this lane; content below verbatim.

# HANDOFF — lane `records/bug090-rediagnosis-0911` (records only)

[AGENT] 2026-09-11. Branch `records/bug090-rediagnosis-0911` off main
`a461ed8b`. Authority: [USER] Mike 2026-09-11, «Great, go ahead and land
this, then launch the lanes» (relayed), on `docs/2026-09-11_review-
dispositions.md` §4 step 2(i). No fix, no runtime edit, no baseline change,
no lake build (the primary's certified binary was copied and run read-only;
sha256 `18beb979fbcc90fe3f13d5f659ed27c515c25840e3ad37db80c717c2bfea7ba4`).
Not merged, not pushed.

## What landed (this branch)

- `docs/2026-09-11_bug090-rediagnosis.md` — the note: scope, measurement
  tables, the cost model per operation kind, the refuted hypotheses, code
  anchors (file:line at `a461ed8b`, verified), C1 requirements.
- `docs/BUGS.md` BUG-090 — stale association-list diagnosis retired under a
  banner (kept verbatim), measured re-diagnosis and revised plan appended;
  Status/Pinned-by/Cases lines untouched.
- `docs/evidence/2026-09-11_bug090-rediagnosis/` (137,655 tracked bytes):
  README (provenance, scope, reproduction), 20 probe sources, `run-probes.py`,
  `ipsample.py` (ptrace leaf-IP sampler; `perf` is refused on this box),
  `results.json` (68 points × 3 runs), `steps.json`, `summarize.py` +
  generated `summary.md`, five `profile-*.json`.

## The headline cost model (three sentences)

(A) A write through a field/index path rewrites and re-normalizes its whole
ROOT cell, and `normalizeListWith` rebuilds arrays as `#[head] ++ tail`, so
one write into an m-element root costs ≈1.1 ns × m² (109 ms at m = 10⁴) and
n in-place appends at capacity ≈ n are cubic — the review's 4,000-append loop
completes in 31.6 s, with ≥ 83 % of samples in the array rebuild and `stepFn`
at 0 %. (B) The pre-step state stays referenced across every step (the
drivers' post-step `raceUpdate m.shared m.threads`; `deliverS`'s
whole-state rollback on panic), so every cell write copies the whole heap
array — ≈4.4 ns per live cell per write, 92 % of the allocation loop's
samples in `lean_copy_expand_array` + `lean_del_core_other` — which is why
allocation COUNT still drives a quadratic cost after the dense heap. Reads
are flat in aggregate size, the per-step baseline is 252 ns, maps cost a
linear key scan (≈11 ns/entry) per write.

## Gates run (static; captured exit codes)

- `scripts/check-bugs.sh` → exit 0 («ok (110 bug(s); pinned cases behave as
  claimed)»; backlog 14 unexplained, unchanged by this lane).
- `scripts/check-evidence-size` → exit 0 («PASS … 0 new» offenders).
- No `scripts/ci` run: no runtime file changed (`git diff --stat` over
  `GoLean tools Main.lean lakefile.toml lean-toolchain baselines scripts` is
  empty); a records-only landing.

## Owed items

- Which of the two retention sites dominates mechanism (B) needs a rebuild
  (a spike that removes one site and re-measures `alloc_new`); not done here
  by design (no lake build in this lane). Both must go for in-place updates.
- The corpus consequences recorded on BUG-090 (Builder rows ≤ 1 KB, fuzz
  10×300, `repeat-bound-refused`, `issue24419`) stay until C1 lands and the
  evidence dir's plan is rerun with the acceptance criteria in the note §5.
- The sampler attributes libc-internal samples to the nearest exported
  symbol (libc is stripped) and misses the first ~0.4 s of a run; both
  limitations are stated in the evidence README. Fine for this purpose;
  a `perf`-capable box would give call stacks.

## PENDING [USER]

- Note §5 item 4: cell granularity for C1 (per-element cells / paths as
  first-class locations vs the aggregate-per-cell shape) — a design choice
  with relational consequences; [AGENT] states the trade-off only.
- BUG-090's revised Plan is an [AGENT] proposal for C1's scope, marked
  PENDING [USER] in the entry.
- Merge of this branch: the audit ask is posed in the lane report; merge only
  on explicit at-that-moment sign-off (charter step 4).

## Exact next command (for the coordinator, after sign-off)

```sh
cd /home/dev/projects/golean && git checkout main && git merge --ff-only records/bug090-rediagnosis-0911
```

Records only — no 5a re-certification is triggered (no semantic source,
frontend, apparatus or toolchain input changed); `scripts/ci` at the merged
tip is the ordinary post-merge check.
