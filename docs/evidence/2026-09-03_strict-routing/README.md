# Strict-lane routing rule adopted — the eight scheduling rows routed or dispositioned (2026-09-03)

Consuming docs: `docs/coverage-suite-structure.md` ("Lane assignment:
the strict-lane routing rule"), `docs/2026-09-01_membership-depth.md`
(§5 rule, §6 P1 status), `docs/language-coverage-ledger.md` §8e,
`docs/coverage-ledger.md` (Goroutines and scheduling row), the four
routed/annotated `cases.tsv` files, `baselines/native-full.tsv` header.

## Provenance

- [USER] ruling (Mike, 2026-09-03): «(6) strict-lane, agree» to the
  coordinator's item "Strict-lane routing rule: adopting it turns eight
  scheduling rows red until routed. Recommendation: adopt, and route
  them in the same slice so nothing sits red." Relayed to this worker
  by the [AGENT] coordinator — cited as relayed, not firsthand.
- Everything below is [AGENT]-executed inside that brief as corrected:
  a GATE CHANGE (guard-strengthening only) in `scripts/diff-coverage`
  and `scripts/coverage-manifest`, red-first fixtures in
  `scripts/test-lane-validation`, corpus lane declarations on 23 rows,
  and records. No `GoLean/` or `tools/` change: the tracer the guard
  calls (`golean choice-trace`, `GoLean/ChoiceTrace.lean`) was already
  on main from the membership-depth lane, unchanged here.
- Commit: worktree `strict-routing` branched from main `345ef090`;
  every run below was made on that commit plus this lane's then-
  uncommitted edits (`git_commit 345ef090`, `git_dirty true` in both
  gate runs' `latest.meta.tsv`, as the gate tail's dirty-tree notes
  say); the lane's own commit is the one that adds this directory
  (`git log -- docs/evidence/2026-09-03_strict-routing`). Two full
  `ci --diff` runs: the first (guard as first written) FAILED on
  exactly the 20 post-trace rows described below — that log's verdict
  lines are `gate-tail-run1-FAIL.txt`; the second PASSED (`gate-tail.txt`).
- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`);
  Lean `leanprover/lean4:v4.32.2`; `golean` from `scripts/capped lake
  build golean` of this worktree (the exploratory enumerations in
  `rows/*/enum-*.stats` were run with the primary checkout's binary at
  the same commit `345ef090` — identical `GoLean/` sources; every
  certified set was then RE-DERIVED by the worktree binary inside
  `scripts/diff-one` / `scripts/ci --diff`, whose logs are here).
- Host: linux/amd64, 125 GB RAM shared with several other agents'
  Lean builds and enumerations at the time (load-sensitive numbers —
  wall seconds — are indicative; memory numbers are the enumerator's
  own `maxrss`).

## Scope note

The lane began as "adopt the routing rule and re-lane eight rows"; the
[AGENT] coordinator corrected the scope mid-lane to "implement memo P1
as written in §5" (the depth guard as a gate change). What carried
over from the first half: the three confluent routings, their
certified sets and gc draws, the enumeration attempts on the other
five (the FINDING that they do not close), the rule text, the records.
What changed: the five unclosable scheduling rows and the fifteen
capacity rows now declare `depth=N` instead of being "OWED"; the guard
is mechanized with red-first fixtures; `beside-loop` moves stage.

## Conclusion

The guard is in the gate (`scripts/diff-coverage` + `scripts/coverage-
manifest`; fixtures `scripts/test-lane-validation` Part A depth shapes
and Part B D1-D6 — all green, log here). Of the 23 rows the memo's trace
showed outrunning the fixed streams (re-traced here, `trace23.tsv`;
numbers match memo §2.3; controls `d-int`/`d-uint`/`named-call`
covered): 3 scheduling rows are CONFLUENT (|set| = 1 by `engine=dedup`,
`backedge=full`, checker-accepted; 20 gc draws each, plain/-race
alternating, all the singleton); 5 scheduling rows declare `depth=N`
because their state graphs do NOT close within the fail-loud caps
(40 GB cgroup kill / 60M dedup work budget — a FINDING: they cannot
honestly sit in a lane claiming invariance over all schedules;
`depth=` is the strict spot check with N tied to the measured wide
count, not a certificate); 15 capacity rows declare `depth=N`. Every
declared seeded stream reports `wideAfterExhaustion = 0` at the gate.
The guard's FIRST full gate run then reached 20 more rows than the
memo's 23 — 16 noodler rows born after the trace (`trace-new16.tsv`;
5 close under `engine=dedup` → confluent, 11 do not → `depth=N`; memo
§10.1) and 4 heavy zero-consumption rows on which the tracer exceeded
the 30 s single-run budget (`tracer-timing/`: 20-64 s unloaded for its
eight passes) — the tracer now has its own named budget
(`LEAN_TRACE_TIMEOUT_SECONDS`, default 240 s). No observed-∉-modeled
finding (160 gc draws over the 8 confluent rows, all members). Gate:
0 PASS→non-PASS; 9 stage-only moves (8 → confluent;
`channels/select-select/beside-loop` FAIL/nondet → FAIL/lean-observation
under item 4).

The brief's first form said "route to the membership lane"; the
apparatus refuses a membership row whose enumerated set is a singleton
and every set that closed IS a singleton, so the lane is confluent —
the memo's own named target (§5 item 3). [AGENT]

The guard's first smoke passed every fixture: bash arrays are invisible
to diff-coverage's per-case `bash -c` workers, so the invariance streams
were EMPTY (= the default stream) and the tracer saw four default runs.
Fixed by exporting scalars and parsing the tracer's reports positionally;
`smoke/latest.tsv` is the post-fix run (2 refusals with the §5 wording,
1 variant-refusal at lean-observation, 3 passes), and D1-D6 pin it.

## Per-row table

| row | old lane | trace: wide picks default / after exhaustion (worst fixed stream) | enumeration | certified set | disposition | gc draws (20, plain/-race alt.) |
|---|---|---|---|---|---|---|
| `spec-examples-stmt/go-statements/func-literal` | strict | 17 / 7 of 17 | `engine=dedup backedge=full`: 3,343 nodes / 3,440 edges, <1 s (DFS `backedge=full` agrees: 217,200 leaves, depth 43, 1 obs, 90 s) | {3} | **confluent** | 20/20 members, 1 distinct |
| `goroutines/pipeline/two-stage` | strict | 44 / 35 of 45 | `engine=dedup backedge=full`: 866,780 nodes / 954,907 edges, 27 s | {2468} | **confluent** | 20/20 members, 1 distinct |
| `goroutines/pipeline/buffered-stage` | strict | 29 / 21 of 31 | `engine=dedup backedge=full`: 187,497 nodes / 207,482 edges, 4 s | {35} | **confluent** | 20/20 members, 1 distinct |
| `spec-examples-stmt/prime-sieve/five` | strict | 187 / 180 of 188 | dedup KILLED at 40 GB: backedge=full 66 s, =0 81 s, =1 81 s | not certified | **strict, depth=1024** (seeded 1024: 145/140/147 wide, 0 after) | — (no set; strict differential) |
| `spec-examples-stmt/prime-sieve/eight` | strict | 521 / 514 of 522 | dedup KILLED at 40 GB: backedge=full 41 s, =0 31 s | not certified | **strict, depth=4096** (seeded 2048 trace: 312/305/295, 0 after) | — |
| `goroutines/worker-pool/shared-feed` | strict | 32 / 24 of 32 | dedup KILLED at 40 GB: backedge=full 161 s, =0 148 s | not certified | **strict, depth=128** (seeded 256: 35/36/36, 0 after) | — |
| `sync/waitgroup-workers-join/workers-join` | strict | 28 / 18 of 28 | dedup work budget exceeded: full@30M 13.6M nodes 59 s; =0@60M 27.1M nodes / 32.9M edges, 39.7 GB, 123 s | not certified | **strict, depth=128** (seeded 256: 30/29/30, 0 after) | — |
| `imported-goose/channel/parallel-search-replace/search-replace` | strict | 42 / 33 of 43 | dedup KILLED at 40 GB: backedge=0 719 s, backedge=full 849 s (maxrss 41.9 GB) | not certified | **strict, depth=256** (seeded 256: 41/39/50, 0 after) | — |
| 15 capacity rows (`fmt/*` 6, `multipkg/mini-raft-twin/*` 5, `strconv/format-parse/*` 4) | strict | `trace23.tsv` (w 10-66; worst after-exhaustion 1-50) | not attempted (capacity latitude; the memo's `depth=` home) | — | **strict, depth=64-512** (memo §10 table) | — |
| `noodler/goroutines/{fifo-one-sender,lockstep-transcript,directional-params}`, `noodler/select/ping-pong`, `noodler/syncmisuse/unlock-from-other-goroutine` (post-trace) | strict | `trace-new16.tsv` | `engine=dedup backedge=full`: 4,955 / 2,018 / 5,718 / 18,694 / 600 edges, < 1 s each | {1234} {206} {15} {12} {3} | **confluent** | 20/20 members each, 1 distinct |
| 11 post-trace rows (`noodler/goroutines/*` 7, `closures/goroutines-loopvar`, `gostmt/pointer-method`, `syncmisuse/waitgroup-reuse`, `strconv-formatint/edges`) | strict | `trace-new16.tsv` (w 20-262) | dedup: work budget 20M exceeded at ~9.0-9.2M nodes or KILLED at 24 GB (`rows/*/enum-*cap24G.stats`); `edges` not attempted (capacity) | not certified | **strict, depth=128-2048** (memo §10.1) | — |

## Lint (item 4 of the first brief): SUPERSEDED by the mechanized guard

A tag lint ("strict row whose `main.go` spawns goroutines must carry
`routing=strict-justified:<reason>`") was measured before the scope
correction: 34 packages / **167 strict rows** at package level, and
the manifest's strict-row rule forbids params — too wide for a tag. The
guard needs no author tag: it reads the tracer's exact observable per
row, which is what P1 asked for. [AGENT]

## Reproduction (from the repo root)

```
# enumerate one row (the certification the confluent lane runs):
.lake/build/bin/golean coverage-observations \
  --input artifacts/coverage/native/<id>/wire.json --function <subject> \
  --max-width 4 --max-sites 64 --cap 64 --work-cap <work> --expect-status ok \
  --backedge full --engine dedup            # + --arg-int <n> for prime-sieve
# the attempts that fail loud were run as
#   GOLEAN_MEM_MAX=40G scripts/capped /usr/bin/time -f "maxrss_kb=%M wall_s=%e" .lake/build/bin/golean coverage-observations ...
# (see each rows/<id>/enum-*.stats header for the exact width/sites/work/backedge)
# gc draws (20, alternating plain / -race) against a certified set:
docs/evidence/2026-09-03_strict-routing/gc-draws.sh artifacts/coverage/go-run/<id-with-__> rows/<id>/certified-set.txt <out-dir>
# the routed rows through the gate's own confluent path:
scripts/diff-one spec-examples-stmt/go-statements/func-literal goroutines/pipeline/two-stage goroutines/pipeline/buffered-stage
# the guard's fixtures (Part A: manifest shapes; --with-go: D1-D6 through the harness):
scripts/test-lane-validation && scripts/test-lane-validation --with-go
# the full gate:
scripts/capped scripts/ci --diff
```

Files: `rows/<id>/enum-*.stats` (enumerator stderr: stats line or the
named refusal / capped kill), `rows/<id>/certified-set.txt` (the
singleton, canonical observation JSON), `rows/<id>/gc-draws.tsv`
(draw#, mode, exit, membership verdict, observation), `trace23.tsv`
(+ `trace23.sh`, `seeded-stream.sh`: the 23-row re-trace under the 3
fixed and 3 seeded streams — run `scripts/coverage-manifest >
artifacts/strict-routing/manifest.tsv` first; the seeded generator is
the one `scripts/diff-coverage` embeds), `smoke/` (the hand-built
6-row manifest + the post-fix harness results and meta),
`trace-new16.tsv` (the 16 post-trace rows under fixed + seeded 256 +
seeded 1024 streams), `tracer-timing/` (the four heavy rows: tracer
wall seconds and their zero-consumption reports),
`test-lane-validation-partA.log` / `test-lane-validation-with-go.log`
(the fixtures), `diff-one-first-three.log`, `gate-tail.txt` (run 2,
PASS) / `gate-tail-run1-FAIL.txt` + `run1-drift-ids.txt` (run 1: the 20
post-trace rows the guard caught), `depth-rows-at-gate.tsv` (the 31
`depth=` rows' PASS details at run 2), `baseline-drift.txt`, `reconcile-before.txt` / `reconcile-after.txt`,
`gc-draws.sh`.
