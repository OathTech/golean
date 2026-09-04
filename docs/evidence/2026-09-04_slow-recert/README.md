# Slow-tier re-certification at main 1b8401c0 — the owed `--slow` re-run after the wire schema moved (2026-09-04)

Consuming docs: `baselines/certified/imported-goose__channel__google-search.certified.tsv`
(the refreshed record's `# re-certification reason (slow-recert,
2026-09-04)` block cites this dir), `docs/operational-lessons.md` ("A
cached certification is owed a re-run the moment the wire schema
moves…"). Branch `slow-recert` off main `1b8401c0` (the round-9
merge train — bug087-paniktext, q-trylock, cedar-census — landed
first; this lane waited for it by design).

## What this is

Gate maintenance of the differential apparatus, NO rule / budget /
criterion / corpus change. `tools/reconcile-records` C9 had reported
"the wire schema moved after the certification date 2026-09-01" on
every gate since 2026-09-01 (13 commits to `tools/nativefrontend/wire.go`
/ `GoLean/NativeToIR.lean` at this tip: exact-key discipline, the
gotest-harvest fixes, BUG-082 make-map `hint`, storeLoc, atomics-w1
`atomic-op`, stdlib source-through, q-trylock `sync-op`). The one
`tier=slow` row in the corpus — `imported-goose/channel/google-search`
(membership lane, `engine=dedup`, `members=6`; the census is a
params-column scan of every `cases.tsv`, below — the five other
"tier=slow" text hits are prose in `why` columns, and there are no
confluent-lane slow rows) — carries CERTIFIED-CACHED standing on the
gate path keyed to its wire sha; only `scripts/ci --slow` re-enumerates.
This dir is the first-hand record of that re-run and of the first K=80
membership exhibition under the 2026-09-03 sampling rule.

## Conclusion

**The certified set is IDENTICAL — no finding.** `scripts/capped
scripts/ci --slow` at the CLEAN tip 1b8401c0 (`git_dirty=false` in
`slow-latest.meta.tsv`): RESULT: PASS, exit 0, **709 s wall**
(01:02:30Z → 01:14:19Z; includes a from-scratch `lake build` in the
fresh worktree), 3284/3284 baseline diff FULL, no regression, 0
PASS→non-PASS flips. The row was genuinely re-enumerated (caption
`enumerated=6 …`, not CERTIFIED-CACHED) and reproduced the tracked
record's set AND graph bit-for-bit: members {123,132,213,231,312,321},
`nodes=6193933 edges=6565663 dedupHits=371731 certified=checkCert`
(`recert-set-comparison.tsv`, `recert-google-search/`). The fixture's
wire sha is UNCHANGED at `2f1d639f…` — none of the moved node kinds
occurs in this program's wire (verified by a fresh frontend emit at the
tip before the run; `recert-google-search/wire.sha256`), which is why
the fast gate never went STALE while C9 fired. Delta class of the record
refresh: **DATE/COMMIT-ONLY** — the `# certified:` header moves to
`2026-09-04T01:02:30+00:00  commit: … 1b8401c0`; set, graph, params and
wire sha are untouched; the 2026-09-01 line is kept as `# previously:`.
[AGENT] decision inside the brief's "IDENTICAL sets → refresh" rule.

**Why a timestamp, not a date** ([AGENT]): C9's staleness test is
`git log --since <certified> -- wire.go NativeToIR.lean`; the last wire
commit (4baa53c7) is dated 2026-09-04T00:26:08Z, the same calendar day
as the run, and `--since` on a bare date means midnight — a bare
`2026-09-04` would keep C9 firing on a current record. The harness
(`sed 's/^# certified: //'`, echoed into the CERTIFIED-CACHED caption)
and the reconciler (`^# certified: (\S+)\s+commit:`) both accept the
instant unchanged; no tool was modified.

**Reconciler**: before (primary checkout, main 1b8401c0, record
unrefreshed) C13 MEDIUM, C5 MEDIUM, C9 MEDIUM (`reconciler-before.txt`);
after (this worktree, refreshed record) **C13 and C5 only, 0 HIGH,
C9 = 0 findings** (`reconciler-after.txt`; also the fast gate's own
"reconciler: 2 finding(s), 0 HIGH" line).

**K=80 exhibition — first slow run under the sampling rule**
(`k80-vs-k32-exhibition.tsv`; K=32 side = the `ci --diff` run at the
same tip with the refreshed record, `diff-k32-membership-rows.tsv`).
58 membership rows (the sampling-budget lane's 37 plus the q-trylock,
noodler-ifaces, BUG-087 and rwmutex/free-sync rows landed since), 511
enumerated members over the lane, every row PASS in both modes,
identical enumerated sets in both. Exhibited: **92 of 511 at K=80 vs
89 at K=32**; pinned rows reaching their `members=` pin: 18 of 46 in
BOTH modes. Rows that moved: `google-search` 4 → **6 of 6** (pin reached
at draw 40 — the first run to exhibit its full support; the
2026-09-03 K=32 gate run saw 5 of 6 and the memo's two 80-draw runs 5), `race/atomics-free/publish-acquire`
1 → 2 of 2 and `rmw-acquire` 1 → 2 of 2 (unpinned rows, full K drawn),
and `goroutines/sched-dependent/select-default-handshake` **2 → 1**
(1 distinct in all 80 draws; 2 at K=32 with the pin at draw 20) — the
memo's warning that this row is 1/80 in one run and 2/80 in another,
reproduced. Reading: K=80 buys a little on the multi-member rows
(`google-search`, the two atomics-free rows) and nothing systematic on
the two-member gc-immobile scheduling rows (`len-handoff` reached its
pin at draw 10 here vs draw 32 at K=32, but `select-wake-multi`, `wake-then-abort`,
`acquisition-order`, `drf`, `insert-then-delete-during-range` and the
whole trylock/noodler-ifaces family stayed at 1 of 2 through 80 draws);
the caption is a lower bound on gc's support either way, and the RESULT
never depends on it. Not a claim about K's adequacy — one run each.

## Reproduction (repo root, worktree at 1b8401c0)

```
scripts/setup-deps --only go,goose --from /home/dev/projects/golean
env GO111MODULE=off GOCACHE=$PWD/artifacts/coverage/go-build-cache \
  go run ./tools/nativefrontend --dir Corpus/coverage/exec/imported-goose/channel/google-search --out .tmp/precheck/wire.json
sha256sum .tmp/precheck/wire.json          # 2f1d639f… = the record's wire-sha256 (pre-check)
scripts/capped scripts/ci --slow           # ci-slow-gate.log; slow-latest{,.meta}.tsv; recert-google-search/ from artifacts/coverage/membership/imported-goose/channel/google-search/
awk -F'\t' '$4=="membership"' artifacts/coverage/latest.tsv > slow-membership-rows.tsv
tools/reconcile-records                    # reconciler-before.txt (primary checkout) / reconciler-after.txt (this worktree, refreshed record)
# refresh the record header (this commit), then:
scripts/capped scripts/ci --diff           # ci-diff-gate-dirty.log (record refreshed, uncommitted); diff-k32-membership-rows.tsv
scripts/capped scripts/ci --diff           # ci-diff-gate-clean-tip.log after the commit (see Files)
git log --since 2026-09-01 --format='%h %cI %s' -- tools/nativefrontend/wire.go GoLean/NativeToIR.lean   # the 13 wire commits C9 counted
```
The K=80/K=32 join is the inline python in the lane transcript
(`k80-vs-k32-exhibition.tsv` header names its two inputs; columns are
parsed from the PASS captions `enumerated=/members= exhibited= draws=`
and the stop reason).

## Toolchain, commit, host

* `go version go1.26.5 linux/amd64` — the pin in `baselines/go-oracle-pin` (go1.26.5). Lean:
  `lean-toolchain` = `leanprover/lean4:v4.32.2` (`lake env lean --version`: Lean (version 4.32.2, x86_64-unknown-linux-gnu, commit f3b06c705e6c85f5314019d5d3baab0fec5b580c, Release));
  `golean` = `.lake/build/bin/golean` built by the gate's own
  `lake build` in this worktree.
* Commit: `1b8401c0` (main tip after the round-9 train), CLEAN for the
  `--slow` run (`slow-latest.meta.tsv`: `git_dirty false`). The first
  `--diff` run has `git_dirty true` (the refreshed record, uncommitted)
  and its log says so; the clean-tip tail is the second `--diff`.
* Host: linux/amd64, the shared 32-core / 125 G dev box, other lanes'
  gates running concurrently: load avg 5.75 at the slow run's start,
  6.49 at its end with a 1-min peak of 22.8 mid-run; 18.3 at the end of
  the fast gate. Timing numbers are for THIS load, not a quiet box.
* Run: 2026-09-04 01:02–01:27 UTC. [AGENT] throughout; no [USER]
  ruling was needed (no set moved). The lane's poll waited for the
  train per the brief (landed 00:54:14Z; two stable polls 60 s apart).

## Files

* `ci-slow-gate.log` — the whole `scripts/capped scripts/ci --slow` output with START/END stamps, tip, dirty count, load.
* `slow-latest.tsv` / `slow-latest.meta.tsv` — the slow run's published results (`membership_draws 80`, `git_commit 1b8401c0…`, `git_dirty false`).
* `slow-membership-rows.tsv` — the 58 membership rows at K=80.
* `recert-google-search/` — `observations.txt` (the fresh 6-member set), `enum-stats.txt` (the dedup graph line), `draws.txt` / `samples.txt` (the 40 alternating plain/-race draws), `wire.sha256`.
* `recert-set-comparison.tsv` — the per-row record-vs-fresh table (one tier=slow row exists).
* `reconciler-before.txt` / `reconciler-after.txt` — C9 present / cleared; C13 + C5 unchanged.
* `ci-diff-gate-dirty.log` — the fast gate on the refreshed-but-uncommitted record (PASS, 443 s).
* `diff-k32-membership-rows.tsv` — the 58 rows at K=32 from that run (google-search captioned CERTIFIED-CACHED with the new stamp).
* `k80-vs-k32-exhibition.tsv` — the joined exhibition table.
* `ci-diff-gate-clean-tip.log` — the clean-tip fast gate after the commit (added by the follow-up evidence commit).
