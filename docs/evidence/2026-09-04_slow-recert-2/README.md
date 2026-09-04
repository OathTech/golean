# Slow-tier re-certification at main aceb0dcb — the second owed `--slow` re-run of 2026-09-04, after the round-11 train moved the wire schema again (2026-09-04)

Consuming docs: `baselines/certified/imported-goose__channel__google-search.certified.tsv`
(its `# re-certification reason (slow-recert-2, 2026-09-04)` block cites
this dir), `docs/operational-lessons.md` ("A cached certification is owed
a re-run the moment the wire schema moves…", 2026-09-04 addendum). Branch
`slow-recert-2` off main `aceb0dcb` (the round-11 merge train — hygiene
A3/A4/A8, fr22-fr23 + its audit fix round, lower-diagnose — landed first).
Predecessor: `docs/evidence/2026-09-04_slow-recert/` (the 01:02Z re-cert
at 1b8401c0, whose set this run reproduces).

## What this is

Gate maintenance of the differential apparatus, NO rule / budget /
criterion / corpus / code change; records only. `tools/reconcile-records`
C9 reported "the wire schema moved after the certification date
2026-09-04T01:02:30+00:00 (5 commit(s) to wire.go/NativeToIR.lean)" on
every gate after the round-11 train. The five: `7857a414` A3 payload
cells (HeapCell = value | mapPayload | chanPayload), `e046feb2` A4
`Expr.global` replaces `Expr.locLit`, `07ec0588` A8 dead-generality
sweep, `977b92e5` FR-22/FR-23 (`$poisoned` cells, signature-opaque
markers), `7ab1c7b8` its audit fix round (last, 16:40:23Z). Three of the
five are MACHINE-side moves through the decoder with no wire-byte
change — the case the standing rule names as the reason the re-cert is
owed even when the cached fixture's sha is unchanged. The one `tier=slow`
row in the corpus is still `imported-goose/channel/google-search`
(membership lane, `engine=dedup`, `members=6`). This dir is the
first-hand record of the re-run and of the second K=80 exhibition under
the 2026-09-03 sampling rule.

## Conclusion

**The certified set is IDENTICAL — no finding.** `scripts/capped
scripts/ci --slow` at the CLEAN tip aceb0dcb (`git_dirty=false` in
`slow-latest.meta.tsv`): RESULT: PASS, exit 0, **516 s wall**
(17:24:37Z → 17:33:13Z; includes the `lake build` in this worktree —
partly warm, see the run note below), 3365/3365 baseline diff FULL, no
regression, 0 PASS→non-PASS flips. The row was genuinely re-enumerated
(caption `enumerated=6 …`, not CERTIFIED-CACHED) and reproduced the
tracked record's set AND graph bit-for-bit: members
{123,132,213,231,312,321}, `nodes=6193933 edges=6565663 dedupHits=371731
certified=checkCert` (`recert-set-comparison.tsv`, `recert-google-search/`).
The fixture's wire sha is UNCHANGED at `2f1d639f…` (fresh frontend emit at
the tip BEFORE the run, `recert-google-search/wire.sha256`; the fixture
imports nothing and none of the round-11 node kinds occurs in its wire).
Delta class of the record refresh: **DATE/COMMIT-ONLY** — the
`# certified:` header moves to `2026-09-04T17:24:37+00:00  commit: …
aceb0dcb`; set, graph, params and wire sha untouched; the 01:02:30 line
is kept as `# previously:`. [AGENT] decision inside the brief's
"IDENTICAL → refresh" rule; a narrowed or widened set would have been a
STOP with old-vs-new recorded here, not a re-pin.

**Header instant** ([AGENT], same reasoning as the predecessor): the
run's START stamp 17:24:37Z is after the last wire commit (16:40:23Z),
so C9's `git log --since <certified> -- wire.go NativeToIR.lean` is
empty at this tip (checked directly: 0 commits). No tool was modified.

**Reconciler**: before (this worktree at aceb0dcb, record unrefreshed —
tree identical to main) C13 MEDIUM, C5 MEDIUM, C9 MEDIUM
(`reconciler-before.txt`); after (record refreshed) **C13 and C5 only,
0 HIGH, C9 = 0 findings** (`reconciler-after.txt`; also the `--diff`
gate's own "reconciler: 2 finding(s), 0 HIGH" line). C5 is at 2
citations (FR-7 `=`, FR-14 `slices.Sort`) — it was 1 at the predecessor;
not this lane's, recorded for the ledger owner.

**K=80 exhibition — second run under the sampling rule**
(`k80-vs-k32-exhibition.tsv`; K=32 side = the `ci --diff` run at the same
tip with the refreshed record, `diff-k32-membership-rows.tsv`). 62
membership rows (the predecessor's 58 + the four `stdlib-source/builder-cap/*`
rows landed by stdlib-source-2; no row dropped, no common row's
enumerated count moved), 770 enumerated members over the lane (511 + the
builder-cap rows' 259), every row PASS in both modes, identical
enumerated sets in both. Exhibited: **97 of 770 at K=80 vs 94 at K=32**
(predecessor: 92 vs 89 of 511); pinned rows reaching their `members=`
pin: 20 of 50 at K=80 vs 18 of 50 at K=32 (predecessor 18 of 46 in both).
Rows that moved (K=80 vs K=32, this run): `len-handoff` 2 vs 1 (pin at
draw 22), `select-default-handshake` 2 vs 1 (pin at draw 6 — the row
that went 2 → 1 last time; the memo's 1-or-2-per-run warning again),
`select-wake-multi` 2 vs 1 (pin at draw 12; stayed at 1 through 80 draws
last time), `mp-litmus` 2 vs 1 of 3 (unpinned), and
`race/free-sync/rw-tryrlock-acquire` **1 vs 2** — K=32 reached the pin at
draw 12, K=80 saw 1 distinct in all 80 draws. **`google-search`: 5 of 6 in
BOTH modes this run** (231 unexhibited at K=80; the predecessor's K=80
run exhibited 6 of 6 at draw 40, its K=32 run 4 of 6). Reading, same as
the predecessor's: K=80 buys a little on a few rows and nothing
systematic; which rows move is run-to-run noise (a row that reached its
pin at draw 6 here stayed at 1 of 2 for 80 draws this morning, and
vice versa); the caption is a lower bound on gc's support and the RESULT
never depends on it. Not a claim about K's adequacy — one run each.

**Run note (honest timing).** A first foreground attempt at 17:14:04Z
was cut by the agent harness's 10-minute foreground timeout clamp (exit
143, SIGTERM to the `scripts/capped` scope) before the differential
step; no child survived it (checked: no processes, no scopes, tree still
clean) and its log lived in a sandbox-private `/tmp` and is not
recoverable. The recorded run (`ci-slow-gate.log`) started 17:24:37Z on
the same clean tree; its `lake build` was partly warm from the cut
attempt, so 516 s is NOT a from-scratch number (the predecessor's 709 s
was). The dedup enumeration itself is the same ~160 s class either way.

## Reproduction (repo root, worktree at aceb0dcb)

```
git worktree add .claude/worktrees/slow-recert-2 -b slow-recert-2 main
scripts/setup-deps --only go,goose --from /home/dev/projects/golean
env GO111MODULE=off GOCACHE=$PWD/artifacts/coverage/go-build-cache \
  go run ./tools/nativefrontend --dir Corpus/coverage/exec/imported-goose/channel/google-search --out .tmp/precheck/wire.json
sha256sum .tmp/precheck/wire.json          # 2f1d639f… = the record's wire-sha256 (pre-check; recert-google-search/wire.sha256)
tools/reconcile-records                    # reconciler-before.txt (record unrefreshed): C13, C5, C9
scripts/capped scripts/ci --slow           # ci-slow-gate.log; slow-latest{,.meta}.tsv; recert-google-search/ from artifacts/coverage/membership/imported-goose/channel/google-search/
awk -F'\t' '$4=="membership"' artifacts/coverage/latest.tsv > slow-membership-rows.tsv
# refresh the record header (this commit), then:
tools/reconcile-records                    # reconciler-after.txt: C13 + C5 only
scripts/capped scripts/ci --diff           # ci-diff-gate-dirty.log (record + evidence dir uncommitted); diff-k32-membership-rows.tsv
scripts/capped scripts/ci                  # ci-fast-gate-clean-tip.log after the commit (see Files)
git log --since 2026-09-04T01:02:30+00:00 --format='%h %cI %s' -- tools/nativefrontend/wire.go GoLean/NativeToIR.lean   # the 5 wire commits C9 counted
git log --since 2026-09-04T17:24:37+00:00 -- tools/nativefrontend/wire.go GoLean/NativeToIR.lean   # empty at aceb0dcb
```
The K=80/K=32 join is the inline python in the lane transcript
(`k80-vs-k32-exhibition.tsv` header names its two inputs; columns are
parsed from the PASS captions — `enumerated=/exhibited=/draws=`, the
`members=` pin, and the stop reason: "stopped at the members=N pin" →
`pin`, "no members= pin" → `no-pin`, otherwise `K-exhausted`; for the
CERTIFIED-CACHED K=32 caption of `google-search`, `members=` stands in
for `enumerated=`).

## Toolchain, commit, host

* `go version go1.26.5 linux/amd64` — the pin in `baselines/go-oracle-pin`
  (`go_toolchain go1.26.5`, `go_drift_actual false` in `slow-latest.meta.tsv`).
  Lean: `lean-toolchain` = `leanprover/lean4:v4.32.2`; `golean` =
  `.lake/build/bin/golean` built by the gate's own `lake build` in this
  worktree.
* Commit: `aceb0dcb` (main tip after the round-11 train), CLEAN for the
  `--slow` run (`slow-latest.meta.tsv`: `git_dirty false`). The `--diff`
  run has `git_dirty true` (the refreshed record + this dir, uncommitted;
  its log's START line says so); the clean-tip fast gate is
  `ci-fast-gate-clean-tip.log`, added by the follow-up evidence commit.
* Host: linux/amd64, the shared 32-core / 125 G dev box, other lanes'
  gates running concurrently and heavily: slow run load avg 5.10 at
  start / 10.83 at end with a 1-min peak of 54.6 mid-run; the `--diff`
  gate started at a 1-min load of 62.7 and took 412 s. Timing numbers
  are for THIS load, not a quiet box.
* Run: 2026-09-04 17:14–17:45 UTC. [AGENT] throughout; no [USER] ruling
  was needed (no set moved). The ops-lessons addendum's "standing
  post-train `--slow`" is a PROPOSAL for a [USER] call, not adopted here.

## Files

* `ci-slow-gate.log` — the whole `scripts/capped scripts/ci --slow` output with START/END stamps, tip, dirty count, load (and the note about the cut first attempt).
* `slow-latest.tsv` / `slow-latest.meta.tsv` — the slow run's published results (`membership_draws 80`, `git_commit aceb0dcb…`, `git_dirty false`).
* `slow-membership-rows.tsv` — the 62 membership rows at K=80.
* `recert-google-search/` — `observations.txt` (the fresh 6-member set), `enum-stats.txt` (the dedup graph line), `draws.txt` / `samples.txt` (the 80 alternating plain/-race draws), `unexhibited.txt` (231), `wire.sha256`.
* `recert-set-comparison.tsv` — the per-row record-vs-fresh table (one tier=slow row exists).
* `reconciler-before.txt` / `reconciler-after.txt` — C9 present / cleared; C13 + C5 unchanged.
* `ci-diff-gate-dirty.log` — the `--diff` gate on the refreshed-but-uncommitted record (PASS, 3365/3365, 412 s).
* `diff-k32-membership-rows.tsv` — the 62 rows at K=32 from that run (google-search captioned CERTIFIED-CACHED with the new stamp).
* `k80-vs-k32-exhibition.tsv` — the joined exhibition table.
* `ci-fast-gate-clean-tip.log` — the clean-tip fast gate after the commit (follow-up evidence commit).
