# B1 entry-identity stamps — set-equality transcripts, red-first, gate tail (2026-09-03)

Consuming docs: `docs/2026-09-03_hygiene-b1-stamps-design.md` (§3, §4,
§6), `docs/2026-09-03_design-hygiene-arc.md` (landing record),
`docs/2026-08-11_latitude-inventory.md` §E9 (MECHANISM OF RECORD
bullet), `docs/BUGS.md` BUG-088 and BUG-005's residual text,
`GoLean/GoCore/Machine.lean` `Cont.mapIterK`'s ENVELOPE STATEMENT,
`GoLean/GoCore/Multi.lean`'s thread-locality section docstring,
`GoLean/GoCore/NPDRF.lean` obstruction 7.

Provenance: produced 2026-09-03 [AGENT] (design-hygiene arc slice 1,
worktree `hygiene-b1-stamps` off `main` @ `345ef090`; arc plan commit
`8d225e82` is the branch's first commit, `f6152a6c` the landing
commit; this README's SHA lines and the clean-tip gate tail were added
by the docs-only follow-up commit). The ratification the arc
rests on is [USER] (Mike, 2026-09-03, relayed by the coordinator —
quoted in the arc plan). No decision in this directory is a new one:
the envelope is the 2026-08-19 [USER] ruling, unchanged; the
representation change is the review's B1 as ratified.

## The claim this directory backs

The stamped machine (entry ids in the map cell, id sets in
`Cont.mapIterK`, no delete-prune anywhere) certifies to the SAME
observation sets, results, stages and enumerator statistics as the
key-set machine on every map-iteration row that exercises the E9
envelope — and on the one class where the two machines differ
(irreflexive keys — NaN), the key-set machine was the wrong one
(BUG-088; red-first below).

## What is here

- `sets/before/` — `scripts/diff-one` on 19 rows at the UNMODIFIED
  tree (`main` @ `345ef090`; the worktree's lake cache was copied from
  main and rebuilt nothing, so the binary is 345ef090's): `latest.tsv`,
  `diff-one.log`, and per membership/confluent/racy row the
  enumerator's `observations.txt` + `enum-stats.txt` under
  `membership/<id>/`.
- `sets/after/` — the same 19 rows plus `noodler/membership/
  {two-senders-buffered,select-two-ready}` and the new
  `maps/nan-key-range` at the slice tree (Lean sources final; records
  in progress), same layout.
- `transcripts/nan-key-range-red-first.txt` — main's binary vs this
  slice's binary vs `go run` on the new row's wire (BUG-088).
- `transcripts/gate-tail.txt` — the `scripts/capped scripts/ci --diff`
  summary block at the slice tree (see "Gate" below).
- `transcripts/gate-tail-clean-tip.txt` — the fast `scripts/capped
  scripts/ci` (no `--diff`: escape-hatch scans, build, eval tests, and
  the baseline diff of the LAST recorded differential run) on the
  committed clean tip `f6152a6c`, so the certified content is a commit
  and not only a worktree state.

## Set equality (the comparison, verbatim method)

```sh
# from the slice worktree root; producer of sets/before (run BEFORE any Lean edit) and sets/after:
scripts/capped scripts/diff-one maps/cross-goroutine-delete-readd/drf maps/cross-goroutine-delete-readd/insert \
  maps/cross-goroutine-delete-readd/racy maps/cross-goroutine-delete-noreadd/delete \
  maps/cross-goroutine-delete-noreadd/clear maps/cross-goroutine-delete-noreadd/other-map \
  maps/delete-insert-readd-during-range maps/delete-readd-during-range maps/added-entry-count \
  maps/added-entries-bound maps/delete-unreached-during-range maps/delete-during-range \
  maps/clear-during-range maps/update-during-range noodler/membership/three-key-map-order \
  noodler/membership/delete-other-key-during-range noodler/membership/insert-then-delete-during-range \
  race/negative/map-range-iter noodler/maps/single-entry-range
#   (after: + noodler/membership/two-senders-buffered noodler/membership/select-two-ready maps/nan-key-range)
# then: cp artifacts/coverage/latest.tsv sets/<side>/ ; cp -r artifacts/coverage/membership sets/<side>/
# comparison: per row, `cmp sets/before/membership/<id>/observations.txt sets/after/membership/<id>/observations.txt`
#             and a field-wise diff of the two latest.tsv rows.
```

Result: 19/19 shared rows — result EQUAL, stage EQUAL, machine
observation set EQUAL (11 enumerated rows: `cmp` clean on every
`observations.txt`), enumerator statistics EQUAL (the confluent/racy
rows' `steps=/probes=/sites=/leaves=/maxdepth=` strings are
byte-identical — the choice tape was consumed identically). The one
differing `latest.tsv` field is `noodler/membership/three-key-map-order`'s
gc-sample tally (`exhibited=2 unexhibited=4` → `exhibited=3
unexhibited=3` of the same 6-member machine set): five fresh `go run`
samples of a randomized iteration order — the oracle, not the machine.
Summary lines: before `cases=19 pass=19 fail=0`; after `cases=22
pass=22 fail=0`.

| row | machine set (before = after) |
|---|---|
| maps/cross-goroutine-delete-readd/drf | {3, 4} |
| maps/cross-goroutine-delete-readd/insert | {1, 2} |
| maps/cross-goroutine-delete-readd/racy | {race} (every path refuses) |
| maps/cross-goroutine-delete-noreadd/delete | {3006} — steps=137326 probes=12399 sites=4133 leaves=2700 maxdepth=17 |
| maps/cross-goroutine-delete-noreadd/clear | {1} — steps=13917 probes=2949 sites=983 leaves=990 maxdepth=13 |
| maps/cross-goroutine-delete-noreadd/other-map | {3006} — steps=137371 probes=12399 sites=4133 leaves=2700 maxdepth=17 |
| maps/delete-insert-readd-during-range | {1, 2} |
| maps/delete-readd-during-range | {-1, 3, 4} |
| maps/added-entry-count | {1, 2} |
| noodler/membership/three-key-map-order | {123, 132, 213, 231, 312, 321} |
| noodler/membership/insert-then-delete-during-range | {2, 3} |
| noodler/membership/delete-other-key-during-range | {1} — steps=139 probes=3 sites=1 leaves=2 maxdepth=1 |
| race/negative/map-range-iter | {race} — steps=2909 probes=777 sites=259 leaves=240 maxdepth=9 |
| maps/{delete,clear,update}-during-range, maps/delete-unreached-during-range, maps/added-entries-bound, noodler/maps/single-entry-range | PASS (plain differential) |

## Red-first: `maps/nan-key-range` (BUG-088)

`transcripts/nan-key-range-red-first.txt` (producer lines in its
header). main @ 345ef090's `golean native-json-run … --fuel 200000` →
`{"status":"fuel-out"}` (at the default fuel the run did not return
within 600 s: the NaN entry is never marked produced and the zero
stream re-picks it forever); this slice's binary → `ok 32`; `go run` →
`32`. The [AGENT] decision to ADD this row (a behaviour the refactor
changed, on a class no prior row covered) rather than leave it
unpinned is recorded in the design note §4 and the arc plan's
invariant 2 ("a slice may ADD rows … reports them as additions").

## Gate

`scripts/capped scripts/ci --diff` at the slice tree — `transcripts/
gate-tail.txt` (the summary block verbatim; the tree state at launch is
noted at its head). RESULT: PASS. `differential coverage summary:
cases=3196 pass=3002 fail=194`; baseline diff FULL (3196/3196, no
regression — the baseline already carried the one NEW row
`maps/nan-key-range` PASS/-, re-pinned in the same tree with its
reason in the header); re-pin guard 0 PASS→non-PASS flips; eval tests
148/148; check-bugs ok (BUG-088's case PASS as claimed);
check-spec-anchors ok; check-coverage ok. The run's reconciler line
showed 1 HIGH (C1H: the baseline's `# cases:` derivation line still
said 3195/3001/194); that line was corrected before the commit and
`tools/reconcile-records` re-run: 3 findings, 0 HIGH (the three
pre-existing MEDIUMs C13/C5/C9). Then `scripts/capped scripts/ci`
(fast) on the committed clean tip `f6152a6c`:
`transcripts/gate-tail-clean-tip.txt` — RESULT: PASS, baseline diff
FULL 3196/3196, re-pin guard 0 flips, reconciler 3 findings 0 HIGH.

## Toolchain / host

`go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`). Lean
`leanprover/lean4:v4.32.2` (`lean-toolchain`); `golean` built by
`scripts/capped lake build` in the worktree (cgroup-capped, the box's
build lock honoured). Host: the shared 125 G linux/amd64 box; other
agents' lanes were active during the runs — the enumerator statistics
compared above are counts, not timings, and are load-independent.
