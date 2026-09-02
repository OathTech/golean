# Machine-side certification of the E9 rows — `scripts/diff-one` at the slice tree (2026-09-02)

Producer (from the repo root, slice tree = `main` @ `0f3c05ff` + this
slice's changes; `golean` built by `scripts/capped lake build golean GoLean`):

```sh
scripts/diff-one maps/cross-goroutine-delete-readd/drf maps/cross-goroutine-delete-readd/insert \
  maps/cross-goroutine-delete-readd/racy maps/delete-insert-readd-during-range \
  maps/delete-readd-during-range maps/added-entry-count
```

Result lines (verbatim `artifacts/coverage/latest.tsv` detail column;
enumerator stats from `artifacts/coverage/membership/<id>/enum-stats.txt`,
sample tallies from `samples.txt` — 5 plain + 5 `-race` gc samples):

| row | lane | machine set (enumerated) | gc samples (10) | enumerator |
|---|---|---|---|---|
| `maps/cross-goroutine-delete-readd/drf` | membership | {3, 4} (members=2) | 3 ×10; 4 unexhibited | steps=387703 probes=44799 sites=14933 leaves=11880 maxdepth=19 width=4 backedge=full |
| `maps/cross-goroutine-delete-readd/insert` | membership | {1, 2} (members=2) | 1 ×2, 2 ×8 — BOTH exhibited | steps=1970410 probes=207879 sites=69293 leaves=62100 maxdepth=21 width=8 backedge=full |
| `maps/cross-goroutine-delete-readd/racy` | racy | every enumerated path refuses (observations=1) | `-race` red | steps=690 probes=102 sites=34 leaves=30 maxdepth=9 width=4 backedge=full |
| `maps/delete-insert-readd-during-range` | membership | {1, 2} (members=2) | 2 ×10; 1 unexhibited (the probe shows ~13% at n=1) | steps=6068 probes=372 sites=124 leaves=114 maxdepth=5 width=8 |
| `maps/delete-readd-during-range` (pre-existing) | membership | {3, 4, -1} — UNCHANGED | 3 ×10 | (unchanged) |
| `maps/added-entry-count` (pre-existing) | membership | {1, 2} — UNCHANGED | both exhibited | (unchanged) |

Summary line: `differential coverage summary: cases=6 pass=6 fail=0
export_status=0`.

Before the pool-level prune (`pruneForeign`), the two cross-goroutine
membership rows' machine sets were the singletons {3} and {1}; the
membership lint refuses a singleton set, and the `insert` row's gc
samples (value 2) would in addition have been OUTSIDE the set — the
differential mismatch the slice closed. The full-corpus
re-certification is the gate run recorded in `gate-tail.txt`.
