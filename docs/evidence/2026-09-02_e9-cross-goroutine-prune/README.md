# E9 cross-goroutine delete-prune — the gc probe matrix and the corpus witnesses (2026-09-02)

Consuming docs: `docs/2026-08-11_latitude-inventory.md` §E9 (the
"CROSS-GOROUTINE MUTATION — CLOSED 2026-09-02" bullet cites this dir);
`docs/spec-divergence-ledger.md` L-012 (the 2026-09-02 ADDENDUM);
`docs/spec-interpretations.md` I-1 (oracle-exhibition bullet);
`docs/assessment/p2-keeps-a1.md` A1-20 (closure note); `docs/BUGS.md`
BUG-005 (residual closure); `GoLean/GoCore/Machine.lean`
`Cont.mapIterK`'s ENVELOPE STATEMENT and `GoLean/GoCore/Multi.lean`
`pruneForeign`'s section docstring; the corpus rows
`Corpus/coverage/exec/maps/cross-goroutine-delete-readd/cases.tsv` and
`Corpus/coverage/exec/maps/delete-insert-readd-during-range/cases.tsv`.

Provenance: probes designed, run, and recorded 2026-09-02 [AGENT]
(Tier-5 slice `t5-e9-prune`, worktree off `main` @ `0f3c05ff`). The
envelope ruling applied is the [USER] ruling of 2026-08-19 (full
literal envelope; a deleted-then-re-created key is a NEW entry — I-1 /
L-012); nothing in this dir re-decides it. The choice to close the gap
by a machine-side cross-goroutine prune (rather than a [USER] re-scope
of the ruling) was the slice brief's stated first option [AGENT
execution inside the written boundary].

## The question

`spec#For_statements` (range clause, maps): "If a map entry that has
not yet been reached is removed during iteration, the corresponding
iteration value will not be produced. If a map entry is created during
iteration, that entry may be produced during the iteration or may be
skipped." Goroutine A ranges over `m`; on its first production it hands
the produced key `k` to goroutine B over an unbuffered channel; B
deletes `k`, re-inserts `k`, acks; A continues. Every map access is
HB-ordered by the handshake (DRF). Does gc ever produce `k` AGAIN? (The
machine's answer before this slice was "never realizable" — the
delete-prune reached only the deleting goroutine's in-flight frames;
fidelity finding A1-20.)

## What is here

- `probe/main.go` — the cross-goroutine probe: modes `drf` (the
  handshake shape; observable = production count, `size` = re-created
  key skipped, `size+1` = produced again), `grow` (as `drf` plus
  `fresh` FRESH-key inserts by B between the delete and the re-insert;
  observable = how many times the handed-over key itself is produced,
  1 or 2), `racy` (no handshake, join at the end — the unsynchronized
  control). In-process trials, one `make(map)` per trial (gc seeds each
  map's hash independently, so trials are independent draws).
- `probe/run-matrix.sh` — the exact producer of the four `gc-*.txt`
  files (builds the probe in the gitignored `.tmp/`).
- `gc-drf-inprocess.txt` — 20,000 trials × GOMAXPROCS ∈ {1,8} × sizes
  {3,8,100,1000}: **never re-produced** (160,000/160,000 at `n=size`).
- `gc-insert-sweep.txt` — the `grow` mode over `fresh` ∈
  {0,1,2,3,4,5,8} at size 3 (both GOMAXPROCS) and {0,1,3,8} at size 8:
  size 3 — 0→0%, **1→87%**, 2→75%, 3→63%, 4→50%, 5→37%, 8→0% of
  trials produce the re-created key twice; size 8 — never. gc's swiss
  map keeps ≤8 entries in a single group; the re-inserted key's slot
  relative to the iterator's position is what decides, and a fresh
  insert shifts it (8 fresh keys force a table growth that relocates
  everything past the iterator; size 8 already fills the group). The
  mechanism is gc's slot placement, NOT the concurrency.
- `gc-fresh-process.txt` — one fresh process per trial, 300 per
  GOMAXPROCS: `drf` 600/600 at n=3; `grow` (1 insert) 251/300 and
  256/300 at n=2.
- `gc-race-legs.txt` — `go build -race`: `drf` 200 trials exit 0 (no
  report), `grow` (1 insert) 200 trials exit 0 with 184/200 at n=2,
  `racy` "WARNING: DATA RACE … Found 1 data race(s)" exit 66.
- `probe-sameg/main.go` + `gc-same-goroutine-insert.txt` — the
  SAME-goroutine control (the ranging goroutine itself deletes, inserts
  `fresh` keys, re-inserts): identical rates (fresh=1 → 17,514/20,000),
  which is what makes the L-012 addendum a statement about gc's map
  and not about scheduling.

## Reproduction (from the repo root)

```sh
docs/evidence/2026-09-02_e9-cross-goroutine-prune/probe/run-matrix.sh
# same-goroutine control:
mkdir -p .tmp/e9probe-sameg && cp docs/evidence/2026-09-02_e9-cross-goroutine-prune/probe-sameg/main.go .tmp/e9probe-sameg/ \
  && printf 'module e9sameg\n\ngo 1.26\n' > .tmp/e9probe-sameg/go.mod && (cd .tmp/e9probe-sameg && go build -o probe .) \
  && for f in 0 1 2 3 8; do GOMAXPROCS=8 .tmp/e9probe-sameg/probe 20000 3 $f; done
# the machine side (the corpus rows; re-certified by scripts/ci --diff):
scripts/diff-one maps/cross-goroutine-delete-readd/drf maps/cross-goroutine-delete-readd/insert \
  maps/cross-goroutine-delete-readd/racy maps/delete-insert-readd-during-range
```

Toolchain: `go version go1.26.5 linux/amd64` — the pin in
`baselines/go-oracle-pin`. Lean: `lean-toolchain` of the tree
(leanprover/lean4 v4.32.2), `golean` built by `scripts/capped lake
build`. Host: linux/amd64, 125 GB box shared with other agents' Lean
servers; the counts are frequency estimates over independent draws,
not timing-sensitive (the GOMAXPROCS=1 and =8 columns agree to within
sampling noise, as expected for a handshake-serialized program).

Commit: probe outputs were produced on the slice's dirty worktree
(base `0f3c05ff`, this slice's changes uncommitted at run time; the gc
side does not depend on repo state). The machine-side numbers below
are from `scripts/diff-one` on the slice tree at the same point;
`MACHINE.md` in this dir records the gate-time re-certification.

## Conclusion

gc never re-produces the re-created key in the plain handshake shape
(160,600 trials), but with ONE intervening fresh insert it re-produces
it in ~87% of runs (size 3), same- and cross-goroutine alike. So the
E9 envelope member the machine could not realize — re-production of a
cross-goroutine deleted-then-re-created key on a DRF program — is not
only spec-permitted but gc-OBSERVED: before the pool-level prune the
`insert` shape was a differential MISMATCH (observed ∉ modeled). With
`pruneForeign` the machine's sets are {3,4} (`drf`) and {1,2}
(`insert`), both containing every gc sample, and the unsynchronized
`racy` control is refused on every enumerated path (gc `-race` red).
The L-012 oracle datum "gc never re-produces (incl. forced growth)" is
corrected by the addendum: gc DOES produce a key twice in one range
when a small insert intervenes, which refutes the rejected
key-identity reading as a description of gc.
