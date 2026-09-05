# G-U uniform consumption rule — before/after choice-trace dumps, the stream bijection certificate, membership-set identity, gate tails (2026-09-04)

Consuming docs: `docs/2026-09-04_c-arc-gu-design.md` (§3–§5),
`docs/2026-08-11_latitude-inventory.md` (§0 census paragraph, E9's
CONSUMPTION RULE bullet), `docs/2026-09-04_reasoning-surface-plan.md`
§5.4 (G-U → LANDED), `TODO.md` item U.

Regeneration note (audit fix M2): `before-dump-sorted.tsv`,
`after-same-streams-dump-sorted.tsv` and `expected-transformed-dump-sorted.tsv`
are REGENERATED copies — the first copies were destroyed by a `sort >
/tmp/x && mv` chain under the sandbox's `/tmp` denial
(`docs/operational-lessons.md`, Sandbox conventions, INCIDENT line);
they were re-derived from the intact `artifacts/choice-trace-before`,
`artifacts/choice-trace-after` and `artifacts/gu-expect` runs (no run was
repeated) and the auditor re-verified the regeneration byte-for-byte
against a fresh `ac45aedd` binary.

Provenance: produced 2026-09-04 [AGENT] (C-arc step 1, worktree
`c-arc-gu` off `main` @ `ac45aedd`), executing design gate G-U — RULED
[USER] 2026-09-04 as recommended, relayed by the [AGENT] coordinator
(cited as relayed, not firsthand). No decision in this directory is new;
the one supersession it records (the width-1 `mapIter` pop attributed to
"memo §5 ruling Q3") is argued in the design note §1.

Toolchain: Go `go1.26.5 linux/amd64` (the pin, `baselines/go-oracle-pin`);
Lean `leanprover/lean4:v4.32.2` (`lean-toolchain`). `golean-before` =
`scripts/capped lake build golean` at `main` @ `ac45aedd` (the tree's
`GoLean/` identical to the seeded sibling build, `fr27-fr28` @ `56982423`);
`golean-after` = the same at the G-U tree (uncommitted at run time; the
committed sources differ from the run tree only by two dropped
redundant `simp` arguments in `Machine.lean` — proof text, no
definition). Host: linux/amd64, 32 cores / 125 GiB, shared with other
lanes' LSP servers (timing-insensitive records only).

## The claim this directory backs

1. **Behaviour SET unchanged**: the AFTER run under the corpus's six
   standard streams reports the same status and the same observation
   hash as BEFORE on every (row, stream) — including every membership
   and confluent row, whose enumerated sets the gate re-certifies — and
   the full differential (`scripts/ci --diff`) shows ZERO baseline drift.
2. **Realization re-index, certified by the bijection**: the AFTER
   machine run on the TRANSFORMED streams (each old stream minus the
   entries its width-1 `mapIter` consults drew) reproduces the BEFORE
   per-consumption dump minus the `(mapIter, bound 1)` records, byte for
   byte, on all 3364 exported rows × 6 streams.

## Reproduction (repo root; `deps/` set up by `scripts/setup-deps`)

```sh
# BEFORE (main @ ac45aedd): build, stash the binary, trace the corpus
scripts/capped lake build golean && cp .lake/build/bin/golean artifacts/golean-before
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-before \
  --golean "$PWD/artifacts/golean-before" \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
# the bijection: transformed streams + the expected AFTER dump, from the BEFORE dump
docs/evidence/2026-09-04_c-arc-gu/gu-bijection.py expect artifacts/choice-trace-before artifacts/gu-expect
# AFTER (the G-U tree): build, stash, trace the same six streams AND the transformed batch
scripts/capped lake build golean && cp .lake/build/bin/golean artifacts/golean-after
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-after \
  --golean "$PWD/artifacts/golean-after" \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
# (the transformed batch: 6 chunks of `golean-after choice-trace --batch artifacts/gu-expect/batch.tsv
#  --out … --dump … --fuel 10000000 --skip k*per --take per`, as scripts/choice-trace-corpus chunks)
docs/evidence/2026-09-04_c-arc-gu/gu-bijection.py compare artifacts/gu-expect artifacts/gu-after-transformed
# same-stream before/after comparison (status + obsHash per (row, stream); per-site counts)
docs/evidence/2026-09-04_c-arc-gu/same-streams-diff.sh artifacts/choice-trace-before artifacts/choice-trace-after
# the gate
scripts/capped scripts/ci --diff
```

EXCLUSIONS — the two rows every corpus trace since the A-series excludes,
recorded in each run's `excluded.tsv`: `goroutines/send-then-spin`
(nonterm=200, runs to the step cap under every stream) and
`strings/trimspace-repeat/repeat-bound-refused` (the 16 MiB shim
refusal path; >15 min per stream). Neither has a range-over-map, so
neither can carry a width-1 `mapIter` consult.

## Files

| file | what |
|---|---|
| `gu-bijection.py` | the certificate script: `expect` (transform the BEFORE dump → transformed streams + the expected AFTER dump) and `compare` (expected vs. the AFTER run on the transformed streams; exit 0 iff byte-identical) |
| `same-streams-diff.sh` | BEFORE vs AFTER under the SAME six streams: status/obsHash per (row, stream), per-site totals, the changed-line set vs. the had-a-width-1-record set |
| `before-summary.txt`, `after-summary.txt` | `scripts/choice-trace-summarize` output of the two same-stream runs (3364 rows exported, 36 frontend refusals, 2 excluded; the one `ERROR` row is the known frontend refusal `arrays/materialization-budget/over-budget`, identical in both) |
| `before-dump-sorted.tsv` | the BEFORE per-consumption dump, `LC_ALL=C sort`ed (23715 records) |
| `after-same-streams-dump-sorted.tsv` | the AFTER dump under the same six streams (23016 records) |
| `transformed-batch.tsv` | the tracer batch for the bijection run: every row's six streams replaced by their transformed streams (repo-relative wire paths; the wires are the BEFORE run's exports) |
| `expected-transformed-dump-sorted.tsv` | BEFORE minus the `(mapIter, 1)` records, idx renumbered, relabelled to the transformed specs (23016 records) — the AFTER run on `transformed-batch.tsv` reproduced it byte for byte, so it is also the actual dump |
| `bijection-stats.txt` | counts from `expect` (records deleted, lines with a realization shift) |
| `bijection-compare.txt` | `compare`'s verdict + the `cmp` confirmation |
| `shifted-rows.tsv` | the 63 (row, stream) lines whose realization shifts (a popped width-1 record followed by a later live read): 13 distinct rows (12 rows × 5 non-empty streams + `noodler/membership/insert-then-delete-during-range` × 3 = 63), 11 strict + 2 membership, never the default stream |
| `same-streams-diff.txt` | the same-stream comparison output |
| `membership-realization-shift.txt` | the two membership rows whose realized member moved between streams — each new hash was already one of the row's BEFORE observations |
| `excluded.tsv` | the two excluded rows (both runs) |
| `ci-diff.txt` | the gate tail: `scripts/capped scripts/ci --diff` at the landed tree |
| `ci-fast-fix-round.txt` | the fast gate (`scripts/capped scripts/ci`: build, eval tests, baseline diff of the recorded run, check-bugs, spec anchors, reconciler) at the audit-fix-round tree (M1-M3, L4-L9) — PASS, 0 HIGH |


## Results

**Bijection (the realization certificate).** `compare`: DUMP IDENTICAL
(23016 records), RESULTS (status, obsHash per (row, stream position))
IDENTICAL (20184 lines) — BIJECTION CHECK: PASS. Of the BEFORE run's
23715 records, 699 were `(mapIter, bound 1)` (121 of them at an already
exhausted stream — no entry to delete); the other 23016 are reproduced by
the new machine on the transformed streams with the same site, bound,
streamValue and pick at the same relative position. Every other delta
would have been a STOP; there was none.

**Same six streams, before vs after.** Per-site totals: `mapIter`
2006 → 1307 (−699, exactly the width-1 records); every other site
identical (`l1Sched` 9367, `appendSpill` 4868, `postOp` 4513, `backEdge`
2404, `l5ExitWindow` 323, `tryLock` 101, `nilValueMethodText` 84,
`l2Entry` 24, `l4Waiter` 22, `l2Arrival` 3). The set of (row, stream)
lines whose record sequence changed (639) EQUALS the set that had a
width-1 `mapIter` record (639); 107 of them are the default stream, where
the only change is the vanished record (the empty stream cannot shift).
Status identical on all 20184 lines; observation hash identical on
20181 — the 3 that moved are two MEMBERSHIP rows realizing a different
member of their certified set under a fixed stream
(`membership-realization-shift.txt`: `maps/added-entry-count` swaps its
two members between `9,8,…` and `rand:1:4096`; `noodler/membership/
insert-then-delete-during-range` realizes its second member under
`9,8,…` as it already did under `rand:1:4096`). No strict row's
observation moved under any stream. 0 violations, 0 alarms, 0 driver
mismatches in both runs.

**Gate.** `scripts/capped scripts/ci --diff` at the landed tree (`ci-diff.txt`):
RESULT: PASS. Differential 3402 cases = 3189 PASS / 213 FAIL, baseline
diff FULL (3402/3402, no regression, 0 PASS→non-PASS, 0 flips of any
kind — the baseline is NOT re-pinned); negative lane 394/394; membership
rows re-enumerated (membership_draws=32) and every tier=slow row verified
against its tracked certified-set record (CERTIFIED-CACHED); eval tests
153/153; core build warning-free; escape-hatch scans, bug-index
cross-check (`check-bugs`), spec-anchor citations (`check-spec-anchors`),
frontend pins, twin wire pin — all ok. Reconciler (report-only): 2
findings, 0 HIGH — both MEDIUM (C13 Go-version mentions, C5 one frontier
citation) already present in the main-era tails
(`docs/evidence/2026-09-04_fr22-fr23/ci-diff.txt`,
`docs/evidence/2026-09-04_fr4-rowm/ci-diff.txt`): 0 new. The run's meta
records `git_dirty=true` (the gate ran on the uncommitted lane tree;
the committed sources differ only by two dropped redundant `simp`
arguments in `Machine.lean`, proof text).

