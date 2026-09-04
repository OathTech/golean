# Wave (iii) B2 + B3 + B8 — gate tails, choice-trace deltas, the B3 equivalence prototype (2026-09-04)

Consuming docs: `docs/2026-09-04_hygiene-wave3-design.md` (every §-item's
"Preservation"/"Gate" paragraph and §B8's finding), `docs/2026-09-03_design-hygiene-arc.md`
(landing record, step (iii)), `docs/2026-09-03_grumpy-professor-review.md`
§3(b) (the "LANDED <sha>" lines for B2, B3, B8; §3(a) A7), `docs/BUGS.md` BUG-092.

Provenance: produced 2026-09-04 [AGENT] (design-hygiene arc step (iii),
worktree `hygiene-wave3` off `main` @ `aceb0dcb` — the A-series on main). The
ratification the arc rests on is [USER] (Mike, 2026-09-03, relayed by the
coordinator — quoted in the arc plan). No decision in this directory is a new
one; the one FINDING (BUG-092) is disclosed, not decided.

Toolchain: Go `go1.26.5 linux/amd64` (the pin, `baselines/go-oracle-pin`);
Lean `leanprover/lean4:v4.32.2` (`lean-toolchain`); every `golean` binary is
`scripts/capped lake build` from the named tree's sources. Host: linux/amd64,
32 cores / 125 GiB, shared with other lanes' gates (timing-insensitive records
only).

## The claim this directory backs

Each item is semantics-preserving on the MACHINE: the full native
differential (`scripts/capped scripts/ci --diff`) reports ZERO baseline drift
after each item (3365 rows: 3165 PASS / 200 FAIL, FULL 3365/3365, 0 flips), and
the whole-corpus labeled-consumption trace (`scripts/choice-trace-corpus
--dump`: every executable row × 6 streams) is byte-identical to the pre-wave
snapshot on every aggregate column AND, since this wave, on every individual
consumption record (id, stream, idx, phase, site, bound, streamValue, pick —
23665 records over 19962 (row, stream) lines). For B8 the byte-identity of the
NEW tracer's records (the machine's own projections) against the OLD tracer's
(the hand mirror) is the executable check of the consumption theorem.

## Reproduction

```sh
# pre-wave snapshot: a clean worktree at main @ aceb0dcb with ONLY the tracer's
# --dump patch applied (GoLean/ChoiceTrace.lean, scripts/choice-trace-corpus —
# lane tooling, no machine change); its binary is the OLD tracer + OLD machine
scripts/capped lake build golean
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-before \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
# per item, at the item's tree (the binary copied aside so later builds do not disturb the run)
scripts/capped scripts/ci --diff                       # transcripts/gate-<item>.txt
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-<item> --golean artifacts/golean-<item> \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
docs/evidence/2026-09-03_hygiene-a-series/choice-trace/trace-diff.sh artifacts/choice-trace-before artifacts/choice-trace-<item>
cat artifacts/choice-trace-before/dump-*.tsv | grep -v '^id	' | sort > before.tsv
cat artifacts/choice-trace-<item>/dump-*.tsv | grep -v '^id	' | sort > <item>.tsv
cmp before.tsv <item>.tsv                              # choice-trace/<item>-diff.txt
# the B3 prototype (equivalence of the rebuild instances to the retired 30-arm walks)
scripts/capped lake env lean b3-prototype/Proto.lean   # at a tree with the PRE-B3 walks (main @ aceb0dcb)
```

EXCLUSIONS (recorded in each run's `excluded.tsv`, never silent): `goroutines/send-then-spin`
(nonterm=200; the A-series' exclusion) and `strings/trimspace-repeat/repeat-bound-refused`
(NEW this wave: the row's single-stream trace did not finish in 15 min — three
drivers × a 16 MiB shim refusal path; the first full run stalled 60 min on it,
`transcripts/first-run-stall.txt`). Both are traced by no wave run; neither
touches a stream-consuming site under the default stream that the corpus does
not exercise elsewhere.

The pre-wave snapshot: 3328 rows exported, 35 frontend refusals
(export-fail.tsv), 2 excluded, 19962 (row, stream) lines, 23665 consumptions,
per-site `l1Sched=9361 appendSpill=4844 postOp=4513 backEdge=2400 mapIter=2006
l5ExitWindow=307 tryLock=101 nilValueMethodText=84 l2Entry=24 l4Waiter=22
l2Arrival=3`, 0 violations / 0 alarms / 0 mismatches; the one `ERROR` row is the
known frontend refusal `arrays/materialization-budget/over-budget`
(`choice-trace/before-summary.txt`).

## Per-item record

| item | tree gated | ci --diff | rows | drift | flips | choice-trace vs before |
|---|---|---|---|---|---|---|
| B2 `Result` at the apply boundary | B2 sources (uncommitted at run; committed unchanged as `91c57c9e`) | PASS | 3365 = 3165/200 | 0 (FULL 3365/3365) | 0 | aggregate DELTA 0 on 19963 lines; per-consumption dump byte-identical, 23665 records (`choice-trace/b2-diff.txt`, `b2-summary.txt`) |
| B3 the `Cont` algebra (+ A7 accessor) | B3 sources (uncommitted at run; committed unchanged as `cd2a3474`) | PASS | 3365 = 3165/200 | 0 (FULL 3365/3365) | 0 | aggregate DELTA 0; dump byte-identical, 23665 records (`choice-trace/b3-diff.txt`, `b3-summary.txt`) |
| B8 consumption from the machine | B8 sources (uncommitted at run; committed unchanged as `2e69fde0`) | PASS | 3365 = 3165/200 | 0 (FULL 3365/3365) | 0 | aggregate DELTA 0 on 19963 lines; the NEW tracer's per-consumption dump byte-identical to the OLD tracer's, 23665 records, 0 sentinel / pick-record alarms (`choice-trace/b8-diff.txt`, `b8-summary.txt`) |

Each per-item `ci --diff` ran on the item's UNCOMMITTED sources; the commit
that followed contains exactly those sources (no edit between run and commit).
The per-item `ci --diff` notes "recorded on a DIRTY tree" for that reason.

## The B3 prototype (`b3-prototype/`)

`Proto.lean` elaborates against the PRE-B3 walks (a tree at `main` @
`aceb0dcb`; the walks are unchanged between there and the B2 tip `91c57c9e`)
and proves `pushDefer'_eq`, `recoverThroughWrappers'_eq`, `recoverResult'_eq`:
each `Cont.rebuild` instance equals the retired 30-arm definition on every
continuation (30-case inductions). `proto-run.txt` is the elaboration
transcript (exit 0, the `Cont.rebuild.induct` shape printed as a check; no
`sorry`). B3 then REPLACED the definitions by the proved-equal instances, so
the prototype is the preservation proof and the differential + trace the
regression.

## Files

- `transcripts/gate-b2.txt`, `gate-b3.txt`, `gate-b8.txt` — `ci --diff` tails.
- `transcripts/first-run-stall.txt` — the stalled first snapshot run (exclusion reason).
- `choice-trace/before-summary.txt`, `b2-summary.txt`, `b3-summary.txt`, `b8-summary.txt` — the corpus tracer summaries.
- `choice-trace/b2-diff.txt`, `b3-diff.txt`, `b8-diff.txt` — aggregate `trace-diff.sh` output + the per-consumption `cmp` verdict.
- `choice-trace/dump-before-sorted.tsv` — the pre-wave per-consumption records (the oracle; 23665 lines).
- `b3-prototype/Proto.lean`, `proto-run.txt`.
