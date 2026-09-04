# The A-series (A1–A10) — per-item gate tails and choice-trace deltas (2026-09-04)

Consuming docs: `docs/2026-09-03_hygiene-a-series-design.md` (every §A-item's
"Gate" paragraph), `docs/2026-09-03_design-hygiene-arc.md` (landing record,
step (ii)), `docs/2026-09-03_grumpy-professor-review.md` §3(a) (the
"LANDED <sha>" / "SKIPPED" lines).

Provenance: produced 2026-09-04 [AGENT] (design-hygiene arc step (ii),
worktree `hygiene-a-series` off `main` @ `1b8401c0` — the first main SHA
with both prerequisite lanes merged: `bug087-paniktext` (ChoiceSite
`nilValueMethodText`) and `q-trylock` (ChoiceSite `tryLock`)). The
ratification the arc rests on is [USER] (Mike, 2026-09-03, relayed by
the coordinator — quoted in the arc plan). No decision in this directory
is a new one.

Toolchain: Go `go1.26.5 linux/amd64` (the pin, `baselines/go-oracle-pin`);
Lean `leanprover/lean4:v4.32.2` (`lean-toolchain`); the `golean` binary is
`scripts/capped lake build golean` from the worktree's sources at each
step. Host: linux/amd64, 32 cores / 125 GiB, shared with other lanes'
gates (timing-insensitive records only).

## The claim this directory backs

Each A-item is semantics-preserving on the MACHINE: the full native
differential (`scripts/capped scripts/ci --diff`) reports ZERO baseline
drift after each item, and the whole-corpus labeled-consumption trace
(`scripts/choice-trace-corpus`: every executable row × 6 streams — the
default stream, three fixed adversarial streams, two seeded random
streams) is byte-identical on every consumption-relevant column
(status, consumed, wide, exhaustedAt, wideAfterExhaustion, perSite,
maxBound, violations, alarms, obsHash, driverAgreement) against the
pre-series snapshot.

## Reproduction

```sh
# from the worktree root, at the SHA named in each row below
scripts/capped lake build golean
scripts/choice-trace-corpus --jobs 6 --out artifacts/choice-trace-<tag> --exclude goroutines/send-then-spin
#   (send-then-spin: the membership row with nonterm=200 that spins to the fuel cap; excluded
#    exactly as the bug087-paniktext lane's trace did — recorded in excluded.tsv, never silent)
docs/evidence/2026-09-03_hygiene-a-series/choice-trace/trace-diff.sh artifacts/choice-trace-before artifacts/choice-trace-<tag>
scripts/capped scripts/ci --diff        # the gate; tail copied to transcripts/gate-<item>.txt
```

The pre-series snapshot (`before`) was taken at `1b8401c0` with the
worktree's binary built from those sources (the lake cache was seeded
from the primary checkout and rebuilt nothing): 3249 rows exported,
34 frontend refusals (export-fail.tsv), 1 excluded, 21972 consumptions
checked, per-site totals `l1Sched=9361 postOp=4513 appendSpill=3151
backEdge=2400 mapIter=2006 l5ExitWindow=307 tryLock=101
nilValueMethodText=84 l2Entry=24 l4Waiter=22 l2Arrival=3`, 0 violations /
0 alarms / 0 mismatches (`choice-trace/before-summary.txt`).

## Per-item record

| item | tree gated | ci --diff | rows | drift | flips | choice-trace delta vs before |
|---|---|---|---|---|---|---|
| A1 stop grammar | A1 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 (id,stream) lines identical on every column; per-site totals identical (`choice-trace/a1-summary.txt`) |
| A2 dense heap | A2 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 lines identical; per-site totals identical (`choice-trace/a2-summary.txt`) |
