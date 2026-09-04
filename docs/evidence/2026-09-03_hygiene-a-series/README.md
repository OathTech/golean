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
| A3 payload cells | A3 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 machine delta — 19489/19489 lines identical on every consumption column; 1 row's `obsHash` moved because its exported WIRE moved (frontend quarantine-reason text nondeterminism on `stdlib-source/frontier/index-rune-goto`, FR-21; diagnosed in `choice-trace/a3-summary.txt`: hash is a function of the wire alone) |
| A4 `Expr.global` | A4 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 lines identical (`choice-trace/a4-summary.txt`) |
| A5 `Platform` | A5 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 lines identical (`choice-trace/a5-summary.txt`) |
| A6 `ShadowKey` | A6 sources (uncommitted at run; committed unchanged) | RED then PASS: first attempt 3083/201 — two `confluent` rows overran the dedup work budget (dedup ENGINE merge rate, not the machine; `transcripts/gate-a6-red-first-attempt.txt`); fixed by the canonical (sorted) shadow; second attempt PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 machine delta on both attempts (19489/19489 consumption columns identical); the second attempt shows the A3 wire-nondeterminism `obsHash` row again (`choice-trace/a6-summary.txt`) |
| A7 apply-position accessor | — | SKIPPED (design note §A7: folded into wave (iii)/B3) | — | — | — | — |
| A8 sweep | A8 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 lines identical (`choice-trace/a8-summary.txt`) |
| A9 refusal rule | A9 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 lines identical (`choice-trace/a9-summary.txt`) |
| A10 docstring diet | A10 sources (uncommitted at run; committed unchanged) | PASS | 3284 = 3085/199 | 0 (FULL 3284/3284) | 0 | 0 — 19489/19489 lines identical (`choice-trace/a10-summary.txt`) |

## Series record

Commits (branch `hygiene-a-series`, forked from `main` @ `1b8401c0`):
A1 `dfa68802`, A2 `7cba41cd`, A3 `6973354b`, A4 `bcdf04c1`, A5 `48d9aba8`,
A6 `367dab2f`, A8 `7ff80223`, A9 `80b4ed89`, A10 `884e5226`, then the
records commit (this README's final row) and a docs-only follow-up with the
clean-tip fast gate tail (`transcripts/gate-clean-tip.txt`). A7 SKIPPED.
Net `git diff --shortstat main..HEAD -- GoLean Tests` at A10: 25 files,
+1727 / −1791.

Each per-item `ci --diff` above ran on the item's UNCOMMITTED sources
(the same bytes were then committed with no edit in between — the gate
records say `git_dirty=true` for that reason, as B1's did); the clean-tip
fast gate (`scripts/capped scripts/ci`, no `--diff`: escape-hatch scans,
build, eval tests, and the baseline diff of the LAST recorded differential
run — the A10 run) is the record that the committed tip is what was
certified.

Two findings that are NOT this lane's to fix, recorded here so they are
not lost: (1) **BUG-091** (docs/BUGS.md; taken by lane `fr22-fr23`): the
native frontend's quarantine-reason string for multi-label `goto` shapes is
export-nondeterministic
(`stdlib-source/frontier/index-rune-goto`; `choice-trace/a3-summary.txt`)
— a diagnostics nondeterminism in a by-design FR-21 refusal row, visible
only through the tracer's `obsHash`; (2) the dedup ENGINE's structural
state equality is sensitive to the insertion order of the detector's
shadow (surfaced by A6's first gate; `transcripts/gate-a6-red-first-attempt.txt`)
— now moot for the shadow (kept canonical), but the same sensitivity
exists for every other assoc-list-shaped component of `RaceState`
(`chans`, `syncs`, `atomics`) and of `ExecState` in principle; an
engine-side canonical form would make merge rates interleaving-insensitive
across the board. [AGENT]
