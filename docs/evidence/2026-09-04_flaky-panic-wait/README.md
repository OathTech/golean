# goroutine-panic-under-wait: gc is schedule-dependent under a deferred Done (2026-09-04)

Lane `flaky-panic-wait` [AGENT], branched from main 74ffe35a; rebased onto
main ac45aedd at merge train round 14 (record-only header/tally conflicts in
`baselines/native-full.tsv` and the ledger §8 reconciled [AGENT]; the
figures below that name the pre-rebase baseline 3383 = 3173 PASS / 210
FAIL are the lane's own transcripts — after the rebase the baseline is
3403 = 3190 PASS / 213 FAIL, i.e. main's fr4-rowm 3402 + the same 1 born
PASS row and the same stage-only move). Corpus + records only: `GoLean/`,
`tools/`, `scripts/` untouched.

## The defect (round-13 merge train; diagnosis accepted by the coordinator [AGENT])

`Corpus/coverage/exec/noodler/goroutines` row `goroutine-panic-under-wait`
(subject `goroutinePanicUnderWait`): a goroutine does `defer wg.Done()`
then panics; main does `wg.Wait()` and returns 1. In gc the deferred
`Done` runs during the panicking goroutine's UNWIND and wakes main's
`Wait`; main can print its observation and `exit(0)` before the runtime
reaches `fatalpanic`'s `exit(2)`. The row sat in the STRICT lane with
`expected_status=panic` — a schedule-dependent oracle behind an
exact-match gate, the `channels/select-select/beside-loop` class
(`docs/operational-lessons.md` "An exact-match guard on a two-valued
oracle is a coin-flip gate", [USER] ruling 2026-09-03).

## gc distribution (go1.26.5, this box, 32 cores; `measure.sh`)

Harness = `tools/coverageharness` output for the row (the gate's own
wrapper); each draw classified by (exit code, ok-JSON on stdout,
`panic: under-wait` on stderr). "printed-then-abort" = the ok observation
was written and the process still died with exit 2 — the gate's strict
path classifies that draw as `panic` (output has `panic:`; rc != 0).

| mode | load | draws | silent panic (rc 2) | printed-then-abort (rc 2) | exit 0 `ok 1` |
|---|---|---|---|---|---|
| plain | idle | 40 | 39 | 1 | 0 |
| plain | 48 CPU burners | 40 | 40 | 0 | 0 |
| plain | 64 CPU burners | 200 | 199 | 1 | 0 |
| -race | idle | 40 | 20 | 20 | 0 |
| -race | 48 CPU burners | 40 | 33 | 7 | 0 |
| -race | 64 CPU burners | 200 | 175 | 25 | 0 |

Totals: plain 280 draws — 278 / 2 / 0; -race 280 draws — 228 / 52 / 0.
The exit-0 `ok 1` member was NOT exhibited in these 560 draws; it was
exhibited once by the round-13 merge train's full `ci --diff` under gate
load (the coordinator's report — the reason this lane exists). The
printed-then-abort member is the SAME class one step earlier (main
progressed past `Wait` and past its print; the child's abort landed
before main's exit) — 52/280 under -race, so the class itself is common;
the exit-0 tail of it is rare. Burners were shell busy-loops owned by
this lane and stopped by PID.

## The gate exhibited the exit-0 member itself

The lane's own full `ci --diff` (`gate-tail-1.txt`) ran the re-laned row
through the membership sampler: `enumerated=2 exhibited=2 draws=17
(K=32; stopped at the members=2 pin) unexhibited=0` — the exit-0 `ok 1`
member was DRAWN by gc at draw 17, a PLAIN draw (`gate-membership-draws.txt`,
under the gate's own parallel load), so both members of the certified set are now
gc-exhibited on record: the strict row would have been RED on that draw.

## The machine

`golean coverage-observations --input <package wire> --function
goroutinePanicUnderWait --expect-status ok,panic --backedge full`:

    default stream        -> panic "under-wait"
    --choices 0,0,1,0,0   -> ok, values [1]
    width 4, sites 16 (tree): observations=2 steps=318 probes=162
                              sites=54 leaves=55 maxdepth=11
    width 4, sites 64, engine=dedup: observations=2 nodes=175 edges=179
                              dedupHits=5 certified=checkCert (CLOSES)
    --expect-status panic ONLY: REFUSED — "member under pick assignment
      [0, 0, 1, 0, 0] has status ok, outside the declared status set"

So the machine's set is exactly {panic "under-wait", ok 1}: the existing
`l5ExitWindow` ChoiceSite plus the B1 `.opDone` post-op boundary already
admit "main exits while another goroutine is mid-panic" (the same
mechanism that admits `goroutines/wake-then-abort`,
`docs/2026-08-11_latitude-inventory.md` C4 / U-1 / B3). observed ∈
modeled: the machine is right and the row's LANE was wrong — no BUGS
entry; the fix is a re-lane to `membership` with `members=2
statuses=ok+panic` (the wake-then-abort precedent), so gc's
schedule-dependent draw is inside the certified set on every schedule.

## The deterministic sibling

`goroutine-panic-under-wait-no-done` (subject
`goroutinePanicUnderWaitNoDone`): the same shape with NO deferred Done —
nothing wakes main, the unrecovered panic is the only exit. gc 20/20
panic plain (`gc-sibling-plain-20.tsv`), 20/20 -race
(`gc-sibling-race-20.tsv`); machine `engine=dedup` closes at 52 nodes
with the singleton {panic "under-wait-no-done"}. Strict lane.

## Records

`cases.tsv` (row comment + `why`), `baselines/native-full.tsv` (stage
move PASS/- -> PASS/membership + 1 born PASS; 0 PASS->non-PASS),
`docs/language-coverage-ledger.md` §8 (the current-tracked-baseline
paragraph; no §8-lettered movement section — no frontier row moved),
`docs/operational-lessons.md`
(addendum to the coin-flip-gate lesson), `docs/2026-09-03_noodler-report.md`
§8 pointer. Gate transcript tail: `gate-tail-1.txt` (full `ci --diff`),
`gate-tail-2.txt` (fast `ci` on the records tree) — both pre-rebase, at
3383 rows; the post-rebase `ci --diff` tail at 3403 rows is reported in
the round-14 merge train record.
