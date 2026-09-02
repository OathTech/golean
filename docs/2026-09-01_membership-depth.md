# Membership-depth lane: strict-lane depth exposure, the menu-invariant validator, and membership sampling honesty

Date: 2026-09-01/02 (the lane's first worker was stopped by a sandbox
restart; this report is by the resumed worker, built and run from the
WIP snapshot preserved at `refs/snapshots/t4-membership-pre-restart`).
Branch `t4-membership-depth`. Assessment findings addressed: B4/B13
(`docs/assessment/lane-b-lower-bound.md`), C3-F3, D-10
(`docs/assessment/p2-keeps-a2a3bcd.md`), E-D8
(`docs/assessment/lane-e-outsider-review.md`).

**Mandate (unchanged from the brief): assessment plus tooling.** No
baseline moved, no gate changed, no `cases.tsv` edited, no merge, no
push. Everything landed is non-gate lane tooling under `scripts/` plus
one observation-only Lean module outside the semantic core; apparatus
changes are PROPOSED here with the measurements that argue for them.

All decisions below are [AGENT] unless marked [USER].

---

## 0. Headline

| Question | Answer |
|---|---|
| Does the instrumentation change machine behavior? | **No.** `GoLean/GoCore/`, `NativeToIR.lean`, `CLI.lean`, `tools/`, `Corpus/`, `baselines/`, `scripts/ci`, `scripts/diff-coverage` are byte-identical to main (`git diff 7cf19198..HEAD --stat` over those paths is empty). The tracer is a separate `golean choice-trace` subcommand dispatched in `Main.lean`; the default path is untouched (§1). |
| Strict rows whose "adversarial" streams are exhausted before a bound-≥-2 consumption (the pick-0 default takes over, invisibly) | **23 of 2,373 traced strict rows** (all 23 baseline PASS): 15 reach only `appendSpill`/`mapIter` (capacity / map-order latitude), **8 reach scheduling sites** (17–521 scheduling picks vs an 8–10-entry stream). List in §2.3. |
| Menu-invariant validator over the full corpus | **62,048 consumptions, 0 violations, 0 self-check alarms, 0 driver-agreement mismatches** across 2,478 rows × 6 streams. First mechanical modeled ⊆ permitted evidence at the site level; what it does NOT witness is in §3.3. |
| Membership sampling today | 228 `go run` draws per full run (22 rows × 10, 4 rows × 2). With the gate's budget and draw order, **9 of the 22 ten-draw rows exhibit only 1 distinct observation** where 80 draws exhibit 2 (or more); saturation of the two-member scheduling rows takes up to 52–66 alternating draws. Proposal (§4.3): alternate plain/`-race`, stop at the `members=` pin, cap K=32 in `--diff` (measured worst case +6.5 min), K=80 under `--slow`. |
| Routing rule | §5: a strict row is 3-stream-certified only if its default-stream bound-≥-2 consumption count is ≤ 8 (the shortest stream). Otherwise the strict PASS must be earned by a stream the accountant sizes (or by the confluent enumerator), never by the default trajectory dressed as three. Fail-closed shape given. |
| Gate | No behavior-bearing file changed, so only the plain `scripts/ci` was owed; this fresh worktree had no recorded differential/negative run for the plain gate's diff steps to judge, so the FULL `scripts/ci --diff` was run at the tip instead (strictly stronger) and the plain gate re-run after it — both tails in §8. Differential spot-check across all four lanes PASS (§1.3). |

---

## 1. Audit of the inherited instrumentation (mandate item 1)

### 1.1 What the WIP snapshot contained

Commit `2a938c25` (preserved as `refs/snapshots/t4-membership-pre-restart`;
do not delete): `GoLean/ChoiceTrace.lean` (897 lines), a one-line import
in `GoLean.lean`, an 8-line dispatch in `Main.lean`, and three scripts
(`scripts/choice-trace-corpus`, `scripts/choice-trace-summarize`,
`scripts/membership-sampling`). Nothing had been built via `scripts/capped`
(the first worker's `scripts/capped` failed on the bus — `build0.log` in the
lane artifacts) and no report existed. The first worker ran the tracer via
LSP `#eval` on copies of the module (`artifacts/membership-depth/Run*.lean`);
those results are of unverified provenance and were **not** used here — every
number in this report comes from a fresh `scripts/capped lake build golean`
of this tree and a fresh run.

### 1.2 Behavior audit — observation-only, verified

* **Semantic core untouched.** The snapshot's diff stat touches exactly
  six files, none under `GoLean/GoCore/`. Re-verified at the tip:
  `git diff 7cf19198..HEAD --stat -- GoLean/GoCore GoLean/NativeToIR.lean
  GoLean/CLI.lean GoLean/EnumDedup.lean tools/ Corpus/ baselines/ scripts/ci
  scripts/diff-coverage` → empty.
* **Separate CLI subcommand, off unless asked.** `Main.lean` matches
  `"choice-trace" :: rest` and otherwise falls through to `GoLean.CLI.main`
  unchanged; `CLI.main`'s own subcommands are `native-json-run`,
  `observation-eq`, `coverage-observations` — no name collision. Every gate
  invocation (`native-json-run`, `coverage-observations`) reaches code that
  did not change.
* **The tracer only reads the machine.** It drives `stepFn`/`stepMulti` with
  the same picks the machine would draw from the stream (the raw stream
  value; the machine reduces modulo the bound itself) and appends a sentinel
  to detect any accounting drift — the enumerator's existing discipline. It
  uses `partial def` for its driver loops; the module is outside
  `GoLean/GoCore/`, where the charter permits it (as in `CLI.lean`). The
  ci escape-hatch scans (`sorry`/`admit`/`native_decide`/`axiom`, the
  meta-layer scan, the engine-isolation lint) pass on the tip (§8).
* **Build is warning-free** (the gate requires GoLean/ modules to be; the
  first worker's module compiled clean on the first capped build).
* One functional fix was needed: `golean choice-trace --help` returned exit
  2 (unknown option), so `scripts/choice-trace-corpus`'s stale-binary probe
  refused a fresh binary. `--help`/`-h` now print usage and exit 0.

**Restructuring verdict:** none required. The module is already
observation-only; the structure (its own subcommand, imports `CLI` for the
accountant and driver copies, emits no records into the machine) is the
right one and was kept.

### 1.3 Gate and differential unaffected

* Plain `scripts/ci` at the tip: green (tail in §8) — eval tests, escape
  scans, baseline diff of the last recorded run all pass.
* Differential spot-check with the freshly built binary,
  `scripts/capped scripts/diff-one` over one row per lane shape:
  `arrays/array-bounds` (strict/panic), `goroutines/pipeline/two-stage`
  (strict, 44 scheduling picks), `maps/range-first-key` (membership,
  enumerated=3 exhibited=3), `race/negative/increment` (racy),
  `goroutines/buffered-wake/fifo` (confluent, |set|=1 certified),
  `channels/deadlock/send-nil` (deadlock) — **6/6 PASS**
  (`artifacts/membership-depth/resume/spot-check.log`).

---

## 2. Strict-lane depth exposure (mandate item 2)

### 2.1 Instrument

`golean choice-trace` replays one stream in lockstep with the consumption
accountant (`CLI.stepNeeds`/`stepNeedsSeq`, the enumerator's mirror of the
machine's consumption points) and records every consumption: census site
(`ChoiceSite`), bound, the stream value drawn or EXHAUSTED, the realized
pick. `scripts/choice-trace-corpus` runs it over the whole executable
corpus under six streams: the empty (default) stream, the strict lane's
three adversarial streams `9,8,7,6,5,4,3,2,1,0` / `1,3,5,7,9,2,4,6,8,0` /
`5,5,5,5,5,5,5,5` (lengths 10/10/8, `scripts/diff-coverage:808`), and two
seeded 4096-entry pseudo-random streams (`rand:1:4096`, `rand:2:4096`).
`scripts/choice-trace-summarize` aggregates.

Run: 2,506 manifest rows → 28 frontend export refusals (all baseline FAIL,
listed in `export-fail.tsv`) → 2,478 rows traced × 6 streams = 14,868
(row, stream) lines, 0 tracer ERRORs. Fuel 10,000,000 (native-json-run's)
for every row except `goroutines/send-then-spin` (a membership row declared
`nonterm=200,backedge=1` — a spinner that runs to the fuel cap under the
default stream, ~10 min per fuel-out stream at 10M; traced separately at
fuel 1,000,000 → 47,618 `backEdge` consumptions before fuel-out; the other
five streams terminate in 7–9 picks). The corpus runner now has a recorded
`--exclude` for exactly this shape.

**Exhaustion definition used here.** A stream is EXHAUSTED at consumption
`n` when `n ≥ |stream|`; `Choices.consume` then yields 0
(`GoLean/GoCore/State.lean:151-160`). The finding that matters is a
bound-≥-2 consumption drawn AFTER exhaustion: from there the "adversarial"
run is the canonical default trajectory, and the 3-stream invariance check
compares the default run with itself. Width-1 consumptions after exhaustion
(`mapIter`'s done-check at width 1) carry no latitude and are not counted.

### 2.2 Distribution (strict rows, default stream)

2,373 strict rows traced (of 2,401 in the manifest; 2,235 baseline PASS).

| consumptions (default stream) | 0 | 1–8 | 9–10 | 11–32 | 33–128 | >128 |
|---|---|---|---|---|---|---|
| all sites | 2,100 | 247 | 4 | 16 | 4 | 2 |
| bound ≥ 2 only | 2,118 | 230 | 3 | 16 | 4 | 2 |

* 255 strict rows make at least one bound-≥-2 consumption under the default
  stream; 2,118 make none (the strict lane is overwhelmingly choice-free,
  which is what "strict" should mean).
* Per-stream exhaustion with a wide consumption after it: 20 rows on each
  10-entry stream, 23 on the 8-entry stream.
* 20 strict rows make >10 bound-≥-2 consumptions under a random-4096 stream
  (max: `spec-examples-stmt/prime-sieve/eight`, 314 picks).
* Per-site totals over all 6 streams and all lanes: `backEdge` 49,108 (47,615
  of them the spinner), `l1Sched` 5,293, `appendSpill` 3,635, `postOp` 2,001,
  `mapIter` 1,752, `l5ExitWindow` 230, `l2Entry` 18, `l4Waiter` 8,
  `l2Arrival` 3.

### 2.3 The exhausted-case list (23 strict rows, all baseline PASS)

`consumed / wide / exhaustedAt / wideAfterExhaustion` per adversarial
stream; default-stream site profile from `results-*.tsv`
(`artifacts/membership-depth/resume/full/exhausted-strict.tsv` has the
full table).

**(a) Scheduling-family sites reached — 8 rows.** These are concurrent
programs certified in the strict lane. Under the three fixed streams,
everything past pick 8–10 is the default schedule.

| row | default-stream picks (sites) | worst adversarial stream: wide after exhaustion |
|---|---|---|
| `spec-examples-stmt/prime-sieve/eight` | 521 (l1Sched 294, postOp 95, backEdge 131, exit 1) | 514 of 522 |
| `spec-examples-stmt/prime-sieve/five` | 187 (l1Sched 105, postOp 33, backEdge 48, exit 1) | 180 of 188 |
| `goroutines/pipeline/two-stage` | 44 (l1Sched 22, postOp 10, backEdge 12) | 35 of 45 |
| `imported-goose/channel/parallel-search-replace/search-replace` | 42 (l1Sched 22, postOp 5, backEdge 14, exit 1) | 33 of 43 |
| `goroutines/worker-pool/shared-feed` | 32 (l1Sched 15, postOp 9, backEdge 8) | 24 of 32 |
| `goroutines/pipeline/buffered-stage` | 29 (l1Sched 14, postOp 7, backEdge 8) | 21 of 31 |
| `sync/waitgroup-workers-join/workers-join` | 28 (l1Sched 16, postOp 9, backEdge 3) | 18 of 28 |
| `spec-examples-stmt/go-statements/func-literal` | 17 (l1Sched 7, postOp 3, backEdge 6, exit 1) | 7 of 17 |

What the two random-4096 streams add for these 8: none exhausted (the
streams are long enough — 14 to 314 picks drawn), and the observation hash
under both random streams equals the default-stream observation for all 8.
So these rows are schedule-invariant on **three** trajectories (default +
two random), which is real but thin evidence; it is not the ∀-schedule
certificate the confluent lane gives, and the 3-stream gate check adds
nothing past the prefix.

**(b) `appendSpill`/`mapIter` only — 15 rows.** `fmt/fprintf-builder/describe-shape`
(10 spills, max bound 421), `fmt/fprint-writers/fprintf-buffer-shape` (12),
`fmt/sprintf-dyn/{logger-shape,sprint-space-rule}` (14 each),
`fmt/sprintf-dyn/verb-kinds` (13), `fmt/sprintf-verbs/d-width` (12),
`multipkg/mini-raft-twin/{duel 11, elect-propose-commit 32, perturb-picks 18,
perturb-rev 23, starve-node 23}`, `strconv/format-parse/{format-int-vals 22,
format-uint-bases 29, parse-uint-errors 33, parse-uint-range-value 66}`.
These consume the R2 capacity envelope inside string-building shims. The
latitude is capacity, observable only through `cap()`; the random streams
draw every spill at a non-default slot and the observations still match the
default — consistent with these rows not observing capacity. Low routing
risk, but the caption "3-stream invariance" is still false for them past the
prefix.

**The 24th row** — `examples/fibmemo/memosize-ten` exhausts the 8-entry
stream at its 9th `mapIter` consumption, but that consumption is width 1 (no
latitude); not counted.

### 2.4 Observation variance across the six streams

Exactly one strict row varies: `channels/select-select/beside-loop` — `ok`
under default and both random streams, `unsupported` ("select-with-select
rendezvous (unmodeled this slice)") under all three adversarial streams.
This is the tracked baseline **FAIL/nondet** row; the gate already catches
it (as D-10 item 2 notes, a refusal under a variant stream is reported as
`nondet` — mislabelled but fail-closed). The tracer's status/observation
agreed with `native-json-run --choices 5,5,5,5,5,5,5,5` directly. Confluent
rows: 0 vary (as their certificate requires). Membership rows: 21 of 26
show ≥2 distinct observations across the six streams; the six fixed
trajectories are not an enumeration and are not read as one.

### 2.5 Confluent-lane note

17 of 58 confluent rows also exhaust the adversarial streams at scheduling
sites. Harmless: the confluent lane's PASS is the enumerator's |set|=1
certificate over all schedules; the 3-stream check there is redundant with
the enumeration, not load-bearing.

### 2.6 Cross-check against the baseline

134 traced rows end in a machine refusal (`unsupported`/`stuck`/`internal`/
`error`, or a `fatal` the row does not expect) under some traced stream;
**all 134 are non-PASS in the tracked baseline.** No PASS row hides a
refusal on any of the six streams. (The 7 sync-misuse rows whose expected
status IS `fatal` are matched by the differential like any status; the
summarizer classifies them against the manifest's expected status.)

---

## 3. The menu-invariant validator (mandate item 3)

### 3.1 What it checks, per consumption

At every consumption the tracer recomputes, from the PRE-STATE and by a
second deliberately plain derivation (not by reading back the machine's
menu function), the width the latitude census states for the site, and
checks the pick against it:

| site | census row | stated width recomputed | structural invariants also checked |
|---|---|---|---|
| `l1Sched` | C1 | \|runnable\| | menu is a permutation of the runnable set, distinct, live; menu = `runnableIdxs` in goroutine order |
| `backEdge` | C2 | \|runnable\| | as above; slot 0 = the current goroutine |
| `postOp` | C3 | \|runnable\| | as above; slot 0 = the issuer |
| `l5ExitWindow` | C4 | 2 | window opens only with a runnable other goroutine and main at its terminal |
| `l4Waiter` | C5 | #parked partners on the opposite side of the arriving op's channel (select clauses counted individually) | every candidate is a parked goroutine ≠ the arriver; distinct; ≥2 (a singleton pairs without a pick) |
| `l2Entry` | C6 | #cell-ready clauses | 2 ≤ commits ≤ #clauses |
| `l2Arrival` | C6 | #clauses cell-ready or with a parked partner | 2 ≤ outcomes ≤ #clauses |
| `l1Sched`/`postOp`/`backEdge` | C8 | (C8 declares zero new sites — sync contention is L1; the scheduler checks above are the C8 check) | — |
| `mapIter` | E9 | live-unproduced candidates + stop slot iff no mandatory (never-removed start key) candidate remains | candidates ≤ live entries; stop not taken while a mandatory entry remains |
| `appendSpill` | R2 | `upper − newLen + 1` with `upper = appendSpillUpper` (the DECLARED envelope) | spill only when newLen > cap; newLen ≤ growth ≤ upper; slot map is a bijection onto [newLen, upper] (skipped above width 8192); slot 0 = the growth-formula point |

Plus, for every site, `pick < max 1 bound`. Three self-checks keep the
tracer honest about being a mirror: (a) its site-tagged bound must equal
`CLI.stepNeeds`'s at every consumption; (b) a step fed exactly the accounted
picks plus one sentinel must leave the sentinel alone (drift either way is
an alarm); (c) the machine's own `StepEvent.picks` records
(`Choices.consumeAtE` at the pool-layer sites) must equal the tracer's
records. And per (row, stream) the run's status and consumption count are
pinned against `CLI.enumRunProgram`'s leftover meter and the real engine's
`runProgramPoolIntsM` observation.

### 3.2 Result

Full corpus, six streams: **62,048 consumptions checked; 0 menu-invariant
violations; 0 self-check alarms; 0 driver-agreement mismatches.** Site
coverage of the check: every census site was exercised (§2.2 per-site
totals), `l2Arrival` least (3 consumptions) and `l4Waiter` (8) — thin at
those two; the membership lane's certified trees exercise them far more
(C5's 336 width-2 L4 sites in first-come's tree) but without this check.

This is the first mechanical evidence, at the site level, of the
modeled ⊆ permitted direction: every choice the machine offered on these
~62k occasions had the width the census declares and satisfied the
declared slot structure. Before this, E-D8's observation stood: the width
at every enveloped row was an unaudited design assertion.

### 3.3 What it does NOT witness (stated so the claim is not over-read)

* **Menu CONTENT beyond bound and structure.** That the goroutine at slot k
  is one the spec would let run is checked only as "it is runnable per the
  machine's `threadRunnable`" — runnability is the machine's own notion,
  and the spec is silent on which runnable goroutine runs, so this is the
  most the check can be. Likewise clause readiness uses the machine's
  `clauseReady`: the C6 check is a consistency check between two machine
  functions, not an oracle.
* **R2's upper end.** The spec's latitude is unbounded; the envelope is a
  declared pragmatic subset. The check is against the declaration
  (`appendSpillUpper`), not against Go.
* **Permitted ⊆ modeled** (the lower bound) — that is the differential's
  job, unchanged.
* **Reachability.** The validator sees only the consumptions the six
  streams reach. Sites reached rarely (`l2Arrival`, `l4Waiter`) are checked
  on few occasions.
* **Anything about the frontend.** Widths are checked on the machine's
  state; a lowering that mis-shapes a program is invisible here.

---

## 4. Membership sampling honesty (mandate item 4)

### 4.1 Today's budget

`run_membership_case_rows` (`scripts/diff-coverage:1084-1112`) draws
`samples` plain `go run` observations then `samples` under `-race`
(default `samples=5`; the four `slices/*` version-tracking rows declare
`samples=1`). 26 membership rows → **228 oracle draws per full
differential** (22 × 10 + 4 × 2). PASS = every draw ∈ the enumerated set;
`exhibited`/`unexhibited` counts are caption metadata, never a pass
criterion (correct: too-wide has no oracle). The question is whether 10
draws describe the oracle's support honestly in that caption.

### 4.2 Measurement

`scripts/membership-sampling` (lane tooling, read-only) draws 40 plain +
40 `-race` per row with the gate's exact oracle invocation and checks each
against the row's enumerated set. Two independent 80-draw runs exist: the
first worker's (`artifacts/membership-depth/sampling/`, Go side trusted —
`go run` does not depend on the golean build; enumeration side re-derived
here) and this worker's fresh run (`artifacts/membership-depth/resume/sampling/`,
golean from this tree's capped build, go1.26.5). `scripts/membership-sampling-sweep`
reduces both (`artifacts/membership-depth/resume/sampling-sweep.txt`).

Fresh run, all 26 rows: **2,080 draws, every classified draw a member of
its row's enumerated set** (the one exception is
`sync/atomic-frontier/mp-litmus`, baseline FAIL — the frontend refuses
`atomic.StoreInt32`, so there is no set; gc shows 2 observations there).
Cost: 0.58–0.86 s/draw under concurrent load (0.55 s/draw in the first
worker's quieter run); the three `wake-window`/`wake-then-abort` rows run
0.06–0.22 s/draw.

Enumerated 443 members across the 26 rows; 52 distinct observations
exhibited in 80 draws (E-D8 measured 45 of 441 under the gate budget).
The gap is R2 by construction: the four `slices/*` rows enumerate 29–300
capacities and gc realizes 1–2.

**Where the 10-draw budget is a point-mass.** Under the gate's draw order
(5 plain, then 5 race), 9 of the 22 ten-draw rows exhibit only 1 distinct
observation in at least one run while 80 draws exhibit 2 (or more):
`goroutines/sched-dependent/len-handoff` (2nd member at draw 51),
`goroutines/sched-dependent/select-default-handshake` (48),
`goroutines/select-wake-multi` (66), `race/litmus/sb-chan` (48; 2 of 3
members), `maps/added-entry-count` (12), `imported-goose/channel/google-search`
(2 of 6 at gate; 5–6 of 6 by draw 50–56), `maps/jitter-draw` (3–4 of 5 at
gate; 5 of 5 by 22–52), `sync/atomic-frontier/mp-litmus` (62),
(`goroutines/sched-dependent/first-come` is NOT among them: both members
by draw 6–7 in both runs.) On the scheduling rows every late member came
from a `-race` draw: plain `go run` is a point-mass there (distinctPlain = 1
on 13 of the 22 ten-draw rows) and `-race` is the only perturbation source
— which is why the current order (plain first) is the worst order for a
small budget. On the map rows (Go's own per-execution randomization) plain
draws move too.

Rows gc never moves off one observation in 160 draws, though the machine
enumerates more: `goroutines/wake-then-abort` (BUG-044's excluded panic
member: 1/100 at 50k-iteration delay), `sync/mutex-order/acquisition-order`
(certified {2 members}, gc shows 1), `maps/delete-readd-during-range`
(3 members, gc shows 1), `goroutines/send-then-spin` (1 member — fine), the
four `slices/*` rows (1–2 of 29–300). For these no budget rule reaches the
pin; the honest caption is the exhibited count, which is what the lane
already prints.

### 4.3 Proposed budget rule (measured; NOT applied — `cases.tsv` unchanged)

**Rule.** Per membership row: alternate plain and `-race` draws (plain,
race, plain, race, …); stop early when the number of distinct observations
reaches the row's `members=` pin; otherwise stop at K draws. Report
`draws=` alongside `exhibited=` in the PASS detail. Rows without a
`members=` pin have no early stop (they draw K) — one more reason to finish
B13's pinning (10 of 26 rows are unpinned today).

**Why alternate.** In both runs the alternating order reaches saturation
earlier than the gate order on every row where they differ (e.g. sb-chan
16 vs 48, select-default-handshake 16 vs 48, len-handoff 22 vs 51,
select-wake-multi 52 vs 66, google-search 20–32 vs 50–56) — because the
second member almost always comes from `-race`, which the gate order
reaches only at draw 6.

**K-sweep** (52 (row, run) samples; 32 of them pinned rows; a pinned sample
"reaches" when the pin is hit within K under the alternating order):

| K | pinned samples reaching the pin within K | mean draws/row | total draws, 26 rows | est. wall at 0.7 s/draw |
|---|---|---|---|---|
| 10 (today's count, better order) | 18/32 | 7.6 | 197 | 2.3 min |
| 16 | 19/32 | 11.5 | 299 | 3.5 min |
| 24 | 20/32 | 16.6 | 430 | 5.0 min |
| **32** | **21/32** | **21.5** | **558** | **6.5 min** |
| 48 | 21/32 | 31.0 | 806 | 9.4 min |
| 64 | 22/32 | 40.3 | 1,048 | 12.2 min |
| 80 | 22/32 | 49.6 | 1,288 | 15.0 min |

10 of the 32 pinned samples never reach the pin in 80 draws (the
gc-immobile rows above); the reachable ceiling is 22/32. K=32 captures
21 of those 22 at +6.5 min on the `--diff` path (today: 228 draws ≈ 2.7
min); the one it misses (`select-wake-multi`, saturating at 52) argues
for **K=80 under `--slow`**, where full re-certification already spends
minutes per slow-tier row. The rule never changes what PASSes — membership
is still every draw ∈ set — it changes how much the `exhibited=` caption is
allowed to under-report, and it makes the budget a recorded number
(`draws=`) instead of an implicit 10.

**Cost as measured on 5 rows (fresh run, 80 draws each):**
`google-search` 49 s, `jitter-draw` 68 s, `len-handoff` 58 s,
`select-wake-multi` 54 s, `sb-chan` 69 s — i.e. 0.6–0.86 s/draw; under the
K=32 rule these five would cost 20 s (pin 6 not reached in 32: 5 of 6) /
27 s (no pin: draws K) / 16 s (pin reached at draw 22) / 22 s (pin at 52,
so K) / 28 s (pin 3 not reached: 2 of 3).

---

## 5. Routing rule proposal (mandate item 5)

**The data.** The strict lane's nondeterminism tripwire is the 3-stream
invariance check, whose streams are 10/10/8 entries; `Choices.consume`
defaults to slot 0 on exhaustion. §2 measures exactly which rows outrun it:
23 of 2,373 (8 at scheduling sites). The remaining 2,350 strict rows are
fully covered — 2,118 draw nothing at bound ≥ 2, 232 draw ≤ 8 wide picks.

**Rule (fail-closed shape).** A strict PASS is a two-part claim — Go
equality on the default trajectory AND invariance across the adversarial
streams — and the second part is only made when the streams cover every
bound-≥-2 consumption. So:

1. Measure the row's default-stream bound-≥-2 consumption count `w` (the
   accountant already computes it; the tracer reports it as `wide`).
2. If `w ≤ 8` (the shortest fixed stream), the existing check stands as is.
3. If `w > 8`, the fixed streams do NOT certify invariance; the strict PASS
   is **refused with the cause named** ("strict row draws `w` wide picks;
   the 3-stream invariance check covers 8 — route to `confluent`, or
   declare depth") unless the row carries one of:
   * `lane=confluent` — the enumerator certifies |set|=1 over all schedules
     (the honest home for the 8 scheduling-family rows; cost is the
     enumeration — `prime-sieve/eight` at 521 picks may not fit the fail-loud
     caps, in which case it should not be in a lane that claims invariance);
   * an explicit per-row `depth=N` with `N ≥ w`, under which the gate
     derives invariance streams of length `N` from a seeded generator
     (e.g. `rand:<seed>:N`, seeds recorded in run meta) instead of the
     fixed prefix — the (S) fix B4 asks for, made honest by tying N to the
     measured `w` rather than to a guess.
4. The variant runs' exit status is checked (D-10 item 2): a refusal under
   a variant stream is reported as a refusal, not as `nondet`.

Fail-closed properties: no default — a row over the covered depth with no
declaration is red, not strict-green; the declared `depth=` must dominate
the measured `w` (a row that grows past its declaration goes red at the
next run, naming the numbers); `--diff` output records `wide=` and
`depth=` per strict row so the number is derivation-anchored.

**Immediate consequence for the 8 rows if the rule were adopted:** they
would go red until routed. That is the rule working — a hand-classified
concurrent program with 17–521 scheduling picks was never
invariance-certified past pick 8–10.

**What NOT to do:** silently lengthen the three fixed streams. Longer fixed
streams move the horizon; they do not tie it to the row, and the failure
mode stays invisible.

---

## 6. Proposed apparatus changes (with evidence; none landed)

| # | change | evidence | cost | status |
|---|---|---|---|---|
| P1 | Strict-lane depth guard (§5): refuse strict PASS when `wide > 8` without `confluent`/`depth=`; seeded streams of declared length | §2.3: 23 rows (8 scheduling) outrun the fixed streams | gate change (diff-coverage) + 8–23 manifest rows to route/declare | PROPOSED — [USER] gate decision |
| P2 | Membership sampling rule (§4.3): alternate plain/race, stop at `members=`, K=32 (`--diff`) / K=80 (`--slow`), print `draws=` | §4.2: 9 of 22 rows point-mass at 10 draws in gate order; saturation up to 52–66 | +6.5 min on `--diff`; membership-lane code only | PROPOSED — [USER] gate decision |
| P3 | Pin `members=` on the 10 unpinned membership rows (B13) | needed for P2's early stop; 4 `slices/*` rows should pin the enumerated width, `maps/*` their certified sets | manifest rows only | PROPOSED |
| P4 | Run `scripts/choice-trace-corpus` as a periodic (non-gate) audit; keep zero violations/alarms as the standing expectation | §3.2 | ~12 min wall at `--jobs 6` | landed as tooling; scheduling is a [USER] call |
| P5 | Report the variant run's status in the strict invariance check (D-10 item 2) | §2.4 the one VARIES row is a refusal labelled `nondet` | one-line gate change | PROPOSED |

---

## 7. What landed on this branch (lane tooling only)

* `GoLean/ChoiceTrace.lean` + `Main.lean` dispatch + `GoLean.lean` import —
  the `golean choice-trace` tracer/validator (observation-only; §1).
* `scripts/choice-trace-corpus` — corpus runner (wire export mirroring the
  gate, chunked/resumable tracing, recorded `--exclude`).
* `scripts/choice-trace-summarize` — the tables in §2–§3 (refusals
  classified against the manifest's expected status; exhausted rows split
  by site family).
* `scripts/membership-sampling` — the oracle-draw instrument (§4.2).
* `scripts/membership-sampling-sweep` — saturation + K-sweep reduction
  (§4.3).
* This report.

Nothing under `GoLean/GoCore/`, `tools/`, `Corpus/`, `baselines/`,
`scripts/ci`, `scripts/diff-coverage` changed.

Artifacts (gitignored, this worktree): `artifacts/membership-depth/resume/`
— `full/` (results-0..6.tsv, summary.txt, exhausted-strict.tsv,
exhausted-confluent.tsv, export-fail.tsv, batch.tsv, wires), `sampling/`
(per-row draws, observations, summary.tsv, provenance.txt),
`sampling-sweep.txt`, `spot-check.log`, `ci-plain.log`, `build1.log`. The
first worker's artifacts remain under `artifacts/membership-depth/` (not
used for any number here).

Reproduce: `GOLEAN_MEM_MAX=32G scripts/capped lake build golean`, then
`scripts/choice-trace-corpus --jobs 6 --exclude goroutines/send-then-spin`
(+ the spinner alone at `--fuel 1000000`), `scripts/membership-sampling
--draws 40`, `scripts/membership-sampling-sweep --manifest <manifest>
<sampling-dir>...`.

---

## 8. Gate tail

This branch's Lean change is an observation-only module outside the core
plus a `Main.lean` dispatch; no behavior-bearing file changed, so the plain
gate is the owed one. The first plain run in this fresh worktree failed
closed on exactly one step — `negative baseline diff (NO recorded negative
run)` — because no negative/differential run had ever been recorded here
(the plain gate judges the LAST recorded run; the only one present was the
6-row spot-check of §1.3, which the differential step correctly reported
as "6 case(s) run … match"). Rather than record just the negative run, the
full `scripts/ci --diff` was run at the tip (records both), then the plain
gate again.

`scripts/capped scripts/ci --diff` at `a367ed8a` (the three tooling
commits; the only uncommitted file during the run was this report, hence
the gate's honest "DIRTY tree" note — it certifies the worktree state,
which differs from `a367ed8a` by this untracked docs file alone). Full run:
2,506/2,506 differential rows and 390/390 negative rows match the tracked
baselines; no row moved.

```
no regression: 390 case(s) run in negative-latest.tsv match baselines/negative-full.tsv
no regression: 2506 case(s) run in latest.tsv match baselines/native-full.tsv
  note build parallelism: cap 32G -> LEAN_NUM_THREADS=4 (cap/8G, floor 2; 32 cores on this box)
  ok   oracle toolchain (go1.26.5 = pin)
  ok   escape-hatch preflight
  ok   meta-layer escape hatches (allowlist empty since the repo split)
  ok   escape-hatch addendum (no decide +native / native-config spellings)
  ok   bug-index cross-check
  ok   feature-coverage (no dead tags)
  ok   spec-anchor citations resolve at the pin
  ok   lane-validation fixtures (manifest gates reject bad shapes)
  ok   imported-goose verbatim (above-marker bytes = pinned upstream)
  ok   engine-isolation (core ↛ EnumDedup)
  ok   core build (warning-free)
  ok   frontend pins (realized init-order deviation + twin wire = pinned bytes)
  ok   import-goose fixtures (importer + verbatim guard reject bad shapes)
  ok   frontend unit tests
  ok   eval tests (141 ok)
  ok   differential run completed (exit 1; failing-set judged by baseline diff)
  ok   lane-validation fixtures incl. harness half (F4/F6/B3-B5)
  ok   negative run completed (exit 0; set judged by baseline diff)
  ok   Tests/FloatVectors.lean = fresh hardware-oracle regeneration (byte-exact)
  ok   inittask-std.tsv = fresh gc-derived regeneration (header at pin; byte-exact modulo date line)
  note negative baseline diff matched (390 case(s)) but the record was made on a DIRTY tree (git_dirty=true) — certifies that worktree state, not a commit
  note baseline diff FULL (2506/2506, no regression) but recorded on a DIRTY tree (git_dirty=true) — certifies that worktree state, not a commit
  note reconciler: 2 finding(s), 0 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
```

Plain `scripts/capped scripts/ci` at the same tip, judging the run just recorded (this report still the only untracked file; the report commit that follows is docs-only and changes nothing the gate checks):

```
no regression: 390 case(s) run in negative-latest.tsv match baselines/negative-full.tsv
no regression: 2506 case(s) run in latest.tsv match baselines/native-full.tsv
  note build parallelism: cap 32G -> LEAN_NUM_THREADS=4 (cap/8G, floor 2; 32 cores on this box)
  ok   oracle toolchain (go1.26.5 = pin)
  ok   escape-hatch preflight
  ok   meta-layer escape hatches (allowlist empty since the repo split)
  ok   escape-hatch addendum (no decide +native / native-config spellings)
  ok   bug-index cross-check
  ok   feature-coverage (no dead tags)
  ok   spec-anchor citations resolve at the pin
  ok   lane-validation fixtures (manifest gates reject bad shapes)
  ok   imported-goose verbatim (above-marker bytes = pinned upstream)
  ok   engine-isolation (core ↛ EnumDedup)
  ok   core build (warning-free)
  ok   frontend pins (realized init-order deviation + twin wire = pinned bytes)
  ok   import-goose fixtures (importer + verbatim guard reject bad shapes)
  ok   frontend unit tests
  ok   eval tests (141 ok)
  note negative baseline diff matched (390 case(s)) but the record was made on a DIRTY tree (git_dirty=true) — certifies that worktree state, not a commit
  note baseline diff FULL (2506/2506, no regression) but recorded on a DIRTY tree (git_dirty=true) — certifies that worktree state, not a commit
  note reconciler: 2 finding(s), 0 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
```
