# BUG-114 capture — the wake-then-abort second-report-boundary shape

Lane `records/bug114-capture-0921`, worktree `.claude/worktrees/bug114-capture`,
branch off main `769bbf23`. **RECORDS ONLY — no observer code was changed**
(`tools/coverageharness/` is trusted surface #2; a widening is the follow-up
lane's, with its own audit ask). [AGENT] worker, 2026-09-21.

Task: capture the gc report shape that made the abort observer refuse draw
61/80 of `goroutines/wake-then-abort` at round 45's slow gate
(«abort classification: additional or unknown report boundary after selected
origin, refused»), classify it against the pinned runtime, and propose — not
implement — either a classification rule or a named apparatus limit.

**Headline: the second-boundary shape was NOT reproduced on the row in 73,600
recorded draws (+1,140 un-recorded smoke draws) across 11 configurations.**
The refusal text itself was reproduced end to end on a purpose-built
two-abort probe, and the set of report shapes that can produce it is pinned
from the runtime source. Both results are below, with their derivations.

## Environment

- Oracle pin `go1.26.5` (`go version` = `go1.26.5 linux/amd64`); reference
  checkout `deps/go` @ `c19862e5f8415b4f24b189d065ed739517c548ba`
  (`scripts/setup-deps --from /home/dev/projects/golean --only go`).
- Box: 32 logical CPUs. All scratch under the worktree's `.tmp/`
  (gitignored); `GOCACHE=.tmp/gocache`.
- No lake/lean was run; the differential runners were not invoked (they build
  the Lean binary). The oracle side was driven directly, with the byte-exact
  environment `scripts/diff-coverage`'s `go_run_oracle` uses.

## Commands

```sh
# 1. the oracle package the gate runs (coverageharness generates it; the
#    crash hook _goleanSetupCrash is what authenticates the report)
go build -o .tmp/coverageharness ./tools/coverageharness
.tmp/coverageharness --input Corpus/coverage/exec/goroutines/wake-then-abort/main.go \
    --out .tmp/gorun --subject wakeThenAbort --expected-status ok --args -

# 2. build once, loop the binary (the volume path)
cd .tmp/gorun && go build -o ../subj_plain . && go build -race -o ../subj_race .

# 3. every draw, in a directory holding a freshly truncated oracle.crash and
#    oracle.registered, with the gate's environment:
env GO111MODULE=off GOFLAGS= GODEBUG=panicnil=0 GOTRACEBACK=system \
    [GOMAXPROCS=<n>] <binary>              # or: go run .   (the gate's driver)

# 4. classification, exactly as scripts/diff-coverage's oracle_observer does
.tmp/coverageharness --abort-message <stderr> --expected-status panic \
    --crash-report <oracle.crash> --crash-registered <oracle.registered>
.tmp/coverageharness --split-stderr  <stderr> --expected-status panic \
    --crash-report <oracle.crash> --crash-registered <oracle.registered>
```

Drivers: `.tmp/drive.py` (binary loop), `.tmp/drive_gorun.py` (`go run .`
loop) — scratch, not tracked. Each draw is bucketed on the tuple (exit
status, stdout class, address-normalised stderr skeleton, address-normalised
crash-file skeleton, **raw count of the three boundary tokens in stderr and in
the crash file**); the boundary counts are computed on the raw bytes of every
draw, so the "0 draws with >1 report boundary" column below is over all
draws, not over the saved representatives.

## 1. What the row actually does (counts)

`counts.tsv` in this directory; reproduced here.

| configuration | driver | draws | abort, `42` on stdout | abort, no stdout | clean exit 0 (`ok 42`) | draws with >1 report boundary |
|---|---|---|---|---|---|---|
| plain, GOMAXPROCS=1, sequential | binary | 1000 | 0 | 1000 | 0 | **0** |
| -race, GOMAXPROCS=1, sequential | binary | 1000 | 0 | 1000 | 0 | **0** |
| plain, GOMAXPROCS=2, sequential | binary | 1000 | 766 | 234 | 0 | **0** |
| -race, GOMAXPROCS=2, sequential | binary | 1000 | 436 | 564 | 0 | **0** |
| plain, GOMAXPROCS=4, sequential | binary | 1000 | 477 | 523 | 0 | **0** |
| -race, GOMAXPROCS=4, sequential | binary | 1000 | 567 | 433 | 0 | **0** |
| plain, GOMAXPROCS=8, sequential | binary | 1000 | 518 | 482 | 0 | **0** |
| -race, GOMAXPROCS=8, sequential | binary | 1000 | 558 | 442 | 0 | **0** |
| plain, GOMAXPROCS unset (=32), 16 concurrent loops | binary | 32000 | 13081 | 18919 | 0 | **0** |
| -race, GOMAXPROCS unset (=32), 8 concurrent loops | binary | 24000 | 9712 | 14288 | 0 | **0** |
| plain, GOMAXPROCS unset (=32), 16 concurrent loops | `go run .` | 9600 | 1996 | 7547 | 57 | **0** |

Total recorded: **73,600 draws** (45,600 plain, 28,000 `-race`). A further
1,140 draws were run as smoke before the bucket labels were fixed (60 plain
GOMAXPROCS=8, 60 `-race` GOMAXPROCS=8, 1000 plain GOMAXPROCS unset, 20
`go run`); their boundary counts were also all 1. Grand total **74,740**,
**0** with a second boundary.

Three outcome classes were observed, all with exactly one report boundary:

1. **abort, `42` on stdout** — main runs between the worker's send and the
   worker's panic, prints the observation JSON
   `{"schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":42}]}`,
   then blocks forever in `runtime.main`'s `panicking != 0` park
   (`deps/go/src/runtime/proc.go:319`) while the worker's report prints; the
   process exits 2. **This is the class the refusing gate draw was in** (the
   entry records that draw's stdout as exactly this JSON). Artifact:
   `row-abort-42-printed.stderr` (3,708 B, includes `go run`'s
   `exit status 2` trailer).
2. **abort, no stdout** — the worker panics before main is scheduled past the
   receive. Artifact: `row-abort-silent.stderr` (4,427 B).
3. **clean exit 0** — main wins the exit window entirely
   (`panicking.Load() == 0` at `proc.go:319`, then `exit(0)` at
   `proc.go:329`): stdout carries the same JSON, **stderr is empty and the
   crash file is empty**. 57/9600 under `go run` with 16 concurrent loops;
   never seen with the bare binary. No artifact is shipped — both captured
   byte streams are empty; the stdout is the JSON quoted above.

Note the absence of a fourth class: no draw produced a **truncated** report
(main's `exit(0)` landing in the middle of the worker's printing). Every
report in 74,740 draws was complete.

For the crash-channel copy, `len(oracle.crash) == len(stderr) - len("exit status 2\n")`
in every abort draw: the authenticated report is exactly the stderr suffix, as
`checkedAbortView` requires. The row's own `.crash` files are therefore not
shipped separately (they are the shipped `.stderr` minus the trailer).

## 2. The second-boundary shape: not observed on the row

`tools/coverageharness/crashview.go` `originKind` refuses when, **after the
selected origin's trace-header line**, the authenticated report still contains
`panic: `, `fatal error: ` or `\nruntime stack:`. In 74,740 draws of this row
no report contained a second occurrence of any of the three tokens. A shape
that was not observed is not described here.

What CAN put one there is settled from the pinned source, and the enumeration
is exhaustive (`deps/go/src/runtime/`, go1.26.5 @ `c19862e5f8`):

| token | every printer at the pin |
|---|---|
| `panic: ` | `printpanics` (`panic.go:747`) — the panic chain of one abort; and the four bad-context guards in `gopanic` (`panic.go:820, 827, 833, 842`), each of which prints `panic: <val>` and immediately `throw`s ("panic on system stack" / "panic during malloc" / "panic during preemptoff" / "panic holding locks") |
| `fatal error: ` | `throw` (`panic.go:1224`) and `fatal` (`panic.go:1248`) — nowhere else |
| `runtime stack:` | `dopanic_m` (`panic.go:1587`), only when the crashing g **is** the M's `g0` |

Every one of these is on the terminal path, and the terminal path is
serialised: `startpanic_m` case 0 (`panic.go:1530-1536`) sets `m.dying = 1`,
does `panicking.Add(1)`, takes `paniclk` and freezes the world; `dopanic_m`
releases `paniclk` at `panic.go:1604` and, if `panicking.Add(-1) != 0`
(`panic.go:1606`), the first M blocks forever on the `deadlock` mutex so the
other one can finish printing. All printing is under the global `debuglock`
(`print.go` `printlock`), so two reports concatenate, they never interleave.

Hence: **a boundary token after the selected origin's trace header means a
second terminal event started printing after the first report's traceback.**
Two sub-shapes are reachable:

- **(a) a second, complete report from another M.** The second M was parked in
  `startpanic_m` case 0 on `lock(&paniclk)`; when the first M unlocks, it
  prints its own `panic: …` or `fatal error: …` report with its own trace
  header and exits 2. Two independent origins. **Exhibited** below.
- **(b) a same-M continuation.** A `throw` on the M that is already printing
  (`m.dying == 1`) prints `fatal error: <msg>` (`panic.go:1224`) and then
  `startpanic_m` case 1 prints the literal line `panic during panic`
  (`panic.go:1544`) and dumps again. One origin; the trailing fragment is the
  runtime failing to finish its own diagnostic. **NOT observed in this lane** —
  named here because the source reaches it, not because it was seen.

For `goroutines/wake-then-abort` specifically: the program has exactly one
panic site and no `fatal`/`throw` of its own, and the generated harness's
`main` can only panic if `json.Encoder.Encode` to stdout fails (stdout is a
regular file under the gate). So a shape-(a) second **`panic: `** report is
not reachable from the program text; any second terminal event on this row
must be runtime-internal (a `throw`). **Which token the gate's draw 61 carried
is NOT determined** — the entry records only the classification text and a
stderr snippet truncated at the harness's quote width, and the full stderr was
lost. This lane did not recover it and does not guess it.

## 3. The refusal, reproduced (probe, not a corpus row)

`probe-two-abort.report` (9,588 B) is the authenticated crash-channel copy of
a real shape-(a) report: a throwaway probe (`.tmp/probes/p1`, eight goroutines
released from one channel and all panicking; the same `zz_golean_crash.go`
hook, the same environment) that produced two complete `panic:` reports in one
crash file — `panic: probe concurrent abort` at line 1 and again at line 159,
the second with its own `goroutine 23 … [running]:` header. It is a PROBE, not
a fixture: it is not in `Corpus/`, and it makes no claim about the row.

Fed to the observer it reproduces the gate's text exactly
(`refusal-repro.txt`, sections C/D):

```
abort classification: additional or unknown report boundary after selected origin, refused
EXIT=3
```

for both `--abort-message` and `--split-stderr`. The same transcript's
sections A/B are the positive control: two real draws of the row classify
cleanly, `"worker abort in the private segment"` with an empty `output`,
EXIT=0.

## 4. Attributable, or not

- **Shape (a) is not attributable and must stay refused.** Two independent
  aborts, two origins; there is no single terminal event to observe, and
  picking the first would be a guess. The current refusal is correct here.
- **Shape (b) would be attributable.** One origin; the panic message and its
  trace header are already selected and authenticated; the trailing
  `fatal error: …` + `panic during panic` is the runtime's own report that it
  could not complete the dump. The observable status (`panic`, message
  `worker abort in the private segment`) is fully determined by the bytes
  before the failure.

Since the gate's draw was not recovered, **this evidence does not license a
widening.** It licenses exactly one of two follow-ups, chosen by which shape a
future capture shows.

## 5. Proposal for the observer lane (NOT implemented here)

### (a) If a shape-(b) instance is captured — the rule

In `crashview.go` `originKind`, after `pinnedTraceKind` succeeds, replace the
blanket `bytes.Contains(tail, …)` with a two-way split of the tail:

1. **clean tail** — no token: classify as today.
2. **same-M continuation** — the tail's first token occurrence is a
   `fatal error: ` at the start of a line, and the line immediately following
   the `fatal error: <msg>\n` line is exactly `panic during panic`
   (un-indented, at a line start). Then the origin stands: kind/message come
   from the head, and the trailing fragment is reported as a named,
   non-fatal-to-classification remainder.
3. **anything else** — refuse, with today's message.

Two cautions the implementing lane must not skip:

- The head's indentation argument (`printpanics`/`printindented` TAB-indent
  every payload continuation) is what makes the marker unforgeable, and it is
  currently applied **only to `head`**. In the tail, un-indented lines are
  normal (every traceback frame header is one), so the rule must anchor the
  marker positionally — immediately after the `fatal error:` line — and must
  require it un-indented. A payload newline in any panic value renders as
  `\n\t`, so a program that panics with a value containing
  `\npanic during panic` cannot put an un-indented copy into the report.
- The rule reads only bytes of the authenticated crash-channel copy, so A-R6
  (no unauthenticated read) is preserved. It must stay that way: do not reach
  for raw stderr to disambiguate.

Controls the lane owes (the L4 observer rules: a new shape gets a positive
control AND a forgery control):

- **positive** — the captured shape-(b) report ⇒ kind `panic`, message = the
  origin's, `output` = the bytes before the report. (A hand-built fixture is
  acceptable only if a captured instance is unavailable, and must say so.)
- **forgery 1** — `probe-two-abort.report` in this directory (a genuine
  shape-(a) two-abort report) ⇒ still refused by name.
- **forgery 2** — the shape-(b) report with the `panic during panic` line
  deleted ⇒ refused (the marker is the discriminator, not the
  `fatal error:` token).
- **forgery 3** — a report whose second fragment is a complete independent
  report (own `goroutine N … [running]:` header) with a `panic during panic`
  line spliced in ahead of it ⇒ refused (the marker must sit immediately after
  the `fatal error:` line, before any further trace header).
- **forgery 4** — a program-printed `panic during panic` inside a panic
  payload (renders indented) ⇒ refused.

### (b) The interim, and the correction the fix plan needs

Until a shape-(b) capture exists, keep the refusal and record the exposure as
a named apparatus limit. **BUG-114's own fix plan says "a `params` note"; that
is not implementable as written**: `scripts/diff-coverage`'s
`parse_lane_params` fails closed on any key outside
`{width, sites, cap, work, members, statuses, tier, backedge, nonterm, engine}`
("unknown lane param key"), and every remaining key must be a positive
integer. A free-text limit cannot live in `params`. It belongs in the row's
free-text `why` column in
`Corpus/coverage/exec/goroutines/wake-then-abort/cases.tsv`, e.g.

> APPARATUS LIMIT (BUG-114): a gc draw whose authenticated report carries a
> second terminal event (`panic: ` / `fatal error: ` / `runtime stack:` after
> the selected origin) is REFUSED by the abort observer and reds the row; the
> refusal is oracle-side classification coverage, not a machine or oracle
> disagreement. Not reproduced in 74,740 isolated draws
> (`docs/evidence/2026-09-21_bug114-capture/`); seen once at K=80 under a
> saturated slow gate (train r45).

On `Cases:`/`Pinned-by:` under `scripts/check-bugs.sh`: BUG-114 is
`Pinned-by: none` with no `Cases:` line, which the checker accepts (only
`open` + `Pinned-by: differential` entries are required to list a case).
Adding `Cases: goroutines/wake-then-abort` would also be safe and would make
the row discoverable from the entry: for `Pinned-by: none` the checker
verifies **existence only** (the row is in `baselines/native-full.tsv` as
PASS), and it must NOT be accompanied by `- Expect: FAIL`, which would demand
the row be red. It does not move the untriaged ratchet either, since the row
is not in the failure pile. This lane proposes it and leaves the call to the
coordinator; the entry's header lines are unchanged here.

## 6. Exposure

Measured, isolated conditions: **0 events in 73,600 recorded draws**. By the
rule of three the one-sided 95% upper bound on the per-draw probability is

- plain draws only (the gate's draw 61 was plain): 3/45,600 = **6.6 × 10⁻⁵**
- all draws: 3/73,600 = **4.1 × 10⁻⁵**

A K=80 slow run spends 40 plain + 40 `-race` draws on this row, so at the
measured upper bound P(the row reds in a slow run) ≤ 1 − (1 − 6.6×10⁻⁵)⁴⁰ ≈
**2.6 × 10⁻³**, about one slow run in 380.

That bound is for *isolated* draws and is plainly not the gate's regime: the
event did happen once, inside a `GOLEAN_MEM_MAX=48G scripts/capped
scripts/ci --slow` run with the slow-tier enumerator saturating the box. The
shape needs a **second terminal event** in a program that has only one panic
site, i.e. a runtime-internal `throw` — the kind of thing an allocation
failure or a traceback of a goroutine that escaped `freezetheworld` produces
under exactly that pressure. This lane deliberately did **not** manufacture
box-wide memory pressure to chase it: the box is shared with other lanes.

With a single observed event the gate-conditions rate cannot be estimated to
better than an order of magnitude. For planning, P(a K=80 slow run reds on
this row) as a function of the per-plain-draw rate p:

| p (per plain draw) | 6.6×10⁻⁵ (measured bound) | 6×10⁻⁴ | 2.5×10⁻³ | 1×10⁻² |
|---|---|---|---|---|
| P(red in one K=80 run) | 0.26 % | 2.4 % | 9.5 % | 33 % |

The one gate event pins p ≈ 1/(40 × M) where M is the number of prior K=80
slow runs this row survived; the records do not state M, so only the shape of
the estimate is offered, not a number. The gate's own K=32 path draws 16 plain
samples, i.e. ~0.4× the slow run's exposure at the same p.

## Files

| file | bytes | what |
|---|---|---|
| `README.md` | this file | commands, counts, classification, proposal |
| `counts.tsv` | 906 | the bucket table above, machine-readable |
| `row-abort-42-printed.stderr` | 3,708 | one real draw, class 1 (abort with `42` on stdout) — verbatim, with `go run`'s trailer |
| `row-abort-silent.stderr` | 4,427 | one real draw, class 2 (abort, no stdout) — verbatim |
| `probe-two-abort.report` | 9,588 | the PROBE's authenticated two-abort crash-channel copy — verbatim; the forgery control for the follow-up lane |
| `refusal-repro.txt` | — | observer transcript: positive controls + the reproduced refusal |

Nothing is truncated; no stack trace was elided.
