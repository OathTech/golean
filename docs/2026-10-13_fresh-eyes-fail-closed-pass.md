# Fresh-eyes fail-closed pass (2026-10-13)

[AGENT] (Fable, a fresh-context release auditor), read-only on `main` @ `6d08b78b` (clean, gate green), in
the worktree `.claude/worktrees/freshpass-1013` with the built binaries copied from `main`'s `.lake`.
The owner's question ([USER] Mike 2026-10-13, paraphrased): the semantics must be fail-closed wherever
confidence is not high — and, for a first release, check whether anything was missed.

**Method.** I did not trust a record I did not re-verify. I wrote ~370 small Go subjects across 21 probe
batches (arithmetic, strings/runes, maps/closures/loop variables, floats, slices, structs/interfaces/methods,
defer/recover, panic payload rendering, fmt, print, stdlib source-through, channels and sync, generics,
package initialisation, multi-file packages with a local import, control flow and typed shifts, type
assertions and switches, evaluation order, pointers/aliasing/budgets, scheduling shapes), lowered each with
the frontend, ran it with `golean native-json-run`, and compared against the pinned go1.26.5 oracle built
by `tools/coverageharness` (plain `go run`; the scheduling shapes also under `-race`, 150 + 150 draws each at
`GOMAXPROCS=2`). Where the machine's answer differed from a single `go run` I asked whether the program is
nondeterministic and, if so, enumerated the machine's set with `golean coverage-observations` and checked
every gc sample for membership. I also read the fail-open candidates by hand: the decoder's `getD`/`| _ =>`
arms, the core's non-stop default arms, the frontend's judgement language, the fmt desugarer's matrix, the
enumerator's accountant, the stdlib register and the Go observer. Classification used throughout:

- (A) silent wrong answer — status `ok` or an agreed `panic` whose value or text is outside the modeled set;
- (B) an answer in a low-confidence area with no differential evidence behind it;
- (C) a refusal by name (fine);
- (D) a documented limit with a visible red (fine).

Probe programs and both sides' raw outputs sit under the worktree's `.tmp/probes/<batch>/` (ephemeral;
each subject is reproducible from the Go text quoted below with
`.tmp/nativefrontend --dir <d> --out wire.json` + `golean native-json-run --input wire.json --function <f>`
on the left and `tools/coverageharness --input main.go --out o --subject <f> --args - --expected-status ok`
+ `cd o && : > oracle.crash && GODEBUG=panicnil=0 go run .` on the right).

## 1. Ranked findings

**No (A) finding.** Across every batch, not one subject answered `ok` (or an agreed `panic`) with a value,
output or abort text that gc did not realise or that the machine's enumerated set did not contain. Every
miss was a refusal naming its cause, a documented envelope whose set contained gc's sample, or an
apparatus-class stop (`fuel-out`, a tripped cap). The items below are ranked by how much they matter to a
consumer who takes the machine's answer at face value.

### F1 — MEDIUM (design, not a bug): a single run answers `ok` with ONE member of an enveloped set and nothing marks it

`golean native-json-run` on a program with a consulted choice site prints the canonical member with status
`ok` and nothing on stderr; the observation JSON carries no key saying a choice was made. The same run under
`golean choice-trace --stream default` reports `consumed=1 … appendSpill=1 maxBound=32`.

```go
func appendCapBytes() int { var b []byte; b = append(b, 1); return cap(b) }   // gc: 32
```

- `native-json-run`: `{"output":"","schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":4}]}`, exit 0, stderr empty.
- `go run`: `… "value":32`.
- `coverage-observations --max-width 64`: 32 members, `{1 … 32}` — gc's 32 is a member (latitude R2, the
  append-spill envelope `[newLen, 32]` here). Two more shapes checked the same way: `append(nil-[]string, "a","b","c")`
  (machine 4, gc 3, set {3 … 32}) and `append(make([]int,1024), 1)` (machine 1472, gc 1536, set {1025 … 2944}, 1920 members).
- Likewise `mapIterFirst` (machine 10, gc either; set {10, 20}), `mapInsertDuringRange` (set {2, 3}; gc 13/100 → 2,
  87/100 → 3), `selectBothReady` (set {1, 2}).

This is exactly the doctrine («observed ∈ modeled»; `docs/cli.md` §5–§6.1 document it; the corpus puts such
rows in the membership lane), so it is (D) for the apparatus. But for a CLI consumer it is a silent answer in
precisely the area where confidence is a set, not a point: the `ok` observation is indistinguishable from a
deterministic one. Fix shape (cheap, additive): have `native-json-run` emit on stderr, or as an additive
observation key, the consumption count the driver already has (`consumed`, per-site menu as `choice-trace`
prints it) whenever it is non-zero — so «one member of N» is never silent. Rows exercising enveloped sites:
`membership` lane 273 rows, `confluent` 103, `racy` 45 (of 3976).

### F2 — LOW: a decode-time budget refusal takes the whole wire, not the declaration

```go
func bigArrayLit() int { a := [70000]int{1: 5}; return a[1] }
```

The decoder refuses the entire program: `native lowering: array type of 70000 elements exceeds the
interpreter's materialization budget (65536 elements; BUG-078 idealization boundary) at
program.funcs[13].body.body[0].lhs[0].type` — and every other subject in the package then answers
`status:error` (27 unrelated green subjects went red in my batch until I deleted that one function). The
frontend quarantines an unlowerable declaration per declaration (`docs/cli.md` §6.3) and leaves the rest of
the package testable; the decoder's `arrayLenBudget` / `arrayFootprintBudget` / `checkMakeFootprint`
refusals (`GoLean/NativeToIR.lean`) do not. Fail-closed and named, so (C), but the blast radius hides every
other function from the differential. Fix shape: apply the same budgets in the frontend's per-declaration
quarantine (the type is static), keeping the decoder's check as the backstop. Corpus rows on these budgets:
`arrays/materialization-budget-*` (born at train 7), 1 wire each — none exercises a multi-function package.

### F3 — LOW (apparatus scope): the enumerator's defaults do not reach two-goroutine programs

Every goroutine shape I enumerated tripped the default `--max-sites 8` («run consumes more than --max-sites
8 choice site(s) — raise the case's sites bound (never truncated silently)»), and three of sixteen shapes —
a two-goroutine mutex-protected counter, a mutex hand-off order, two goroutines on one `sync.Once` — exceeded
`--work-cap 4000000` after ≈2.97 M steps + 1.03 M probes with subtrees unexplored; the other thirteen
certified sets contained every one of 150 plain and 150 `-race` draws each. Both stops are loud (good). Scope note for the release text: the membership lane's practical
reach on the DFS engine is small concurrent programs; the dedup engine (verified certificate) is the route
for larger graphs. 238 rows carry `goroutines`, 70 `select`, 217 `sync`.

### F4 — LOW (apparatus, documented): the strict lane cannot compare pointer, slice, map or channel results

The Go observer (`tools/coverageharness/main.go`, `_goleanReflectValue`) has no `reflect.Pointer`,
`Slice`, `Map` or `Chan` arm outside seeded mode (`seedPointerArm` is injected only with `--seed`), so a
subject returning one is refused on the Go side and the row is red. The machine renders them as raw
allocation ids. This is stated limit 5 of the 2026-10-03 offer; it should be stated once more in the release's
limits as «what a strict row can compare».

### F5 — note: the harness's own post-subject work widens the C4 window, and the runner handles it

```go
func childPanicVsReturn() int { go func() { panic("c") }(); return 1 }
```

Machine set {ok 1, panic c}. gc plain, 150 draws: 75 abort before the observation, 16 clean `ok 1`, and 59
runs that printed the `ok 1` observation on stdout and THEN aborted with the child's panic (exit 2). The
hybrid is the harness printing JSON after the subject returned. `crashview.go:205` refuses an `ok` run whose
crash report is non-empty, and the sampler routes a non-zero exit through the panic branch, so the hybrid is
either the `panic` member or an undecided red — never a silent pass. Recorded here because a future harness
change could reopen it.

## 2. What held (re-verified, not read)

Every row is one subject; «SAME» means value, kind, output bytes and (for aborts) gc's first line all agree.

| batch | subjects | SAME | refused by name (C) | enveloped, gc ∈ set (D) | apparatus stop |
|---|---|---|---|---|---|
| arithmetic (tdiv/tmod, MinInt/-1, shifts ≥ width, negative shift, wrap, narrowing) | 23 | 23 | 0 | 0 | 0 |
| strings/runes (invalid UTF-8 range, `string(rune(-1))`, surrogates, bounds texts) | 22 | 22 | 0 | 0 | 0 |
| maps/closures/loop vars (NaN keys, ±0, unhashable panic, delete/insert in range, Go 1.22 per-iteration) | 24 | 22 | 0 | 2 | 0 |
| floats (f32 via f64, ±0, NaN compares, denormals, fma shape, float→int) | 30 | 26 | 4 (R6: out-of-range/NaN/`int8(300.0)`/`uint64(-1.0)`) | 0 | 0 |
| slices (aliasing, 3-index, overlap copy, bounds texts, make limits) | 33 | 29 | 1 (slice→array, FR-10) | 3 (R2 cap) | 0 |
| structs/interfaces/methods (nil-in-interface, uncomparable panics, promotion, method values) | 30 | 29 | 1 (anonymous struct, FR-13) | 0 | 0 |
| defer/recover/panic texts (`[recovered]`, nested panics, runtime-error payloads) | 24 | 17 | 7 (BUG-099 payload class ×3; address-printing payloads ×3; `panic(nil)` recover) | 0 | 0 |
| panic payload rendering (Stringer, named int/float, rune/byte, pointer, Error() that panics) | 19 | 15 | 3 (float/named-float/pointer payloads) | 0 | 1 (my runner lacked `GODEBUG=panicnil=0`; the apparatus sets it) |
| fmt (`%d` widths, `%x`, `%q` ≥ 0x80, `%v` composites, Stringer precedence, panicking String) | 40 | 23 | 17 | 0 | 0 |
| print/println (format pins, high bytes, defer of println) | 20 | 16 | 3 | 1 (invalid-UTF-8 output refused at the comparator) | 0 |
| stdlib source-through (strconv edges, strings, slices incl. pdqsort ties, errors) | 51 | 48 | 3 (`IndexRune` goto shape FR-20 ×2, `errors.Is`) | 0 | 0 |
| channels/sync/goroutines (close/send texts, deadlock, misuse fatals, leaks at exit) | 27 | 26 | 0 | 1 | 0 |
| scheduling membership (select/default poll, `len(map)` under a peer, unbuffered order, atomic spin, four print-interleaving shapes, `len`/`cap` beside a peer send, RWMutex read beside a write, two-sender select, child abort vs return) | 16 | — | — | 13 (every one of 150 plain + 150 `-race` gc draws ∈ set) | 3 (`mutexCounter`, `mutexHandoffOrder`, `onceTwoGoroutines`: DFS work cap at ≈3 M steps, loud) |
| generics (constraint arithmetic, instantiation identity, zero values, generic methods) | 29 | 29 | 0 | 0 | 0 |
| package init (file order a.go/b.go/main.go, dependency order, closures, methods in initialisers) | 9 | 8 | 1 (anonymous struct global, FR-24) | 0 | 0 |
| multi-file + local import (cross-package init, methods, identity, assertion) | 7 | 7 | 0 | 0 | 0 |
| control flow (typed shifts `var x int8 = 1 << n`, labels, goto, fallthrough, `range int`, recursion depth) | 41 | 38 | 0 | 0 | 3 (`fuel-out`: 500 k-deep recursion, infinite recursion, 2·10⁷ loop) |
| type assertions/switches (texts, nil, named, byte/rune, func/map/chan cases) | 28 | 28 | 0 | 0 | 0 |
| evaluation order (call-first, index-then-assign, literals, short-circuit, defer args) | 23 | 23 | 0 | 0 | 0 |
| pointers/aliasing/budgets (element pointer across realloc, method value on addressable receiver, zero-size address, `[]byte(s)` ×2) | 28 | 27 | 1 (`make([]int, 1<<40)`: machine budget; gc OOM) | 0 | 0 |

Specific things I expected to be wrong and were not: `Int.tdiv`/`Int.tmod` (not Euclidean) for `/` and
`%`; `MinInt64 / -1` wraps with no panic; shift counts ≥ width saturate with sign fill; float32 arithmetic
rounds through float64 (innocuous at 53 ≥ 2·24+2, and what gc's own softfloat does); `string(rune(x))` for
negative, surrogate and > 0x10FFFF gives U+FFFD; the Go 1.22 per-iteration loop variable holds under closures,
address-taking and post-statement mutation; `recover()` only in the directly deferred call; `panic: first
[recovered]` first-line collapse; map NaN keys count twice, ±0 once; `copy` overlap both directions; the
three-index slice stops aliasing; pdqsort tie order matches gc byte for byte; `strconv` error texts match.

Hand-read fail-open candidates that turned out benign: `NativeToIR.lean:564` (`tyFootprint?` counts 1 for
non-arrays — a count, not a size), `:734/:737` (metadata defaults), `:1681` (a locals pre-pass; the main
decoder refuses an unknown range kind at `:2727`); `Machine.lean:540` (interface boxing by design),
`:1527` (decimal int rendering); `emit.go:1405` (unknown type ⇒ assume the panicking case — sound
direction); `staticinit.go:601` (direction argued per shape, 125-row gc verdict table).

## 3. What I could not reach

- The three scheduling shapes that exceeded the DFS work cap (two goroutines each contending one mutex or
  one `Once` beside a `WaitGroup`): their sets are unknown to me; gc's draws were all the single expected value.
- The dedup engine as a cross-check of the DFS sets; the `choice-trace --batch` path; seeded-heap mode.
- The race detector's precision beyond the recorded BUG-041 / BUG-111 classes; racy programs are refused by
  doctrine and I did not try to slip one past the detector.
- The `unseq` evaluation-order envelope on the three legacy `cases` arms (E3/E4 are recorded as known ≠ gc).
- The negative corpus and the frontend's rejection classes; the raft subject; any program over a few hundred
  machine steps per branch (the fuel and work caps bound what a probe can see).
- Packages outside the register (`time`, `os`, `io`, `bufio`, `math` beyond `Float*bits`, `sort`): they are
  quarantined by name and I did not probe the quarantine texts.
- A 32-bit or non-gc platform instance (none exists; stated).
- Statistical blind spots of the membership lane: K = 32 draws cannot see a 1-in-200 gc behaviour (I saw
  `selectDefaultPoll` take the send 1/150 plain, 4/150 under `-race`); this is a known limit of sampling, not a
  model defect.

## 4. Verdict

On everything I could probe, the semantics is fail-closed where its confidence is low: the implementation-
dependent corners (float→int out of range, NaN bit observation, address-printing payloads, fmt verbs outside
the pinned matrix, `print` of floats, `uintptr` observation, runtime-error payload types, unsafe, anonymous
structs, goto shapes, decoder budgets) all refuse naming their cause; the latitude points it does answer
(append capacity, map order, select choice, scheduling) answer with one member of a set that contained every
gc sample I drew; and the apparatus stops are loud. I found no silent wrong answer in ~370 fresh subjects,
and the hand-read default arms substitute nothing. Before a first release I would do three cheap things:
(1) make `native-json-run` say when a choice site was consulted (F1), so a single-run `ok` on a
nondeterministic program is never mistaken for a point answer by a consumer who never reads `docs/cli.md`
§6.1; (2) move the decoder's array/make budgets into the frontend's per-declaration quarantine so one
over-budget literal does not red out a whole package (F2); (3) state in the release's limits the strict
lane's comparable surface (F4) and the enumerator's practical reach on concurrent programs (F3). None of
these is a semantics change; the semantics itself I would ship as it stands.
