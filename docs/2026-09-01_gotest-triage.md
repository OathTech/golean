# $GOROOT/test triage — the first outside-authored differential run

Date: 2026-09-01 · Lane: t4-gotest (assessment) · [AGENT]-executed under
[USER]-approved fidelity decision 4 ("the single best external-validity
purchase" — the synthesis's phrase, `docs/assessment/synthesis.md` §4,
approved-as-recommended by decision 4; outsider review demand D2,
`docs/assessment/lane-e-outsider-review.md`
— the test262-analogue step).

**Assessment-run boundaries**: the tracked products of this lane are this
report and the runner `scripts/gotest-triage` (lane tooling, NOT a gate).
NO baseline changes, NO corpus changes, NO gate changes were made. Every
mismatch below is a RECOMMENDATION for promotion, not a promotion.

## Why this run matters

The fixture corpus is a closed loop: the same effort authored the
semantics and its test cases. `deps/go/test` (the classic run.go/testdir
suite, pinned at the go1.26.5 checkout) is ~2,700 programs authored by
the Go project over ~15 years, each a regression test for a real
compiler/runtime bug — an adversarial corpus nobody here wrote. Its
`// run` tests are predominantly SELF-CHECKING: silent on success, panic
on any wrong value, so a status-level differential exercises every
internal assertion of each test.

Verdict up front: **of 335 comparable tests, 331 agree and 4 disagree —
and all 4 disagreements are genuine model bugs** (three distinct
spec-evaluation-order/special-case defects, each reproduced shim-free
with a minimal probe, none previously in BUGS.md). The closed-loop
concern was warranted, the purchase paid.

## Method

Runner: `scripts/gotest-triage` (see its header for the full contract).
One run = survey + drive + classify, all under `artifacts/gotest/`
(gitignored).

- **Survey**: enumerate the testdir driver's own directory list (14
  dirs), extract each file's execution directive by the driver's own
  rule (first non-empty, non-build-constraint comment line).
- **In-scope slice**: plain `// run` (no flags/args), single file. The
  frontend itself is the in/out-of-fragment classifier — a refusal IS
  the verdict (fail-closed doctrine).
- **Entry-point shim**: the native frontend deliberately skips
  `func main` in the main package (GoCore runs a named subject), so the
  scratch copy renames `func main` → `func gotestMain` and appends
  `func main() { gotestMain() }`. The transformation is SYMMETRIC —
  both pipelines consume the identical transformed source — so it
  cannot skew one side. Unrenameable shapes (main inside a generated
  string literal, meta-tests) fail closed as INFRA.
- **Oracle**: `go run` on the pinned go1.26.5 (pin checked, refusal on
  drift — `scripts/diff-coverage`'s rule), `GO111MODULE=off
  GODEBUG=panicnil=0`, with the testdir `.out`-file expectation
  enforced: an output deviation on the pinned toolchain is INFRA, never
  a machine verdict.
- **Machine**: `go run ./tools/nativefrontend` → `golean native-json-run
  --function gotestMain` (fuel 10^7 default, 30 s wall cap per side).
- **Comparison**: observation equality via the repo's own
  `golean observation-eq` on canonical observations (ok/panic/deadlock/
  fatal shapes synthesized exactly as `scripts/diff-coverage` does).

**Honest scope — the comparable surface.** The machine has NO stdout
observable; `main` returns nothing. The differential surface here is
termination status + panic/deadlock/fatal message. Tests that print on
success would be flagged `output-uncompared` and counted separately —
in this run that count is ZERO — a MEASURED result, not a theorem:
the in-scope printing tests happen to reach stdout via
print/println/fmt, which the frontend refuses, but nothing guarantees
every conceivable printing route is refused — the zero is what the
run counted (loosened at the audit fix round, G4). So every MATCH
below is a full-strength one (silent-success self-checking program
agreed on both sides).

**Scope of the run**: the FULL in-scope slice — all 1,013 cases, no
sampling, no truncation. Wall time 86 s at 8 workers (plus a one-time
`scripts/capped lake build golean`). Meta: commit 670d3351, go1.26.5,
2026-09-01T05:48:33Z.

## The counts

### Survey (2,663 test files in the driver's 14 directories)

| directive | files | notes |
|---|---|---|
| run | 1,039 | 1,013 plain = the in-scope slice; 26 carry flags/args (gcflags/-race/goexperiment/program args) — out of scope |
| errorcheck (+withauto/output) | 675 | compile-error golden tests — a FUTURE lane (frontend-refusal vs gc-diagnostic comparison), not runnable |
| compile / compiledir / build / builddir / buildrun(dir) | 679 | compile-only |
| rundir / runindir | 127 | multi-file/package run tests — out of scope for the single-file harness (candidate extension; the harness's multi-package plumbing exists in the corpus runner) |
| asmcheck | 81 | gc codegen assertions — permanently out of scope |
| runoutput | 22 | generate-then-run — out of scope |
| errorcheckandrundir / errorcheckdir | 30 | multi-file errorcheck |
| skip | 9 | skipped by the suite itself |
| (stray) | 1 | `linkmain.go` — companion file of a meta-test, no directive |

### The in-scope run (1,013 cases, full slice)

| category | count | share |
|---|---|---|
| FRONTEND-REFUSED | 641 | 63.3% |
| MATCH | 331 | 32.7% |
| MACHINE-REFUSED | 15 | 1.5% |
| INFRA | 22 | 2.2% |
| **MISMATCH** | **4** | **0.4%** |

Comparable (MATCH+MISMATCH): **335 of 1,013 (33%)**; agreement on the
comparable slice **331/335 (98.8%)**; status-only (output-uncompared)
matches: **0**.

### FRONTEND-REFUSED by cause (the fragment census)

| cause bucket | count |
|---|---|
| builtin `println` in statement position | 159 |
| builtin `print` in statement position | 28 |
| fmt.* outside the modeled subset (Printf/Println as statements, unmodeled verbs) | 82 |
| runtime.* calls (GC, GOMAXPROCS, SetFinalizer, Caller(s)…) | 55 |
| other stdlib package calls (time, sort, sync/atomic, math, …) | 51 |
| unsafe.* (Pointer, Sizeof, Offsetof — deliberately unmodeled: implementation-specific layout) | 46 |
| anonymous non-empty struct types | 35 |
| reflect.* | 25 |
| os.* (Exit, Args, Getenv) | 19 |
| imported generic instantiation (iter.Seq[…] etc.) | 17 |
| complex numbers | 14 |
| everything else (build-constraint tags, function-local type collisions, map-element multi-assign targets, quarantine cascades, …) | 110 |

The single biggest fragment lever is plain `print`/`println` in
statement position: 187 direct refusals plus a large share of the
quarantine cascades and fmt rows — the classic suite's standard
failure-reporting idiom is `println(...)` inside an `if fail` branch,
and per-decl quarantine refuses the whole helper even when the failing
branch is dead. Modeling statement-position println (even as an
effect-discarded evaluation for the no-.out case) would plausibly move
200-350 tests from refused to comparable at one stroke. Second lever:
anonymous struct types (35). These are recommendations for fragment
widening priorities, not obligations.

### MACHINE-REFUSED (15)

- 8 wall-clock timeouts at 30 s (atomicload, turing, gc1, issue7550,
  issue13169, issue16249, issue29190, issue67255) — heavy-loop programs
  at interpreter speed; turing and issue7550 were probed at 120 s and
  still time out. Honest budget refusals, not verdicts.
- `convert4.go`: slice-to-array-pointer conversion (recorded L2b
  frontier refusal).
- `bug341.go`: float-to-int out-of-range/NaN — the machine's DELIBERATE
  latitude refusal (implementation-dependent in Go); correct posture.
- `bug206.go`, `issue71857.go`: default value for imported named types
  (go/token.Pos, sync/atomic.Uint64) — fragment edges.
- **Suspicious-refusal flag**: `issue19911.go`, `issue53619.go`,
  `typeparam/issue42758.go` refuse with "nil literal for non-nilable
  type …interface…". The shape is the CONVERSION form `any(nil)` /
  `error(nil)` — nil-to-interface conversion is legal Go, so this is a
  modeling gap in the conversion path (fail-closed, so no fidelity lie,
  but an easy fragment win and worth a look: the assignment form
  lowers, the conversion form refuses).
  *[Superseded 2026-09-01, fix slice + audit fix round: the conversion
  arm is BUG-077 (fixed). Only issue42758 MATCHes on it; issue19911
  progresses to a strings.Index frontier refusal (FR-14); issue53619
  carries a SECOND defect this triage did not see — its comma-ok
  assertion into INTERFACE-typed globals lowered an unboxed bool and
  refused downstream at interface equality — now BUG-079, refused at
  the lowering by name. The "one modeling gap" classification of the
  three was wrong.]*

### INFRA (22)

- 9 entry-point shim refusals: main inside generated string literals /
  meta-tests (compile-and-exec-a-child tests) — correctly not
  comparable.
- 8 go-run failures: meta-tests driving `go tool` themselves, wasm/js
  build-constraint tests.
- 4 pinned-toolchain output deviations: tests asserting runtime.Caller
  frames or link modes; one (`issue21879.go`) deviates BECAUSE the shim
  renames main — the fail-closed .out comparison caught the shim's one
  observable side effect, as designed.
- 1 **golean robustness note**: `issue34395.go` (a very deep recursion
  program) crashes `golean` with a native STACK OVERFLOW (exit 134,
  "Stack overflow detected. Aborting.") rather than a named refusal.
  *[Corrected by BUG-078 (2026-09-01): issue34395 is NOT a deep-
  recursion program — it is a `[100<<20]byte` global with a two-line
  main; the overflowing recursion was the machine's element-wise
  normalize over the array, and the case now refuses by name at the
  wire decoder's array-type budget.]*
  Fail-noisy, not fail-silent, but a process abort is not a
  cause-naming refusal — recorded here as a standing robustness
  follow-up for the interpreter driver.

## The four mismatches — diagnosis

All four were re-derived with minimal probes that bypass the shim
entirely (named subject functions, no renamed main), under
`artifacts/gotest/probe/`; gc verdicts confirmed per-shape. All four
are OUR BUGS — none is a gc-version artifact, none is an unmodeled
observable, none is latitude (each violates a spec-pinned order or
special case).

### M1 — select entry-time evaluation is not snapshotted (2 tests, 1 root cause)

`fixedbugs/issue4313.go` (go ok, machine panics `42`) and
`fixedbugs/issue43111.go` (go ok, machine deadlocks).

Spec (§Select statements, step 1): on entry, ALL channel operands of
receive clauses and BOTH the channel and right-hand-side expressions of
send clauses are evaluated exactly once, in source order. The lowering
(`emitSelect`, tools/nativefrontend/emit.go) hoists only EFFECTFUL
subexpressions to statement level; effect-free operands (a plain ident
`x`, a global channel var `ch`) are left in the clause and read at
COMMIT time — after a later clause's hoisted call has mutated them.

- issue4313: `select { case c <- x: … case <-makec(&x): … }` — makec's
  hoist sets x=42 before the send value is read; machine sends 42 where
  gc sends the entry-time 0. Probe: `probeSel` returns 42 (gc: 0).
- issue43111: `select { case <-ch: case nilch <- f(): }` where f closes
  ch and sets `ch = nil` — the machine re-reads the now-nil `ch` at
  commit and deadlocks; gc receives from the entry-time (closed)
  channel. Probe reproduces the deadlock.

Fix shape: snapshot every clause's channel operand and send RHS into
entry-time temps (in source order), effect-free or not.

**Recommendation: fidelity-bug candidate — BUGS.md entry + two corpus
rows** (entry-order send-value shape; entry-order channel-operand shape,
which also pins the deadlock-vs-ok observable).

### M2 — multi-value `return` stores results before a later operand's panic

`fixedbugs/issue43835.go` (go ok, machine panics `FAIL`).

Spec: return-statement operands are evaluated like an assignment to the
result variables — all RHS evaluated (left-to-right, panic included)
BEFORE any result is stored. Probes (f/g/h shapes from the test):
machine `probeF`=false (correct — the two-phase ASSIGN path is right),
`probeG`=true, `probeH`=true (gc: false/false/false). So the
multi-value `return e1, e2` path stores result 1 before evaluating e2;
when e2 panics and a deferred recover() catches it, the partial store
is observable through named/blank results. The site is
`GoLean/NativeToIR.lean:1171-1183` — `decodeReturn` lowers
`return e1, .., en` as SEQUENTIAL per-result assigns
(`assign r1 := e1; assign r2 := e2; ...; return`), so each result
stores as its operand evaluates instead of after ALL operands have
evaluated. That is the wire decoder — TRUSTED-SURFACE, not the
frontend (the frontend emits the return node faithfully).

**Recommendation: fidelity-bug candidate — BUGS.md entry + one corpus
row** (return-with-panic-in-second-operand, recover-observed).

### M3 — `for range *p` (nil pointer-to-array, effect-free) wrongly evaluates the indirection

`fixedbugs/issue72844.go` (go ok, machine panics nil-dereference).

Spec (§For statements w/ range clause + §Length and capacity): for an
array or pointer-to-array range expression with no iteration variables,
only the (constant) length is used and the expression is not evaluated
unless it contains calls/receives. Probes: `len(*nilPtrVar)` is RIGHT
(4, no panic — the len special case is implemented) but
`for range *nilPtrVar {}` PANICS (gc: 4 silent iterations). The other
seven shapes in the test agree with gc, including the ones that must
panic. The range lowering is missing exactly the non-evaluation special
case that len already has.

**Recommendation: fidelity-bug candidate — BUGS.md entry + one corpus
row** (range over nil `*[N]int`, no iteration variables).

## Standing-lane recommendation

**Adopt as a periodic leg — nightly-class, not per-commit.** [AGENT]
recommendation, sized as follows:

- Cost, measured: 86 s wall at 8 workers for the full 1,013-case slice
  (plus the golean build the gate already pays). Deterministic modulo
  the 8 timeout rows.
- Per-commit gating would need a tracked expected-category baseline
  (1,013 rows) and would churn on every fragment widening — that is
  baseline-maintenance cost without per-commit value, since the corpus
  differential already gates runtime changes.
- As a nightly/pre-merge-audit leg its value is exactly what this run
  showed: it catches spec corners the authored corpus is structurally
  blind to. The natural trigger points: after any frontend fragment
  widening (each print/println/fmt widening unlocks 100-350 more
  tests → re-run and re-triage), after any evaluation-order/lowering
  change, and on oracle re-pins (a new $GOROOT snapshot brings new
  tests).
- If adopted, track a small expected-MISMATCH allowlist (the M1-M3 rows
  until fixed) so a NEW mismatch is loud — the fail-closed shape the
  other legs already use. Promotion of the runner to a gate leg is a
  gate change and stays the user's call.

Extensions worth their cost, in order: (1) statement-position
print/println modeling (fragment lever #1, unlocks the biggest slice);
(2) the `rundir`/`runindir` 127 multi-file tests (the corpus runner's
multi-package plumbing already exists); (3) an errorcheck lane
comparing frontend refusals against gc diagnostics on the 675
errorcheck tests (a frontend-precision census, no machine involvement).

## Artifacts and reproduction

- Runner: `scripts/gotest-triage` (header = contract). Full run:
  `scripts/capped lake build golean && scripts/gotest-triage run`.
- This run's raw rows: `artifacts/gotest/results.tsv` (+ `.meta.tsv`,
  `survey.tsv`) at commit 670d3351 — gitignored artifacts; the numbers
  above are the tracked record.
- Probes (shim-free reproductions): `artifacts/gotest/probe/{p4313,
  p43111,p43835,p72844}/main.go` — gitignored scratch; their exact
  shapes are stated in the diagnosis sections above, and the upstream
  test files in `deps/go/test/fixedbugs/` are the permanent
  reproducers (pinned by the go checkout rev).
