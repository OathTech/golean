# Coverage Suite Structure

This document describes the target structure for a large Go differential
coverage suite. The goal is to make adding tests cheap, make failures explicit,
and avoid a central manifest becoming a second source of truth.

## Goals

- Every executable test uses ordinary canonical Go source.
- The Go and Lean paths consume the same source file.
- Expected Go runtime behavior is classified per case as `ok` or `panic`.
  Lean `unsupported`, `stuck`, and `error` observations are failures, not
  expected conformance outcomes.
- Static invalid-Go cases live in a separate negative lane.
- Test ids, source paths, and artifact paths are derived mechanically.
- Subsets are runnable by id, directory prefix, feature tag, expected status,
  or last failure stage.
- Reports summarize both individual red/green cases and feature coverage.
- Gaps are exposed, not hidden. Unsupported features, frontend failures,
  semantic stuckness, and differential mismatches stay red in the default
  report. Known-gap annotations may categorize work, but they must not make the
  main conformance lane green.
- Every detected coverage gap on legal Go is ROWED at detection: a born-FAIL
  case whose red is a fail-closed refusal (not a wrong answer) gets a frontier
  row in `docs/language-coverage-ledger.md` §4 WITH a fix plan and a §5 queue
  slot in the same change — never left as an unrowed red in the post-vintage
  bucket ([USER] direction 3, 2026-09-03, recorded in the ledger §0; relayed
  by the coordinator, not firsthand).

## Directory Layout

Current executable layout:

```text
Corpus/coverage/
  tags.tsv
  exec/
    <area>/
      <case>/
        main.go
        cases.tsv
  negative/
    compile/
      <area>/
        <case>/
          main.go
          case.tsv
  suites/
    smoke.lst
    frontend.lst
    semantics.lst
  README.md
```

Deeper grouping such as `exec/<area>/<feature>/<case>` is allowed when it makes
the suite easier to browse. The id is always derived from the relative path
under `exec`.

## Naming

Use stable, lowercase kebab-case path components. The executable case id is
derived from the path under `exec` plus the row id from `cases.tsv`.

For a one-case package:

```text
Corpus/coverage/exec/slices/append/overlap/
  main.go
  cases.tsv
```

The full id is:

```text
slices/append/overlap
```

For grouped litmus packages, add a short row id:

```text
Corpus/coverage/exec/strings/bytes/indexing/
  main.go
  cases.tsv
```

with rows `ascii`, `utf8-leading-byte`, and `utf8-continuation-byte`, giving:

```text
strings/bytes/indexing/ascii
strings/bytes/indexing/utf8-leading-byte
strings/bytes/indexing/utf8-continuation-byte
```

Prefer one case per package unless grouping removes real boilerplate while
remaining easy to inspect.

## Case Metadata

Each executable package has a `cases.tsv` file. The runner validates exact
column count, valid statuses, known feature tags, subject presence in `main.go`,
path and row id syntax, duplicate ids, subject syntax, integer args, and
expected reason policy.

Columns:

```text
id<TAB>subject<TAB>args<TAB>expected_status<TAB>expected_reason<TAB>features
```

Optional lane columns (membership lane, arc slice 3,
`docs/2026-08-04_membership-lane-design.md`) may follow `features`:

```text
...<TAB>lane<TAB>why<TAB>params
```

- `lane` is `strict` (the default when the columns are absent or `-`),
  `membership`, `confluent`, or `racy` (the last two: channels arc slice 4,
  `docs/2026-08-04_nondeterminism-doctrine.md` "Per-lane epistemic
  captions"). Membership cases are oracled by SET MEMBERSHIP — every
  `go run` sample must lie in the machine-enumerated observation set
  (`golean coverage-observations`) — instead of equality against one run.
- `why` is mandatory free text for `membership` (which observable depends
  on which consumption site); it must be `-` for `strict`.
- `params` is comma-separated `key=value` settings: `width` (enumerator
  pick alphabet `[0,B)`; REQUIRED for membership rows, no silent default —
  author-asserted to cover every consumption-site bound in the case, with
  the bound argued in `why`; the enumerator's alias-guard ladder is a
  heuristic cross-check of the assertion, not a proof), `sites` (max
  consumption depth, default 8), `cap` (max distinct observations,
  default 64), `work` (enumerator work cap, default 200000), `members`
  (the certified set's exact cardinality — a mechanical pin; also the
  sampling rule's early-stop target, below). Under `engine=dedup` (the
  verified whole-graph certificate) only `work=`, `members=` and
  `statuses=` are read: `width=`, `sites=`, `cap=` and `backedge=` are
  REFUSED there as inert — by the manifest, by the harness, and at the CLI
  (`--max-width`/`--max-sites`/`--cap`/`--fuel`/`--backedge` with
  `--engine dedup` exit 2 by name; release-readiness item 27, 2026-10-12)
  — and `width=` is not required. `samples=` is RETIRED
  (2026-09-03): both `scripts/coverage-manifest` and the harness refuse
  it by name — the Go-side draw budget is no longer a per-row count.
- **Membership sampling rule** ([USER]-ruled gate change, Mike
  2026-09-03, relayed by the coordinator: "yeah, agree on the sampling
  budget, go ahead as you propose" — adopting
  `docs/2026-09-01_membership-depth.md` §4.3 / P2; implemented in
  `scripts/diff-coverage` `run_membership_case_rows`, budget constant
  `MEMBERSHIP_DRAWS`). Per membership row the oracle draws ALTERNATE
  plain and `-race` (`plain, race, plain, race, …` — the `-race` runtime
  is the only scheduling perturbation on the scheduling rows, so it comes
  second, not sixth as under the old "5 plain then 5 race" order); the
  row STOPS EARLY once the distinct observations drawn reach its
  `members=` pin — but never before TWO draws (one plain, one `-race`)
  have been taken ([USER] ruling 2026-09-03, relayed: «(d) this is a 'spirit of the ruling' vs. 'letter of the ruling' case - we should do option A which seems like the spirit of the ruling» —
  option A, the two-draw floor; such rows caption `draws=2 (floor; …)`),
  otherwise at the budget **K=32** (not a knob; the former `--slow`
  mode's K=80 went with the cached tier in the 2026-10-12 gate cull),
  printed in the run header and recorded as
  `membership_draws` in `latest.meta.tsv`. Rows WITHOUT a `members=` pin
  have no early stop and draw the full K (the run log names the row as
  unpinned). The PASS detail reports the budget spent beside the
  exhibition count: `exhibited=E draws=D (K=32; stopped at the
  members=N pin | pin members=N NOT reached — d distinct drawn | no
  members= pin — no early stop) unexhibited=U`. The rule never decides a
  row's RESULT: membership PASS/FAIL is "every draw ∈ the enumerated
  set" (plus the enumeration/cardinality/coupling guards) and NEVER the
  exhibition or draw count; the baseline stores result/id/stage and a
  FAIL row's cause key, never a PASS caption, so the changed caption is
  not drift. Fail-closed as before: a draw that
  times out or is killed is NOT an observation — the row fails at
  `membership` naming the cause and the draw index (`draw i/K (mode) …
  did not decide`), never counting toward saturation; an undecided
  distinctness comparison (comparator timeout/kill/exit 2) fails the row
  with "saturation NOT decided"; a draw outside the set is the too-narrow
  soundness alarm exactly as before, checked on EVERY draw. Fixtures:
  `scripts/test-lane-validation --with-go` S1-S4 (red-first record and
  the before/after exhibition table:
  `docs/evidence/2026-09-03_sampling-budget/`). The cached `tier=slow`
  certification and merge-protocol step 5a were retired in the
  2026-10-12 gate cull: every enumerating row runs fresh on every
  `--diff` (`docs/2026-10-12_gate-cull-plan.md` §3.1).
- Fail-closed both ways: `lane=membership` requires the `nondet` feature
  tag and a `why`; a `nondet`-tagged case requires `lane=membership`; a
  membership case whose enumerated set is a singleton fails ("belongs in
  the strict lane"); a strict case that varies across the adversarial
  choice streams keeps failing at stage `nondet`.

Rules:

- `id` is `-` for a one-case package, otherwise a kebab-case suffix.
- `subject` is the source-level Go function Lean should run.
- `args` is `-` or comma-separated integer arguments. On a **seeded** row (a
  strict row with `seed=<file>` in `params`, below) the tokens may also be
  `ref:k(.f|[i])*` (a pointer to seed cell `k` or a component of it: `ref:0`,
  `ref:0.next`, `ref:1[2]`, `ref:0.a[3].b`) and `nil` (a nil pointer), in
  parameter order — `native-json-run`'s `--arg-ref`/`--arg-nil`. A `ref:`/`nil`
  token without `seed=` refuses the row by name.
- `expected_status` is one of `ok` or `panic`.
- `expected_reason` is `-` for `ok`; it is required for `panic`.
- Frontend export failures, Lean `unsupported`, Lean `stuck`, Lean `error`, and
  differential mismatches are reported as red cases. They are not encoded as
  expected statuses in executable metadata.
- `features` is a comma-separated list of canonical feature tags.
- `ok` subjects must return at least one observable value. Use a checksum or
  deterministic summary for mutation-heavy tests. (A seeded row may return
  nothing: its `seed` key — the cells' final values — is observable.)

Derived fields:

- `go_dir` is the directory containing `cases.tsv`.
- Frontend artifact paths are adapter-owned. For the current Gobra adapter this
  is `artifacts/coverage/work/<full-id>/main.go.internal.json`, but the
  normalized manifest does not store that path.
- Result logs are under `artifacts/coverage/results/<full-id>/`.

This removes manifest duplication where ids, source directories, and
frontend-specific artifact paths can drift independently.

### Lane assignment: the strict-lane depth guard (memo P1, [USER]-ruled 2026-09-03)

Origin: the membership-depth lane's routing-rule proposal
(`docs/2026-09-01_membership-depth.md` §5, P1 in §6). Ruling: [USER]
(Mike, 2026-09-03) «(6) strict-lane, agree» to the coordinator's item
"Strict-lane routing rule: adopting it turns eight scheduling rows red
until routed. Recommendation: adopt, and route them in the same slice
so nothing sits red" — relayed by the [AGENT] coordinator, cited here
as relayed, not firsthand; the coordinator then corrected the scope
to "implement P1 as written in §5". Implemented on lane
`strict-routing` (`docs/evidence/2026-09-03_strict-routing/`).

**The rule (as the record proposed it; mechanized in
`scripts/diff-coverage`).** A strict PASS is a two-part claim — Go
equality on the default trajectory AND invariance across three
adversarial choice streams — and the second part is only made when
the streams cover every bound-≥-2 consumption (`Choices.consume`
yields slot 0 once a stream is exhausted, so a row that outruns its
stream is compared with its own default trajectory):

1. After the invariance re-runs, one `golean choice-trace` call
   replays the default stream and the three streams that ran, in
   lockstep with the consumption accountant, and reports per stream
   `wideAfterExhaustion` — bound-≥-2 consumptions served AFTER the
   stream ran out — plus the default-stream wide count `w` (recorded
   in the PASS detail as `wide=`, for sizing only; a `w ≤ 8` threshold
   is NOT the rule — it both leaks and over-refuses, memo §5).
2. `wideAfterExhaustion = 0` on every invariance stream ⇒ the check
   stands; the row PASSes with `wide=<w> exhausted=none depth=fixed`.
3. Otherwise the strict PASS is REFUSED at stage `nondet` with the
   cause named — "strict row: k wide pick(s) served after stream <s>
   was exhausted at consumption n — the 3-stream invariance check did
   not cover this row; route to confluent, or declare depth" — unless
   the row carries `lane=confluent` (the enumerator certifies |set| = 1
   over all choice streams the row consumes — registry-point schedules
   and, since Stage D of the evaluation-order model (2026-09-20),
   expression-order picks (`unseqNext`) — [USER] 2026-09-21 «yes, I agree»,
   relayed, on the Stage D audit's F3; the 3-stream check is then
   redundant with the certificate and the guard does not run) or, when
   the enumerated set has ≥ 2 members, `lane=membership` with
   `members=`; or an explicit strict-lane `depth=N`, under which the
   gate runs SIX invariance streams: the three fixed adversarial
   streams (kept — they are skewed prefix probes that catch corners a
   uniform draw rarely does: memo §2.4's `beside-loop` is ok under the
   default and both long random streams yet refuses under all three
   fixed ones; on a depth row their coverage is recorded in the PASS
   detail as `fixed-probes-after=`, not required to be 0) PLUS three
   SEEDED streams of length N (seeds `1 2 3`, generator
   `lcg31(1103515245,12345) bits16..31`, both in the run meta as
   `depth_seeds`/`depth_generator`; the same explicit list goes to
   `native-json-run --choices` and to the tracer, so nothing depends on
   a shared generator). The seeded streams are UNIFORM RANDOM over
   0..65535, reduced mod the site's bound by `Choices.consume` — not
   demonic, not adversarial; the word "adversarial" belongs to the
   three fixed streams only. The seeded streams must themselves report
   `wideAfterExhaustion = 0` — else "strict row: k wide pick(s) served
   after the declared depth=N stream <seeded:seed:N> was exhausted at
   consumption n — … raise depth". The gate refuses a stream set that
   is not exactly 3 (no depth) or 6 (depth) streams, an empty stream,
   a tracer report labelled "default" past the first, or a report count
   other than streams + 1 — each by name. No default: a strict row whose
   streams were outrun with no declaration is red, never strict-green.
4. A REFUSAL under a variant stream (status ≠ the default run's) is
   reported at stage `lean-observation` — "a refusal under a variant
   stream is a refusal, not a variance" — never as `nondet`
   (assessment D-10 item 2 / memo P5; the one corpus row this moves is
   `channels/select-select/beside-loop`, FAIL either way).
5. The guard itself failing to run (timeout, kill, a tracer
   violation/alarm/driver disagreement, an empty stream in a worker,
   fewer than four reports) is a `nondet` FAIL naming that cause —
   never a pass.

`depth=N` is a strict-lane param (`why` stays `-`); on the enumerating lanes it
is refused as a category error. The strict lane's other param is `seed=<file>`
(the seeded rows below); the two may co-occur, each at most once. Sizing
convention [AGENT]: N = the smallest power of two ≥ 4·w, min 64, where
w is the default-stream wide count at the row's trace; the guard, not
the convention, is the check. `depth=` is the strict lane's spot check
made honest (N tied to a measurement), NOT a schedule-confluence
certificate. Lengthening the three fixed streams is NOT a remedy (it
moves the horizon without tying it to the row).

**Standing consequence — the 23 rows the guard reaches at the memo's
trace, plus 20 the first full gate run found** (memo §2.3; re-traced in the evidence dir's
`trace23.tsv`, with the three memo controls `fmt/sprintf-verbs/{d-int,
d-uint}` and `spec-examples-stmt/go-statements/named-call` confirmed
covered by the fixed streams):

- Scheduling rows routed to `lane=confluent` (3):
  `goroutines/pipeline/{two-stage,buffered-stage}`,
  `spec-examples-stmt/go-statements/func-literal` — `engine=dedup`
  (the `backedge=full` declared then was inert under dedup, retired with
  item 27), |set| = 1 checker-accepted; 20 gc draws each
  (plain/-race alternating) inside the singleton.
- Scheduling rows declaring `depth=N` (5) — FINDING: their state
  graphs do NOT close under `engine=dedup` within the fail-loud caps
  (40 GB cgroup kill or the 60M dedup work budget; per-row numbers in
  their `cases.tsv`), so they cannot honestly sit in a lane claiming
  invariance over all schedules: `spec-examples-stmt/prime-sieve/five`
  (w=187, depth=1024), `…/eight` (w=521, depth=4096),
  `goroutines/worker-pool/shared-feed` (w=32, depth=128),
  `sync/waitgroup-workers-join/workers-join` (w=28, depth=128),
  `imported-goose/channel/parallel-search-replace/search-replace`
  (w=42, depth=256).
- Capacity rows declaring `depth=N` (15; `appendSpill` only — the
  latitude is capacity, observable through `cap()`, which none reads):
  `fmt/fprintf-builder/describe-shape`, `fmt/fprint-writers/
  fprintf-buffer-shape`, `fmt/sprintf-dyn/{logger-shape,
  sprint-space-rule,verb-kinds}`, `fmt/sprintf-verbs/d-width` (64 each);
  `multipkg/mini-raft-twin/duel` (64), `…/{elect-propose-commit,
  perturb-picks,perturb-rev,starve-node}` (128); `strconv/format-parse/
  {format-int-vals,format-uint-bases}` (128), `…/parse-uint-errors`
  (256), `…/parse-uint-range-value` (512).

- Rows that landed AFTER the memo's 2026-09-01 trace (the noodler
  lane, 2026-09-03) and which the guard's first full run caught —
  the rule working on rows no one had classified by hand
  (`trace-new16.tsv` in the evidence dir): 5 → `lane=confluent`
  (`noodler/goroutines/{directional-params,fifo-one-sender,
  lockstep-transcript}`, `noodler/select/ping-pong`,
  `noodler/syncmisuse/unlock-from-other-goroutine`; `engine=dedup`
  closes each in < 1 s; 20 gc draws each inside the singleton) and 11
  → `depth=N` because `engine=dedup` does not close them within a 20M
  work budget / 24 GB (a FINDING each): `noodler/goroutines/
  {close-broadcast 256, once-across-goroutines 256, pipeline-three-stages
  256, rwmutex-readers 256, semaphore-total 512, worker-pool-sum 512,
  mutex-counter 2048}`, `noodler/closures/goroutines-loopvar` (256),
  `noodler/gostmt/pointer-method` (128), `noodler/syncmisuse/
  waitgroup-reuse` (128), `noodler/strconv-formatint/edges` (256,
  `appendSpill`). `mutex-counter` is the row that shows why the guard
  verifies the declared streams: a 256-entry seeded stream is itself
  exhausted there (67-123 wide picks after); 1024 covers, 2048 declared
  (the 4·w rule).
- Stage D of the evaluation-order model (2026-09-20, lane
  `core/unseq-stage-d-0920`, [AGENT]; `docs/2026-09-20_unseq-stage-d-design.md`
  §3): `spec-examples-stmt/continue-label` — the strict `depth=128` the
  Stage C pilot declared (w=18 `unseqNext` picks, a silent singleton) →
  `lane=confluent`, `engine=dedup` (work 200000; the width/sites declared
  then were inert under dedup, retired with item 27). Route α
  certifies the `unseq` scheduler's pick in the dedup engine (`innerVecs`
  N-PICK; `checkCert_slowObs` unchanged in statement), so the spot check
  became a certificate: 5122 unique states / 5145 edges / 24 dedup hits,
  |set| = 1 checker-accepted, against the DFS's 32805 leaves / 39.6M steps.
  The only row the rules license: the guard fired there, the observation is
  a silent singleton, the engine closes it. The 41 membership rows the engine
  also closes (their declared sets reproduced exactly) are recorded, not moved.
- The tracer's wall budget: `LEAN_TRACE_TIMEOUT_SECONDS` (default 8 ×
  `LEAN_TIMEOUT_SECONDS` = 480 s since 2026-10-07, 240 s before
  — the single-run default moved 30 → 60 s, [USER] «Agree 1 / 2»,
  relayed; the tracer makes eight interpreter
  passes where `native-json-run` makes one). The guard's first full
  run under the 30 s single-run budget timed out on four heavy
  zero-consumption rows (`imported-goose/unittest/replicated-disk`,
  `noodler/budget/{loop-100k,map-20k,recursion-5k}`: 20-64 s
  unloaded) — a named `nondet` FAIL, as designed; the knob is
  recorded in the run meta.

Fixtures: `scripts/test-lane-validation` — six manifest shapes (Part
A) and D1-D7 (Part B, `--with-go`; D7a-c pin the harness-defect
refusals: empty stream, tracer labels every stream "default", too few
tracer reports): the exhausted strict row refused
with the named cause; the same row confluent → certified; `depth=128`
→ PASS with `wide=`/`depth=`; `depth=4` → refused naming the seeded
stream; the variant-stream refusal reported at `lean-observation`;
`depth=0` refused by the harness's own re-validation.

### Seeded rows: `seed=<file>` (seeded-heap slice C, 2026-10-12)

A strict row may run its subject over a **seeded heap**: `params` declares
`seed=<file>`, a `golean-seed-v1` file (`docs/cli.md` §2.1.1) given relative to
the case directory (plain path characters, no absolute path, no `.`/`..`
component; a REGULAR file, not a symlink, whose resolved path lies inside the
case directory — the manifest and the runner both refuse otherwise, by name), and `args` takes the seeded tokens above. Design:
`docs/2026-10-09_seeded-heap-design.md` §7. Both twins read the same file:

- the machine: `native-json-run --seed <file>` with the tokens mapped in order to
  `--arg-int`/`--arg-ref`/`--arg-nil`, on the default stream AND every
  invariance stream (a seeded row keeps the full strict claim), and
  `choice-trace --seed …` for the depth guard (the tracer seeds since slice C;
  `coverage-observations` does not, so `seed=` on an enumerating lane is refused
  by name — design D6);
- the Go oracle: `tools/coverageharness --seed <file> --args <tokens>`
  (`tools/coverageharness/seed.go`). The generated `main` allocates every cell
  (`new(T)`, the file's type spelling pasted), fills them in cell order by
  reflect with the resolver's typing (ints range-checked at their kind, every
  declared struct field required and no other, a blank field refused, arrays
  of the exact length, `nil` only at a pointer — a `ref:`/`nil` ARGUMENT's
  parameter judged a pointer by its reflect kind, so a named pointer type or an
  alias binds as on the machine — a `ref`'s target type equal to
  the pointer's element type), binds the arguments, calls the subject, and
  observes in GoLean's seeded shape: a pointer into a cell is
  `{"tag":"seedRef","cell":k,"path":[…]}` (matched by address AND element type
  against every addressable sub-object of every cell — exact for a non-zero-size
  type, refused by name for a zero-size one), the `seed` key holds the cells'
  final values, and a pointer outside the seed refuses the whole observation
  with status `unsupported` («seed readout: result i / cell k holds a pointer
  outside the seed …», GoLean's text class). The file's shape and type
  spellings are refused at generation, by the classes GoLean's decoder refuses.

The observations then compare through `observation-eq` exactly like any other
row; `panic` rows carry no `seed` key on either side. A row whose subject lets
a pointer escape the seed is NOT a corpus row: both sides refuse (status
`unsupported`), and a refusal never passes, so it would be red by design. The
pair is pinned as controls instead: the machine's refusal by
`scripts/check-wire-boundary` (`seed-escape`), the Go twin's by
`tools/coverageharness/seed_test.go` (`escaping result`, `escaping cell`).
The rows live under `Corpus/coverage/exec/seeded/`, tagged `seeded`, each seed
file BESIDE the case's `main.go` (`seed-<name>.json`): a subdirectory without a
`cases.tsv` is a husk case directory to `scripts/check-coverage`.

## Go Source Contract

Every executable package contains `main.go`.

Each row names a subject function. The subject function contains the behavior
under test. Lean executes that function directly after frontend lowering.

For Go execution, the runner generates a temporary harness from metadata rather
than trusting a handwritten `main`. The generator strips the source `main`,
copies every non-test Go file in the package into the temporary directory,
calls the named subject with the metadata integer args, and encodes the return
values as schema-versioned observations. For `panic` cases, it lets the process
panic; the runner extracts the actual Go panic line and compares that
normalized observation against Lean.

**The `output` field (stdlib slice 3, 2026-09-04; split hardened at its
audit fix round A2, 2026-09-05).** Every observation — on BOTH sides and at
EVERY status — carries `"output"`: the program's own fd-2 bytes, i.e. what
`print`/`println` wrote (the machine's `StepEvent.out` events folded in
step order into `Readout.output`; on a terminal, the prefix printed before
it — G-OUT). The field is always present (possibly `""`), so the comparator
is total and an old-shape observation without it fails the exact-key decode
rather than comparing. Oracle side: the runner captures the `go run` child's
stdout (the harness JSON) and stderr SEPARATELY (`go_run_oracle` →
`oracle.stdout`/`oracle.stderr` under the case's go-run dir; `GOFLAGS` and
`GODEBUG` pinned so no build chatter reaches the compared channel) and
recovers the program prefix with the harness's `--split-stderr` mode
(`tools/coverageharness/split.go`), FAIL-CLOSED: `ok` = the whole stream;
`panic` = the ONE occurrence of `panic: ` in the stream (repanic
continuations `\n\tpanic: ` excepted), at a line start and followed by gc's
goroutine trace header — a program that printed the marker text anywhere,
or printed without a trailing newline so its text and the report share a
line, refuses; `fatal`/`deadlock` = the one `fatal error: `/`panic: `
marker in total (the panic-then-fatal unwinding shape counts once); `race` =
the prefix must be empty (TSan's report interleaves asynchronously; rows
with program output are not comparable, and output AFTER the report is not
detected — `builtins/print/refused/race-with-output`, FR-29 (iv)); non-UTF-8
bytes refuse (the JSON string cannot carry them byte-exactly — the Lean
encoder refuses the same way). A refused split is a red row at stage
`go-observation` naming the harness's cause. Standard output (fd 1) is NOT
an observable (os.Stdout is gate G7); the harness JSON owns that channel.

Handwritten `main` functions may remain useful for `go run` debugging, but they
are not part of the differential contract.

The corpus unit is a Go package directory. The current Gobra frontend can only
export a single `main.go`; multi-file executable packages therefore fail red in
the `frontend-export` stage until a package-aware frontend adapter exists.

## Feature Tags

Feature tags are controlled by `Corpus/coverage/tags.tsv`. The manifest
generator rejects unknown tags, malformed tags, and duplicate entries in the
vocabulary. Add tags intentionally; do not use ad hoc spellings in case files.
The `nondet` tag marks membership-lane cases (it was reserved for a future
relation-style oracle until 2026-08-05, when the membership lane landed):
a `nondet`-tagged executable case must declare `lane=membership`, and vice
versa. The compile-negative lane rejects the tag outright.

## Runner UX

Target commands:

```sh
scripts/coverage list
scripts/coverage list --tag slices
scripts/coverage run
scripts/coverage run slices/append-overlap
scripts/coverage run --prefix slices/
scripts/coverage run --tag maps --tag nil
scripts/coverage run --status panic
scripts/coverage run --last-failed
scripts/coverage negative
scripts/coverage negative --id slices/slice-compare
scripts/coverage negative --tag compile_error
scripts/coverage report
scripts/coverage report --full
scripts/coverage report --by tag
scripts/coverage report --by stage
```

`scripts/diff-one <id> ...` should remain as a compatibility alias for exact
ids. The main implementation should be a single coverage driver that builds a
temporary normalized manifest and delegates to the existing differential
runner.
`scripts/coverage all` runs both executable and compile-negative lanes and
rejects filters, because executable and negative ids live in separate
namespaces.

## Reports

The runner should continue printing one line per case:

```text
PASS<TAB><id><TAB><features>
FAIL<TAB><id><TAB><features><TAB>stage=<stage><TAB>detail=<detail>
```

It also writes machine-readable results:

```text
artifacts/coverage/latest.tsv
artifacts/coverage/latest.meta.tsv
```

Filtered runs still write `latest.tsv`, but the metadata records `full_run`,
filters, frontend, manifest hash, manifest case count, total corpus case count,
git commit, and dirty flag.
Reports warn when `latest.tsv` is not a full corpus run. Full runs also update
`artifacts/coverage/latest-full.tsv`, which can be summarized with
`scripts/coverage report --full`; full reports are checked against the current
generated full manifest so stale reports cannot look authoritative.

Summary reports should include:

- total cases, pass count, fail count;
- pass/fail by feature tag;
- fail count by stage;
- expected status distribution;
- top red cases by stable id.

This makes it reasonable to keep a large suite where many features are still
red, because the red cases are categorized and measurable.

The default executable lane is a conformance signal, not an expected-failure
test suite. A case that does not match Go remains a failure even when the
failure is understood.

### Diagnosing a refusal

A `FAIL/frontend-export` row (or any program the frontend refuses) shows
ONE cause — the first refusal the emitter hit — and fixing it may only
reveal the next (the cedar-go census's FR-22 → FR-23 → FR-24 sequence,
export fraction unchanged each time). [USER] direction (4) of
`docs/language-coverage-ledger.md` §0 (2026-09-04, coordinator-relayed:
«it'd be useful if we didn't just get stuck without any information
about *why* it's happening») is served by `scripts/lower-diagnose <dir |
main.go> [--json] [--tsv]` (`tools/lowerdiag`;
`docs/2026-09-04_lower-diagnose.md`): it runs the real frontend for the
first refusal (what a user sees today), then a STATIC go/types demand
census over EVERY declaration of the program and its case-local
imports, judged against `docs/stdlib-admission-register.md` and the
machine-owned surface, and reports the full histogram of blockers by
cause and ledger FR row, the sole-blocker counts, the cumulative
projection ("if these were fixed, N more declarations lower"), the
per-package export status (whole-export kills and who inherits them),
and a distance line. The frontend's own refusal now ends with a line
pointing at it. It is REPORT-ONLY lane tooling: it writes no wire, every
artifact opens with `DIAGNOSTIC — NOT A LOWERING`, its output root is
`artifacts/lower-diagnose/`, and no gate, baseline or corpus path reads
it; `scripts/cedar-census` uses the same engine for its static demand
step (one implementation of the cause taxonomy, `tools/lowerdiag/causes.tsv`,
checked against the ledger's FR ids by `go test ./tools/lowerdiag`).

### The tracked baseline and its stage column

`baselines/native-full.tsv` records one `result<TAB>id<TAB>stage<TAB>cause`
row per case (`baselines/negative-full.tsv`: `result<TAB>id<TAB>stage`,
judged with `--no-cause`); `scripts/coverage-baseline-diff`
requires every case a run actually ran to reproduce its row exactly
("same set = no regression"). ONE relaxation exists, per row and
[USER]-ruled per row (ruling (a), 2026-09-03 — «(1) the guard - agree
with the redommendation, do (a)», relayed by the [AGENT] coordinator;
primary record `docs/assessment/decisions-2026-08-31.md`, 2026-09-03
addendum): the stage column may be a
`|`-separated ALTERNATION such as `nondet|differential`, and the observed
stage then matches iff it is a member of that set. The result column is
never relaxed. The form is reserved for a red whose STAGE depends on the
oracle's schedule rather than on the machine: gc samples one of several
values, and because `scripts/diff-coverage` runs the strict-lane
differential check before its oracle-invariance re-run and returns early,
the same red lands at `differential` on one gc sample and at `nondet` on
another (`channels/select-select/beside-loop`, "5 or 90 in gc" — the only
row today). The rules are fail-closed at exit 2 (REFUSED, never "no
drift"): non-PASS rows only — a PASS is never absorbed by an alternation
and a PASS/FAIL flip in either direction is drift; every member is a
stage word `scripts/diff-coverage` emits, at least two distinct; the
comment block immediately above the row carries a `# reason:` line naming
the oracle mechanism. The other consumers of the stage column treat an
alternation as fidelity-bearing iff EVERY member is a fidelity stage
(`scripts/check-bugs.sh` (6) flags a mix loudly; the row never drops out
of a count). Durability: a `# reason:`
block over a non-alternation row is REFUSED, and `scripts/ci`'s re-pin
guard runs `scripts/check-alternation-survival` — every alternation row
of the previous baseline must still be one, unless a header comment
`# alternation removed: <id> — <why>` names its removal. Fixtures:
`scripts/test-lane-validation` Part A4.

### The cause column (refusal-cause pinning, 2026-10-12)

A FAIL row's stage alone let a crash, a timeout, a different refusal or
(at `lean-observation`) a machine panic match a designed red at the same
stage (`docs/2026-10-12_refusal-cause-pinning-design.md` §2 — it happened
once, BUG-090). Since 2026-10-12 ([USER] «1,3-6 approved», D1-D6 of that
note) the differential baseline's fourth column pins a normalized CAUSE
KEY, derived from the run's detail by `scripts/coverage-cause` and
compared by `scripts/coverage-baseline-diff` (a changed key at the same
result/stage is drift, printed `CAUSE CHANGED`). The grammar (first rule
wins; the script's header is authoritative): a runner non-verdict at any
stage → `killed:N` / `timeout` / `undecided:N` / `undecided:decode`;
`frontend-export` → the `tools/lowerdiag/causes.tsv` class
(`FR-15/complex`) of the frontend's refusal or of a run-time quarantine
stub's message, `crash:frontend` for any frontend exit but 1 (the runner
records `native frontend (exit N): …`); `lean-observation` →
`<status>:<id>` from `scripts/machine-causes.tsv`; every other stage, and
every PASS row, `-`. An unclassified text keys as `fe?:<head>` or
`<status>:?` — pinned all the same, and reported under `scripts/ci`'s
speedbump heading (`scripts/coverage-cause --unclassified`) until a table
row names it. On an alternation row the cause is a `|` set paired with the
stage set member by member (`unsupported:select-select|-`). The column is
REGENERATED from a recorded full run, never hand-edited:
`scripts/coverage-cause --apply baselines/native-full.tsv
artifacts/coverage/latest.tsv` keeps every row's result/id/stage (it
refuses if the run disagrees — re-pin those rows first) and rewrites the
key; alternation rows keep their hand-set paired cause. A record made
before the runner wrote the frontend's exit code is refused (re-run
`scripts/ci --diff`).

The NEGATIVE lane has a GoLean leg on the same date (D3): a row passes only
if gc rejects it with the expected substring AND the native frontend,
built from the tree, exits 1 as a rejection — `type-check:` (but not an
importer failure, `could not import`, which is `frontend-reason`), a
go/parser error on one of the row's files, or the file-selection boundary
(BUG-108); otherwise it fails at `frontend-accepts` (exit 0: GoLean lowered
a program gc rejects), `frontend-crash` or `frontend-reason`. The class is
the PASS row's detail (`frontend=type-check|parse|file-selection`). One row
is red by design: `functions/main-undeclared` (BUG-125 — the frontend is a
subject lowerer and accepts a `package main` with no `func main`).

A FAIL row whose cause is re-pinned from a named key into the
non-verdict/crash family (`killed:`, `timeout`, `undecided:`, `crash:`)
needs a `docs/BUGS.md` `- Cases:` line, like a PASS→non-PASS flip
(`scripts/check-cause-regressions`, run by `scripts/ci`'s re-pin guard).
A re-pin that REMOVES a row — PASS or FAIL, e.g. with its retired fixture —
must name it in the new baseline's header: `# removed: <id> — <why>`
(`scripts/check-row-removals`, the same guard; a `# alternation removed:` line satisfies it too — one line retires an alternation row; the `# alternation removed:`
convention). A removed PASS row still needs its `BUGS.md` Cases line as
well (the flip rule is unchanged).

Non-verdict exits of a comparator, oracle, driver or enumerator run are
reported at the stage of the CHECK that could not complete — the stage
vocabulary is unchanged — with a detail that names the cause and what
was NOT established. Only exit 0 and exit 1 are verdicts (equal / not
equal; ok / error observation; go run green / red). Wall-clock kills
(the runner's `*_TIMEOUT_SECONDS` budgets; exit 124 from
`run_with_timeout`) read `… TIMED OUT after <N>s (<KNOB>) — <what was
NOT established>` (e.g. `lean-observation: Lean run TIMED OUT after 30s
(LEAN_TIMEOUT_SECONDS) — no observation produced`; `nondet: … re-run under
stream [...] TIMED OUT … — invariance NOT certified`; `membership:
enumerator TIMED OUT … (coverage not certified)`). Signal deaths (the
wrapper's 128+signal: 137 SIGKILL — a cgroup/OOM kill or scripts/capped's
— 143 SIGTERM, any other 128+n) read `… KILLED (exit N — …; did not
decide)`; the comparator's undecodable-observation refusal reads
`observation-eq could not decode the observation (exit 2 — did not
decide; comparator said: <decode message>)`; any other code reads
`… failed with exit N (did not decide)`. None of these is ever a pass,
and none is ever rendered as a differential mismatch, an iteration-order
variance, driver drift, an invalid Go observation, or the membership
soundness alarm — a killed command has decided nothing
(`scripts/test-lane-validation` T1-T8;
`docs/evidence/2026-09-03_timeout-cause/`,
`docs/evidence/2026-09-03_runner-exitcode/`).

### Go version diversity (report-only; release-readiness item 32)

`scripts/capped scripts/go-version-diversity [--staticinit] [--record <dir>] <goX.Y.Z>`
re-runs the differential and negative corpora with ONLY THE ORACLE on another
Go toolchain and compares every row with the recorded run of record
(`artifacts/coverage/`, at the pin and the current manifests — else it refuses:
«run scripts/ci --diff first»). The seam is the runners' knob
`GOLEAN_ORACLE_GOTOOLCHAIN=<v>` (headers of `scripts/diff-coverage` and
`scripts/coverage-negative`): the per-row `go run` / gc `go build` alone gets
the module-cache toolchain's `PATH`/`GOROOT` (Go ignores `GOTOOLCHAIN` in the
oracle's GOPATH mode — measured), a `runtime.Version()` canary checks the switch
took, and the native frontend and harness stay on the pin, so the lowering is
not a second variable. Both toolchains are in each run's meta
(`go_toolchain_frontend`, `go_toolchain_oracle`, `go_drift_actual=true`), and an
oracle off the pin still needs `GOLEAN_ALLOW_GO_DRIFT=1` (the script sets it).
Artifacts go under `.tmp/go-diversity/<v>/`; the report is printed and written
to `report.txt` there.

What it compares: per row result, stage, cause key and the normalized detail
(artifact roots, GOROOT paths, addresses, goroutine ids); on rows where all of
those agree, the oracle's own recorded observation (stdout, the fd-2 split, the
abort message); per negative row result, stage and detail; with
`--staticinit`, gc's static-init verdict table re-recorded under `<v>`. Classes:
«oracle does not compile under `<v>`» (a fixture needs a feature that toolchain
lacks — by construction, not a behaviour change), result/stage/cause flips,
detail changes, membership sampling captions that moved (not a version signal),
and oracle-observation changes (strict rows listed; sampled lanes counted).

What a difference means: Go's behaviour differs between the two versions on
that row (the machine's side does not depend on the Go version) — a latitude
the model may need to admit, a version-specific behaviour the pin's written
reason should name, or a fixture tied to a newer toolchain. It is a FINDING for
a human, never a re-pin: the oracle of record moves only deliberately, with a
full run and a written reason (CLAUDE.md, trusted surface 2). Exit 0 when the
runs complete (differences included), 1 when a run could not complete, 2 on a
refusal. Only toolchains already in the module cache run inside the sandbox;
the [USER] fetches one outside it with `GOTOOLCHAIN=<v> go version`.
`scripts/oracle-version-sweep` (2026-09-01) is the older probe: it puts the
candidate first on PATH for the whole run, frontend included, and compares
(result, stage) only.

## Migration Plan

1. Add JSON output next to `artifacts/coverage/latest.tsv`.
2. Expand the corpus aggressively from `Corpus/challenges/semantic-edges`.
3. Add optional suite files under `Corpus/coverage/suites/` for curated subsets.

The central executable and compile-negative manifests have been removed.
Generated normalized manifests are an implementation detail of the current
frontend/Lean and Go-negative runners.
