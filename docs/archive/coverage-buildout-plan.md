> **ARCHIVED (2026-07-21).** Historical record — superseded or completed; see `docs/archive/README.md`. Do not treat as current guidance.

# Differential Coverage Buildout Plan

This document is the authoritative operating guide for the long-cycle buildout
of the Go differential coverage suite. An agent should be able to read this
document and carry out the test-suite buildout without relying on prior
conversation. The job is to grow a broad, precise, ordinary-Go corpus that
exposes unsupported language features, frontend gaps, semantic mismatches, and
static errors without hiding any of them.

The suite is not a benchmark collection and not a demo gallery. It is a
conformance instrument for building a faithful executable Lean semantics for
Go.

## Start Here If You Have No Other Context

Your task is to build out the differential test suite, not to make the Lean
semantics pass it. Add ordinary Go litmus tests that expose real behavior. A
valid red test is progress. An invalid, flaky, hidden, weakened, or
frontend-specific test is not progress.

The most important rule:

**Never change a test away from ordinary Go, remove a test, weaken metadata, or
add expected-failure machinery merely because the current frontend or Lean
semantics cannot handle it. Gaps must stay visible.**

Before doing any work, read this document. When unsure, prefer a smaller,
clearer Go litmus that makes one behavior observable. If the suite or harness
cannot express an important class of Go behavior without cheating, stop and
write down the needed harness design change.

Every iteration should improve one of two things:

- breadth: a previously uncovered Go behavior is now represented by a focused
  active or deferred test;
- accounting: `docs/coverage-ledger.md` more accurately records what is
  covered, missing, deferred, or unexpressible in the current harness.

Adding tests without improving breadth or accounting is churn.

## Agent Contract

When working on the coverage buildout, the agent is responsible for the test
suite, not for making the semantics pass. A normal buildout iteration may add
many red cases. That is success if the cases are valid, focused, deterministic,
and accurately classified.

The agent must:

- preserve ordinary Go source as the only executable corpus input;
- add tests that reveal real Go behavior;
- keep every new case small enough for code review;
- run the manifest and Go-side validation commands before stopping;
- report the new executable and negative case counts;
- report any invalid generated code, harness limitation, or metadata issue;
- stop and ask for a design decision only when the test harness or corpus
  policy cannot express an important class of Go behavior.

The agent must not:

- implement semantics merely to make new tests green unless explicitly asked;
- weaken, skip, delete, or rewrite a valid red test to improve pass rate;
- add expected-failure metadata for Lean gaps;
- fork a test into a Gobra-friendly variant;
- hide nondeterministic cases in the default equality lane;
- paste generated code without reducing it to focused litmus tests.

## Off-Rails Guards

Long-running agents tend to drift in predictable ways: adding large low-signal
programs, chasing green results, encoding frontend quirks, or hiding failures.
Use these guards to stay on task.

### Batch Size

Work in reviewable batches:

- one feature family or coherent semantic area per batch;
- roughly 10-30 executable cases per batch unless the cases are trivial and
  mechanically related;
- roughly 3-10 compile-negative cases per batch;
- one checkpoint or commit per coherent slice.

If a batch becomes hard to summarize, it is too large. Stop, validate, and
write a handoff summary.

### Required Validation Gate

Before any pause, handoff, or commit, run:

```sh
scripts/coverage-manifest --list
scripts/coverage-negative-manifest --list
GOLEAN_FRONTEND=none scripts/coverage run
scripts/coverage-negative
git diff --check
```

For `GOLEAN_FRONTEND=none scripts/coverage run`, the acceptable executable
failure stage is `frontend-export`. Any `manifest`, `go-harness`, `go-run`,
`go-observation`, or other pre-frontend failure means the corpus itself is
wrong or the harness cannot express the case yet. Fix that before continuing.

If negative cases were not changed, `scripts/coverage-negative` should still be
cheap and should still pass. If it fails, fix the negative corpus before
continuing.

### Handoff Discipline

Every pause must say what changed and what was validated. Use the handoff
format near the end of this document. Do not leave future agents to infer
whether a dirty tree is intentional, whether a partial run was full, or whether
red cases are expected.

### Review Questions

Ask these questions about every new case:

- Is this ordinary Go source?
- Does the case exercise one primary behavior?
- Can a reviewer compute the expected result locally from the code?
- Does an `ok` case return an observable value?
- Does a `panic` case use a real Go panic substring?
- Is this deterministic under ordinary Go execution?
- Is every feature tag meaningful and already canonical or intentionally added?
- Would this case still make sense if Gobra were replaced by a different
  frontend?
- Is any failure left visible rather than hidden?

If the answer to any question is no, fix the case before adding more tests.

### Duplicate Control

Before adding a case:

1. Search existing cases by feature tag:

   ```sh
   scripts/coverage list --tag <tag>
   ```

2. Browse the relevant corpus area:

   ```sh
   find Corpus/coverage/exec/<area> -maxdepth 3 -type f | sort
   ```

3. Check `docs/coverage-ledger.md`.

Add the case only if it covers a new behavior, a new interaction of behaviors,
a boundary condition not already represented, a static negative not already
represented, or a clearer reduction that should replace a weaker case.

Near-duplicates are allowed only when the distinction is semantic. Examples:

- nil slice versus empty slice is a meaningful distinction;
- array copy versus slice header copy is a meaningful distinction;
- `break` in a switch versus labeled `break` out of an outer loop is a
  meaningful distinction;
- the same integer expression with different variable names is not meaningful;
- the same map lookup with key `1` instead of key `2` is not meaningful.

If a new case supersedes an older weaker case, do not silently delete the old
case during buildout. Note the supersession in the handoff and leave cleanup to
an explicit review step.

## Mission

Build an incredibly broad suite of tiny Go litmus programs covering essentially
all expressible Go language patterns and idioms. Each executable litmus program
must be run as real Go and compared against Lean execution of the same source
after frontend lowering. Each static invalid-Go litmus must be checked by the
Go toolchain in the negative lane.

The expected outcome during buildout is not a green suite. The expected outcome
is a large, accurate red/green map:

- green means the current frontend, lowering, GoCore semantics, Lean execution,
  and observation comparison agree with real Go for that case;
- red means a real gap exists and is categorized by stage;
- no test is weakened, skipped, rewritten into another language, or moved out
  of the suite merely because it is currently red.

## Non-Negotiable Principles

- The canonical input is ordinary Go source in `Corpus/coverage`.
- Do not create Gobra-specific, Lean-specific, or frontend-specific variants of
  a test.
- The Go path and Lean path must consume the same source-level package.
- Gaps must be exposed, not hidden. Frontend failures, `unsupported`, `stuck`,
  `error`, panics, and mismatches remain visible red cases.
- A passing executable case must observe the behavior under test.
- Do not add tests whose only purpose is to increase case count.
- Do not add code that is random, flaky, time-dependent, environment-dependent,
  or scheduler-dependent to the default equality lane.
- Do not use standard-library behavior as a substitute for language semantics
  unless the case is explicitly about a language-required builtin or runtime
  behavior.
- Static invalid-Go behavior belongs in the negative compile lane, not in the
  executable differential lane.

## Coverage Lanes

Every interesting Go behavior must belong to exactly one current lane or one
explicit future lane. Do not force a behavior into the wrong lane just to make
it runnable today.

### Lane 1: Deterministic Executable Differential

Path:

```text
Corpus/coverage/exec
```

Use this lane for ordinary valid Go programs whose behavior can be observed
deterministically by running the subject function. This is the main conformance
lane. Cases may be currently red because the frontend or Lean semantics cannot
handle them.

Allowed outcomes in metadata:

- `ok`;
- `panic`.

Not allowed in this lane:

- expected Lean `unsupported`, `stuck`, or `error`;
- nondeterministic scheduling or random map/select order;
- tests whose only observation is printed output;
- static invalid-Go programs.

### Lane 2: Compile/Typecheck Negative

Path:

```text
Corpus/coverage/negative/compile
```

Use this lane for invalid Go programs that should be rejected before execution.
These cases are checked with `go build`.

Examples:

- unused locals or imports;
- invalid comparisons;
- invalid addressability;
- invalid control-flow statements;
- invalid generic method declarations;
- duplicate declarations;
- type errors.

Do not place runtime panics in this lane. Runtime panics are valid Go programs
and belong in the executable lane with `expected_status=panic`.

### Future Lane: Nondeterministic / Relational Runtime

Use a future nondeterministic lane for valid Go behaviors whose correct result
is a set or relation rather than a single observation.

Examples:

- map iteration order;
- select among multiple ready cases;
- goroutine scheduling;
- races, where applicable;
- blocking behavior that needs timeout-free semantic classification.

Until this lane exists, keep such cases in `Corpus/challenges` or mark them in
`docs/coverage-ledger.md` as deferred. Do not add them to the default equality
lane.

### Future Lane: Unsafe

Use a future unsafe lane for `unsafe.Pointer`, `uintptr`, layout, alignment,
and representation-sensitive behavior. The default executable lane should not
import `unsafe` unless a design decision explicitly admits a particular safe
subset.

### Future Lane: Standard Library / Runtime

Use a future stdlib/runtime lane for behavior primarily defined by packages
rather than by the Go language core.

Examples:

- `fmt` formatting details;
- `encoding/json`;
- `time.Time`;
- `sync.Once`;
- `bytes.Buffer`;
- `errors.Is`.

Some standard-library usage is acceptable in active tests only when it is
incidental and not the behavior under test. Prefer avoiding imports entirely.

### Future Lane: Fuzzed / Generated Programs

Use a future generator lane for GoSmith, Microsmith, or other synthesized Go
programs. Generated programs must be reduced before promotion into the active
litmus corpus unless the generator lane itself has a clear oracle and triage
format.

Do not paste raw generated programs into `Corpus/coverage/exec`.

## Go Version Policy

The active corpus should target the Go version installed in the development
environment unless a case explicitly documents a version requirement. Agents
must record version-sensitive behavior rather than assuming all Go versions
agree.

Current version-sensitive areas include:

- Go 1.22 loop variable capture changes;
- Go 1.22 range-over-integer;
- Go 1.23 range-over-function iterators;
- Go 1.21 `panic(nil)` behavior;
- generic and type-set behavior introduced in Go 1.18 and refined later.

Rules:

- If behavior changed across Go versions, include the required version in the
  case comment and in `docs/coverage-ledger.md`.
- If the installed Go toolchain does not support the syntax or behavior, do not
  add it to the active lane. Record it as deferred.
- Do not encode version-dependent nondeterministic behavior as a single
  equality observation.
- Prefer stable, currently supported language features for the active lane.

When a long-cycle agent starts, it should note `go version` in the handoff if
it adds version-sensitive cases.

## Where Tests Live

Executable differential cases:

```text
Corpus/coverage/exec/<area>/<case>/main.go
Corpus/coverage/exec/<area>/<case>/cases.tsv
```

Static compile/typecheck-negative cases:

```text
Corpus/coverage/negative/compile/<area>/<case>/main.go
Corpus/coverage/negative/compile/<area>/<case>/case.tsv
```

Challenge tours and large reference programs stay outside the active suite
until split into focused litmus cases:

```text
Corpus/challenges/
```

## What A Good Executable Litmus Looks Like

A good executable litmus is small, deterministic, and focused. It usually has:

- one `package main`;
- one source file unless the feature requires package-level/multi-file
  behavior;
- one primary subject function named in `cases.tsv`;
- no dependency on handwritten `main`;
- no imports unless the feature requires them;
- no sleeps, wall-clock time, randomness, filesystem, network, or process IO;
- a return value that directly encodes the semantic behavior under test.

Prefer this shape:

```go
package main

func sliceHeaderByValue() int {
	a := []int{1, 2, 3}
	grow := func(s []int) {
		s = append(s, 99)
		_ = s
	}
	grow(a)
	return len(a)*100 + a[0]*10 + a[2]
}
```

Avoid this shape:

```go
package main

import "fmt"

func main() {
	fmt.Println("look at these outputs")
}
```

The harness ignores handwritten `main`, so a test that only prints from `main`
is not a differential test.

## Reducing Real-World Or Generated Code

Real projects and generators are useful for discovering missing patterns, but
active corpus cases must be reductions, not imports of large source fragments.

Reduction workflow:

1. Identify the semantic behavior in the source program.
2. Remove package dependencies, IO, logging, testing frameworks, and unrelated
   library calls.
3. Replace complex data with small literals.
4. Replace printed output with a returned observation.
5. Preserve the exact Go behavior being tested.
6. Add the smallest case that still fails if that behavior is modeled
   incorrectly.
7. Add a short source comment only when it records provenance or a version
   constraint that would not be obvious from the code.
8. Update `docs/coverage-ledger.md`.

Good reductions preserve semantic essence. Bad reductions preserve incidental
shape.

Example:

- Source idiom: a real project relies on a nil map read returning the zero
  value.
- Good litmus: `var m map[string]int; return m["x"]`.
- Bad litmus: copy the whole project function with logging, config structs,
  error wrapping, and unrelated branches.

For generated programs, reduce by deleting unrelated statements while checking
the behavior still appears under `go run`. If the generated program is too
large to reduce confidently, leave it in a challenge area with notes instead of
adding it to active coverage.

## Coverage Accounting

The buildout must be measurable. A long-running agent should not merely add
cases; it should make it clear which Go behaviors are covered, missing, or
deferred.

The mutable coverage ledger lives in `docs/coverage-ledger.md`. Update that
file when adding a meaningful feature area, promoting challenge cases, or
discovering a deferred/unexpressible behavior. The ledger does not need to list
every single case, but it must identify representative active cases and
important missing subareas.

Do not edit this buildout plan during ordinary corpus buildout. This plan is
stable policy. The ledger is the editable accounting artifact.

Ledger status values:

- `active`: active corpus contains focused cases;
- `partial`: active corpus contains some cases but important subareas remain;
- `deferred-nondet`: needs a nondeterministic or relational oracle;
- `deferred-stdlib`: primarily standard-library/runtime package behavior;
- `deferred-unsafe`: requires unsafe/layout policy;
- `deferred-version`: requires a Go version not available or not yet adopted;
- `missing`: known important area with no active case yet;
- `unexpressible`: cannot currently be expressed honestly in the harness.

When marking `unexpressible`, explain the harness limitation. Do not use
`unexpressible` for ordinary frontend or semantics gaps.

Coverage accounting is as important as test code. If an agent discovers a
major missing area but cannot add good cases in the current batch, it should
update `docs/coverage-ledger.md`.

## Observations

Executable `ok` subjects must return at least one observable value. Current Go
harness observations support scalar values, strings, arrays, and structs. For
features involving slices, maps, channels, interfaces, function values, or
other currently unsupported observation shapes, return a deterministic integer
checksum or a small supported struct instead of returning the unsupported value
directly.

Checksums are acceptable only when they are transparent and local. Keep the
code simple enough that a reviewer can compute the expected result by reading
the test. Do not pack many unrelated facts into one opaque checksum.

Good:

```go
func nilMapRead() int {
	var m map[string]int
	return len(m)*100 + m["missing"]
}
```

Bad:

```go
func everythingAboutMaps() int {
	// 80 lines, many unrelated maps, huge checksum.
}
```

For runtime panic cases, set `expected_status=panic` and provide a concrete
substring from real Go's panic message in `expected_reason`. The runner
normalizes the actual Go panic line and compares Lean against that normalized
observation.

## Metadata Rules

Each executable `cases.tsv` has exactly:

```text
id<TAB>subject<TAB>args<TAB>expected_status<TAB>expected_reason<TAB>features
```

Rules:

- Use `-` as the row id for a one-case package.
- Use short kebab-case row ids for grouped cases.
- Use source-level function names as subjects.
- Use `ok` or `panic` only for `expected_status`.
- Use `-` as `expected_reason` for `ok`.
- Use a real Go panic substring for `panic`.
- Use only tags listed in `Corpus/coverage/tags.tsv`.
- Add tags intentionally when needed; do not invent near-duplicates.
- Keep tags semantic, not implementation-specific.

Each compile-negative `case.tsv` has exactly:

```text
expected_substring<TAB>features
```

Use a stable substring from `go build` output. Avoid line numbers or
machine-specific paths.

## What Not To Generate

Do not add garbage code. In this project, garbage code includes:

- big generated tours pasted directly into `Corpus/coverage/exec`;
- examples that require a human to inspect printed output;
- tests that only exercise `fmt`, `json`, `time`, `runtime`, `reflect`, or
  other library behavior when the intended target is language semantics;
- tests with many independent features and no clear primary behavior;
- duplicate tests that differ only by variable names or constants;
- complicated helper frameworks inside individual cases;
- table-driven tests where each row is itself a different language feature;
- tests that rely on goroutine scheduling, map iteration order, select
  fairness, timers, random seeds, addresses printed as strings, or process
  environment;
- tests that use `unsafe` except in a clearly tagged future unsafe suite;
- tests that pass because they observe nothing;
- tests that are changed to fit Gobra rather than ordinary Go;
- tests moved out of the active suite because they are currently red.

If a case is interesting but too broad, split it. If it is interesting but
nondeterministic, put it in a challenge file or future nondeterministic lane,
not the default executable lane.

## Allowed Creativity

Agents should actively look for missing Go patterns, not merely promote cases
from existing challenge files. Good gap-finding sources include:

- the Go language specification;
- Go release notes, especially version-specific language changes;
- `go/types` and `cmd/compile` error behavior;
- Goose, new Goose, and Perennial examples;
- real-world Go idioms from Kubernetes, etcd, Docker, CockroachDB, Terraform,
  Prometheus, and the Go standard library;
- bug reports about surprising Go behavior;
- small reductions from generated programs, once a generator lane exists.

Creativity must produce precise litmus tests. A surprising behavior should be
reduced to the smallest readable program that still exercises it.

## Coverage Taxonomy

The buildout should cover all major Go semantic areas. This list is not
exhaustive; missing areas should be added as they are discovered.

### Basic Evaluation

- literals, zero values, default values;
- unary and binary operators;
- evaluation order;
- short declarations and assignment;
- simultaneous assignment;
- addressability;
- selector expressions;
- builtin functions.

### Numeric Semantics

- signed and unsigned integer widths;
- overflow and conversion wrapping;
- shifts, including variable and negative shifts;
- division and modulo, including panic cases;
- untyped constants and default types;
- `iota`;
- floating point, infinities, NaN, signed zero;
- complex numbers.

### Control Flow

- `if` with and without init statements;
- all `for` forms;
- `range` over arrays, slices, strings, maps, channels, integers, and functions
  as Go versions allow;
- `switch`, expressionless switch, type switch;
- `fallthrough`;
- `break`, `continue`, labels, and nested control flow;
- `goto` and its restrictions.

### Functions

- calls and returns;
- multiple return values;
- named results and naked returns;
- variadic functions and variadic forwarding;
- function values;
- closures and captured variables;
- recursive functions;
- deferred calls;
- panic/recover/unwind behavior.

### Pointers And Allocation

- `new`;
- address-of and dereference;
- nil pointer panics;
- pointer identity;
- pointer receivers;
- pointer-to-array indexing and slicing;
- escape-like aliasing patterns observable in source semantics.

### Structs And Methods

- struct literals;
- field get/set;
- embedded fields;
- promoted methods and fields;
- field shadowing;
- method values and method expressions;
- value versus pointer receivers;
- nil receiver calls;
- comparability.

### Arrays And Slices

- array value copying;
- array comparison;
- slice header copying;
- nil versus empty slices;
- slicing and full slicing;
- capacity and reslicing;
- append allocation and aliasing;
- copy overlap and min-length behavior;
- bounds panics;
- range-copy behavior.

### Maps

- nil map reads and write panics;
- map literals and make;
- lookup with and without comma-ok;
- delete, including nil map delete;
- assignment and aliasing;
- key comparability;
- map element non-addressability;
- iteration order as a nondeterministic future lane.

### Strings, Bytes, And Runes

- byte length versus rune count;
- string indexing as byte;
- slicing by byte;
- invalid UTF-8 preservation;
- conversions among string, `[]byte`, `[]rune`, byte, and rune;
- range over strings;
- concatenation and comparison.

### Interfaces

- nil interface versus typed nil value;
- dynamic type and dynamic value;
- type assertions, comma-ok and panic forms;
- type switches;
- interface equality and panic on uncomparable dynamic values;
- method sets;
- embedded method promotion;
- `error` as ordinary interface behavior.

### Generics

- generic functions;
- type inference;
- constraints, including `comparable`;
- zero value of a type parameter;
- instantiated function values;
- compile-negative generic methods;
- type sets and underlying type constraints.

### Packages And Initialization

- package-level variable initialization order;
- dependency-ordered init;
- multiple `init` functions;
- multi-file packages;
- imports and export visibility;
- blank identifiers.

### Concurrency

Default equality tests should include only deterministic concurrency cases.
Nondeterministic behavior needs a separate relation-style oracle before it can
enter the default lane.

Eventually cover:

- goroutine creation and termination;
- channel send/receive, buffered and unbuffered;
- close semantics;
- receive comma-ok;
- range over channels;
- nil channel blocking;
- select default and ready cases;
- panic/recover per goroutine;
- happens-before patterns once a concurrency semantics exists.

### Static Negative Behavior

Compile-negative coverage should include:

- unused locals and imports;
- invalid assignment and addressability;
- invalid comparisons;
- invalid conversions;
- impossible type assertions known statically;
- invalid `fallthrough`, `break`, `continue`, and `goto`;
- generic method declarations;
- duplicate declarations;
- import/export/package errors;
- syntax that parses but fails typechecking.

## Buildout Procedure

Use this loop:

1. Pick one feature area or one cluster of related semantic edges.
2. Check existing coverage with `scripts/coverage list --tag <tag>` and by
   browsing `Corpus/coverage/exec/<area>`.
3. Add tiny executable or compile-negative cases.
4. Add only necessary feature tags.
5. Run `scripts/coverage-manifest --list` and
   `scripts/coverage-negative-manifest --list`.
6. Run Go-side sanity with `GOLEAN_FRONTEND=none scripts/coverage run` when
   many executable cases were added. This validates that real Go execution and
   harness generation work while intentionally failing at `frontend-export`.
7. Run `scripts/coverage-negative` when negative cases were added.
8. Run a focused Gobra-backed subset only when useful. Do not require green
   results before keeping a valid new litmus case.
9. Run `git diff --check`.
10. Summarize new case count, negative case count, and any known harness issues.

Do not run a long full Gobra suite solely to decide whether newly added tests
are allowed. The point is to record the frontier.

## Iteration Stop Checklist

Before ending a buildout iteration, verify:

- `scripts/coverage-manifest --list` succeeds;
- `scripts/coverage-negative-manifest --list` succeeds;
- `GOLEAN_FRONTEND=none scripts/coverage run` succeeds as a harness run and
  fails only because the selected frontend is unsupported;
- `scripts/coverage-negative` passes if negative cases were changed;
- `git diff --check` passes;
- every new executable package has `main.go` and `cases.tsv`;
- every new negative package has `main.go` and `case.tsv`;
- every new tag is in `Corpus/coverage/tags.tsv`;
- no active executable case depends on handwritten `main`;
- no active executable case requires wall-clock time, randomness, scheduler
  behavior, filesystem state, network state, or external services;
- every `ok` case returns an observable value;
- every `panic` case uses a real Go panic substring.

If `GOLEAN_FRONTEND=none scripts/coverage run` reports `go-harness`,
`go-run`, `go-observation`, or `manifest` failures for new cases, fix those
before stopping. `frontend-export` failures are expected in that mode.

## Handoff Summary Format

When pausing, report:

```text
Executable cases: <count>
Negative cases: <count>
Validation:
- scripts/coverage-manifest --list: <result>
- scripts/coverage-negative-manifest --list: <result>
- GOLEAN_FRONTEND=none scripts/coverage run: <result>
- scripts/coverage-negative: <result or not run>
- git diff --check: <result>
Notable new areas:
- <area>
Known issues:
- <issue or none>
Commit status:
- <uncommitted | committed <hash>>
```

This keeps future agents from treating partial state as a clean baseline.

## Completion Criteria

The buildout is meaningfully complete when:

- every major Go language spec section has focused executable or negative
  coverage;
- every challenge item in `Corpus/challenges/semantic-edges/manifest.tsv` is
  either promoted, superseded by a stronger active case, or explicitly marked
  as requiring a future nondeterministic/stdlib/unsafe lane;
- real-world Go idioms from large projects have been sampled and reduced into
  litmus cases;
- version-specific Go features are tagged or documented with the relevant Go
  version policy;
- the suite contains broad red coverage for features not yet modeled, without
  skips or expected-unsupported annotations;
- reports can answer which feature areas are green, red at frontend export, red
  at lowering/checking, red at Lean execution, or red by differential mismatch;
- adding a new frontend does not require changing the corpus layout or Go
  source files.

Completion does not mean all cases pass. Passing is the semantics buildout's
job. This document governs the coverage buildout: make the map broad,
accurate, and hard to cheat.

## Current Near-Term Target

The immediate target is to grow from a small hand-built corpus into a broad
deterministic litmus suite. Start by promoting and reducing semantic-edge
challenge cases, then fill gaps from the Go spec and real-world idioms.

Prioritize:

- interfaces and method sets;
- defer, panic, and recover;
- constants, iota, and untyped values;
- map addressability and delete behavior;
- labels, fallthrough, and goto restrictions;
- package initialization;
- generics and static negative coverage;
- strings/runes/range behavior;
- deterministic channel basics only after the test oracle can express blocking
  and nondeterminism safely.
