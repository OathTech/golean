# Core Go Coverage Spike Plan

This document is a focused spike plan derived from
`docs/coverage-buildout-plan.md`. The original buildout plan remains the stable
policy for the long comprehensive corpus effort. This document narrows the next
coverage task to a shorter, achievable spike: bulk up the thin core-language
areas enough that implementation work on the Lean executable interpreter can
proceed with a credible, high-signal differential test base.

The goal is not complete Go conformance. The goal is a "nice core of Go"
coverage set: broad enough that common mistakes in a deterministic executable
interpreter for ordinary Go are likely to be exposed quickly.

## Starting Point

Current validated baseline at the start of this spike:

- executable cases: 633;
- compile-negative cases: 298;
- `GOLEAN_FRONTEND=none scripts/coverage run`: all executable cases reach
  `frontend-export`;
- `scripts/coverage-negative`: all negative cases pass;
- active branch: `phase-2-gocore-memory`.

The corpus is already strong enough to start building `golean`. This spike
exists to reduce the highest-risk blind spots before and during that
implementation, not to delay implementation until coverage is exhaustive.

## Non-Negotiable Rules

All rules from `docs/coverage-buildout-plan.md` still apply. In particular:

- add ordinary Go source only;
- never create Gobra-specific, Lean-specific, or frontend-specific variants;
- never weaken, skip, remove, or hide a valid red test;
- use compile-negative tests for invalid Go and executable tests for valid Go;
- keep nondeterministic, unsafe, and stdlib/runtime behavior out of the default
  deterministic equality lane unless a separate lane exists;
- fail closed on surprising manifest, Go harness, Go run, Go observation, or
  negative-compile behavior.

This document is a task plan, not the mutable accounting source. Update
`docs/coverage-ledger.md` as cases are added or deferred.

## Spike Outcome

The spike is successful when the high-risk core areas below either have
focused active litmus coverage or have an explicit ledger entry explaining the
required harness/design work.

Completion requires:

- each P0 area below has representative executable or compile-negative tests;
- any unimplemented harness capability has a clear design note in the ledger;
- a full validation gate passes;
- there is a short handoff/report stating what was covered, what remains thin,
  and whether implementation should proceed on focused subsets.

Do not measure success by raw case count. Case count is useful accounting, but
a small precise batch beats a large pile of redundant cases.

## P0 Spike Areas

These are the highest-impact gaps for a deterministic executable interpreter.
Work through them first.

### Go 1.26 `new(expr)`

Official Go 1.26 adds expression forms of `new`. Existing coverage mostly
exercises `new(T)`. Add focused cases for:

- typed value expression allocation and initialized value;
- untyped integer, boolean, string, rune, float, and complex defaulting where
  supported by the installed toolchain;
- expression evaluation exactly once before allocation;
- composite expression operands;
- generic expression operands;
- pointer identity between repeated `new(expr)` calls;
- static invalid forms such as `new(nil)` if rejected by the toolchain.

Tag with `new`, `pointers`, `conversions`, `typed`, `untyped`,
`evaluation_order`, `generics`, or other existing semantic tags as appropriate.
Document the Go 1.26 version dependency in the ledger.

### Comparison Short-Circuiting

Array and struct comparison order can hide or expose runtime panics when later
elements or fields contain interfaces with uncomparable dynamic values. Add
cases for:

- array comparison where an early unequal element prevents a later interface
  comparison panic;
- array comparison where equal early elements reach the later panic;
- struct comparison with the same early-field short-circuit behavior;
- nested array/struct variants only if they expose a distinct rule;
- compile-negative cases for statically uncomparable array/struct members if
  not already covered.

These tests should make comparison order observable without relying on
unspecified behavior.

### Generic `comparable` Runtime Edges

Go's `comparable` constraint admits some interface-typed values whose dynamic
comparison can still panic. Add small generic cases for:

- `Eq[T comparable]` instantiated with `any` values holding comparable dynamic
  values;
- the same generic function reaching a runtime panic for `any` holding a slice,
  map, or function;
- arrays or structs containing interface fields under a comparable generic
  function;
- negative cases for unconstrained comparison and invalid comparable
  assumptions if missing.

The point is to catch a semantics that treats `comparable` as "comparison can
never panic".

### Range Over Function

Existing range-over-function coverage is minimal. Add representative Go 1.23+
cases for:

- iterator functions yielding zero values;
- one-value and two-value iterator signatures;
- early `break` causing `yield` to return false;
- iterator respecting `yield` false;
- defer/panic interaction if deterministic and small;
- compile-negative invalid iterator signatures not already covered.

Avoid scheduler or timing behavior. Document the Go 1.23+ dependency.

### Higher-Order Generic Inference

Go 1.21 strengthened type inference, especially when generic functions are
passed as values. Add cases for:

- passing a generic function as an argument with inferred type arguments;
- assigning an instantiated or inferred generic function to a variable;
- returning a generic function value where legal;
- partial instantiation where legal;
- negative cases for ambiguous or impossible inference.

Keep each case tiny. If a case requires many declarations, split it.

### Recursive Generic Constraints

Go 1.26 supports recursive generic constraints. Existing coverage includes
recursive generic data types, which is not the same thing. Add cases for:

- F-bounded interface constraints such as a type whose method accepts the same
  constrained type;
- valid method calls through such constraints;
- invalid recursive constraints or method mismatches if the toolchain rejects
  them;
- interactions with comparable only if they remain readable.

Document the Go 1.26 dependency.

## P1 Spike Areas

Do these after the P0 areas, or interleave only when a P0 area requires the same
setup.

### Package-Aware Harness Design

Package/import semantics are the largest core-language hole, but they may need
harness support before they can be expressed honestly. Investigate enough to
decide whether the current spike can add package-aware executable tests.

Target behaviors:

- multi-file package initialization;
- package-level declaration order across files;
- import initialization order;
- exported and unexported selector behavior across packages;
- cross-package type identity and alias identity;
- method sets across package boundaries.

If current tooling cannot express this without cheating, do not force cases
into the active lane. Update the ledger with a precise harness limitation and
proposed directory/manifest shape.

### Pointer, Addressability, And Writeback Depth

Add cases only where they expose object identity, addressability, or writeback
behavior not already covered:

- selector and index expressions with pointer receivers;
- map value copies versus pointer/slice fields stored inside map values;
- addressability of composite literal results, call results, conversion
  results, and embedded fields;
- aliasing through pointer-to-array and slice headers.

Avoid near-duplicates of existing selector/addressability cases.

### Composite Literal Matrix

Add focused typed/untyped and nested literal interactions:

- keyed and positional struct literal conversion edges;
- sparse arrays with typed constants;
- nested map/slice/struct literals where evaluation order or type identity is
  observable;
- invalid mixed-key or duplicate-key forms not already covered.

### Architecture-Sized Integer Policy

Before adding many `int`, `uint`, or `uintptr` cases, write down the intended
policy for host-width sensitivity. Then add only portable cases or clearly
documented installed-toolchain cases.

## Explicit Non-Goals For This Spike

Do not spend this spike on:

- nondeterministic goroutine scheduling;
- map iteration order;
- select fairness among multiple ready cases;
- race behavior;
- unsafe pointer/layout/alignment;
- broad standard-library behavior;
- raw generated programs;
- making the Lean semantics pass the corpus.

These are real future areas, but they require separate lanes or design work.

## Iteration Shape

Work in small coherent batches:

- one P0/P1 family per batch;
- roughly 6-20 executable cases per batch;
- roughly 2-8 compile-negative cases per batch;
- one local commit per coherent validated batch;
- no remote push unless explicitly requested.

Before adding cases:

```sh
scripts/coverage list --tag <relevant-tag>
find Corpus/coverage/exec/<area> -maxdepth 3 -type f | sort
find Corpus/coverage/negative/compile/<area> -maxdepth 3 -type f | sort
```

When possible, use a prefix run for quick feedback on the new cases:

```sh
GOLEAN_FRONTEND=none scripts/coverage run --prefix <area>/<case>
```

Then run the full gate before committing.

## Required Validation Gate

Before any pause, handoff, or commit, run:

```sh
scripts/coverage-manifest --list
scripts/coverage-negative-manifest --list
GOLEAN_FRONTEND=none scripts/coverage run
scripts/coverage-negative
git diff --check
git diff -- docs/coverage-buildout-plan.md
```

Acceptable `GOLEAN_FRONTEND=none` result:

- every executable case is discovered;
- every executable case reaches `frontend-export`;
- no case fails at `manifest`, `go-harness`, `go-run`, `go-observation`, or any
  other pre-frontend stage.

Negative coverage must pass. If it does not, fix the corpus or metadata before
continuing.

## Iteration Speed Work

The corpus is large enough that full reruns slow the implementation loop. This
spike may include harness ergonomics work if it directly helps keep coverage
usable.

High-impact improvements:

- a curated smoke suite containing high-signal representatives from core
  semantic areas;
- a command that runs changed coverage packages since a base commit;
- cached Go observations for unchanged cases, with fail-closed invalidation;
- clearer reporting that distinguishes full runs from filtered runs;
- CI/release gates that require full-run metadata, not a filtered `latest.tsv`.

Do not let speed work weaken validation. Faster feedback is good only if gaps
remain visible.

## Handoff Format

At the end of a spike iteration, report:

```text
Spike batch: <area>
Executable cases: <count>
Negative cases: <count>
Validation:
- scripts/coverage-manifest --list: <result>
- scripts/coverage-negative-manifest --list: <result>
- GOLEAN_FRONTEND=none scripts/coverage run: <result>
- scripts/coverage-negative: <result>
- git diff --check: <result>
- docs/coverage-buildout-plan.md unchanged: <yes/no>
New active coverage:
- <families>
Still thin:
- <families>
Harness issues:
- <issues or none>
Commit status:
- <uncommitted | committed <hash>>
```

## Spike Completion Criteria

The spike can stop when:

- all P0 areas have active representative coverage or precise ledger/design
  notes;
- at least one P1 decision has been made for package-aware harness support;
- the coverage ledger accurately reflects the new state;
- the default fail-closed control lane still works;
- a concise final spike summary can say what implementation mistakes the suite
  is now likely to catch, and what remains outside the current oracle.

At that point, proceed with `golean` implementation using focused subsets and a
small smoke suite, while continuing to grow coverage opportunistically.
