# Architecture Audit

Date: 2026-06-28

This audit checks whether the current architecture can grow from the Gobra-backed
prototype into an independent, full-featured, highly accurate Go semantics in
Lean.

## Verdict

The project is directionally sound.

The central decisions still look right:

- GoCore, not Gobra, is the semantic center.
- The executable interpreter is valuable and should stay first-class for
  differential testing.
- A future proof-facing semantics should be relational and use the same syntax,
  values, locations, errors, and outcomes.
- The heap model with path-like `Loc.field` and `Loc.index` locations is the
  right foundation for structs, arrays, slices, and later Iris-style ownership.
- The active workflow, "add feature, add paired Go/Gobra fixture, compare Go
  execution against Lean execution", is exposing real mistakes early.

The biggest risks are scale and semantic precision, not the top-level design.
The next phase should make those risks explicit before adding interfaces,
numeric widths, methods, packages, or concurrency.

## Non-Negotiable Invariants

These should be preserved as the codebase grows.

- GoCore models Go runtime behavior, not Gobra verification behavior.
- Gobra assertions, preconditions, postconditions, predicates, invariants, and
  ghost constructs are frontend wire data only.
- Unsupported Go features fail closed as `unsupported`; malformed GoCore states
  fail as `stuck`; Go runtime traps fail as `panic`.
- Every semantic feature needs differential coverage unless it is purely
  internal refactoring.
- The executable interpreter may pick deterministic policies for testing, but
  the future relational semantics must leave room for Go-permitted
  implementation variation.
- Syntax, values, locations, errors, and outcomes must remain reusable by both
  the interpreter and the future relation.

## What Is Healthy

### Semantic Boundary

The `GobraJson -> GobraToIR -> GoCore` split is working. Gobra-specific
desugarings, proof artifacts, bodyless declarations, and frontend gaps are
handled before GoCore. GoCore has not become a Gobra verifier IR.

This is essential for replacing Gobra later with a native Go frontend.

### Memory Shape

Heap-backed locals and path locations are the right choice:

```lean
Loc.base Addr
Loc.field Loc typeName fieldName
Loc.index Loc index
```

This is compatible with Goose/Perennial's struct and slice proof story. It also
keeps future Iris predicates natural: field and index ownership can be stated
over path-like locations rather than over ad hoc generated addresses.

### Differential Loop

The current paired corpus is already useful. It found the slice reslicing
capacity bug and the string byte-length bug before those choices hardened into
assumptions. That is exactly the intended role of the testing loop.

### Fail-Closed JSON

The strict Gobra JSON decoder and negative tests are doing the right thing.
Schema drift or unknown tags should remain loud failures.

## Primary Risks

### 1. GoCore Is Too Monolithic

Before the first hardening refactor, `GoLean/IR.lean` contained:

- syntax;
- type definitions;
- values and state aliases;
- heap/local operations;
- default-value construction;
- equality/comparison;
- expression evaluation;
- statement execution;
- function entry points.

This is acceptable for the prototype, but it will not scale to full Go. Adding
interfaces, methods, packages, typed integers, strings, channels, and relational
rules into one file would make semantic review harder and increase accidental
coupling.

The first mechanical split is now in place:

- `GoLean/GoCore/Syntax.lean`: `Ty`, `Expr`, `Assignee`, `Stmt`, `Func`,
  `Program`.
- `GoLean/GoCore/Value.lean`: concrete `GoError`, `Loc`, `SliceValue`,
  `MapValue`, and `GoValue` definitions. `GoLean/Runtime.lean` remains only as
  a compatibility import.
- `GoLean/GoCore/State.lean`: `ExecState`, locals, heap operations, allocation.
- `GoLean/GoCore/Ops.lean`: default values, equality, comparison, indexing,
  slicing, map helpers.
- `GoLean/GoCore/Eval.lean`: executable expression/statement/function
  evaluation.
- `GoLean/IR.lean`: compatibility import during the transition.

The remaining risk is not file size alone; it is semantic coupling inside the
new modules. Expression evaluation now returns an updated state, equality is
type-directed for the current value forms, and integers now carry kind
information for the first fixed-width subset. Values still need interface
structure.

### 2. Expression Evaluation Will Need Effects

`evalExpr` now returns both a value and the updated state:

```lean
evalExpr : ExecState -> Expr -> Except GoError (GoValue × ExecState)
```

Assignee evaluation has the same shape for locations. This keeps the current
interpreter ready for Go expressions that can mutate state, including
calls-in-expressions, receives, conversions with panics, allocation-like
builtins, append, map operations, and eventually interface/method dispatch.

The checkpoint preserves the current Go assignment discipline: evaluate lvalues
and rvalues before committing stores. Existing regression tests cover multiple
assignment, call-assignment targets, map lookup, append, and bounds panics.

### 3. Integer Semantics Are Under-Specified

GoCore now has an integer-kind descriptor on `Ty.int` and `GoValue.int`. The
executable interpreter normalizes fixed-width integer values on typed stores
and integer arithmetic. A first integer-to-integer conversion slice is also in
place, as are first shift and bitwise slices. Strings are now byte-backed,
with exact literal bytes from Gobra JSON and first string/`[]byte` conversion
coverage. The current executable policy treats `int` and `uint` as 64-bit,
matching the local Go differential harness; the Gobra fork can still expose
narrower `int` metadata in some conversion nodes, so architecture policy must
remain explicit rather than implicit.

This is the first slice, not the whole integer story. Full Go still needs:

- signed and unsigned integer families;
- `byte`/`uint8` and `rune`/`int32`;
- broader conversion families, including rune conversions;
- more bitwise/shift edge cases;
- overflow behavior for fixed-width values;
- an architecture-dependent `int`/`uint` width policy in the future relation.

This cannot be postponed too long because strings, bytes, arrays, indexes,
maps, and constants all touch numeric typing.

Current model:

- keep mathematical constants separate from runtime integer values;
- carry an integer-kind descriptor in `Ty` and integer runtime values;
- store runtime integer values normalized to their kind where typed context is
  available;
- make operations type-directed and fail closed when kind information is
  missing.

### 4. Equality Is Now Type-Directed For Current Values

`valueEq` now carries static GoCore type information:

```lean
valueEq : ExecState -> Ty -> GoValue -> GoValue -> Except GoError Bool
```

Map key lookup uses the same typed equality path. This removes the old raw
value-shape equality path for scalars, pointers, arrays, structs, slices, maps,
aliases, and named structs.

Remaining work: full Go equality still needs interfaces, function values, and
exact dynamic comparability panics once those value forms are introduced.

### 5. Type Information Is Too Thin

The current type environment is enough for structs and aliases, but full Go
needs package-qualified type identities, named/underlying type distinctions,
method sets, embedded fields, export visibility, type parameters, and interface
type sets.

Recommended next step:

- introduce stable type identities independent of frontend-generated strings;
- keep source/frontend names as metadata, not semantic identity;
- make lowering responsible for mapping Gobra names into GoCore identities.

### 6. Gobra Lowering Still Contains Heuristics

The type-definition recovery in `GobraToIR` is intentionally pragmatic. It is
not a long-term schema. The multi-assignment reconstruction is also tied to a
known Gobra desugaring pattern.

These are acceptable while Gobra is a temporary frontend, but they must remain
quarantined. They should not influence GoCore syntax.

Required direction:

- enrich the Gobra fork where needed so the wire format exposes explicit Go
  constructs;
- add lowering tests whenever a Gobra desugaring is reconstructed;
- record frontend gaps separately from semantic gaps.

### 7. Relational Semantics Is Still Only a Design Constraint

The docs correctly require a future relation, but no relation exists yet. That
is fine at this stage, but we should avoid making the interpreter harder to
relate later.

Required direction:

- after one more feature family, add a small relational skeleton for the current
  deterministic subset;
- start with statements and heap operations, not the whole language;
- prove or at least test-check a few interpreter/relation correspondence lemmas
  for straight-line scalar and heap programs.

This should happen before concurrency, because Iris integration will be much
harder if the relation is retrofitted after channels/goroutines.

## Harness Risks

### Cold Gobra Export Cost

Caching helps, but cold runs still invoke SBT/Gobra per fixture. That will not
scale to thousands of deterministic cases or random generation.

Recommended path:

- keep using `scripts/diff-one` for the tight local loop;
- add feature filtering in the manifest once feature families grow;
- eventually batch Gobra export or bypass Gobra with a native Go frontend.

### Paired Source Drift

The Gobra fixture and plain Go fixture are separate files. This is tolerable
now, but long-term conformance should avoid drift.

Recommended path:

- when possible, generate both from a single source template;
- or move toward a native Go frontend so the same Go source drives both real Go
  execution and GoCore lowering.

### Generator Readiness

Do not integrate random generators until unsupported classification is more
structured. Otherwise generator failures will be noisy rather than useful.

Minimum prerequisites:

- typed integer policy for generator-visible integer families beyond the first
  fixed-width slice;
- richer string/byte support;
- function/method call expression support;
- manifest feature filters;
- fast targeted run tooling.

## Immediate Refactor Plan

1. Done: split GoCore modules mechanically before adding interfaces or typed
   integers.
2. Done: convert expression evaluation to state-returning form before adding
   calls-in-expressions, channel receives, or effectful builtins.
3. In progress: introduce typed integer kinds and byte/rune values before
   string operations and numeric conversions. The first fixed-width integer
   slice is implemented, as are integer-to-integer conversion, shift, bitwise,
   string byte-indexing/slicing, and string/`[]byte` conversion support; rune
   operations remain.
4. Done: make equality type-directed for the current value forms before
   interfaces and exact comparability tests.
5. Replace Gobra type-definition recovery heuristics with explicit fork output
   when the next struct/named-type feature requires it.
6. Add a relational semantics skeleton before concurrency or Iris-facing proof
   rules.

## Next Feature Recommendation

Do not add interfaces or concurrency next.

The best next semantic family is typed integers plus byte/string operations:

- it is small enough to differentially test thoroughly;
- it unblocks string slicing and rune-level operations;
- it forces the runtime value representation to become more precise;
- it is a prerequisite for broader conversions, arrays, maps, and constants.

This is also a good forcing function for the GoCore module split, because typed
integers touch syntax, values, operations, lowering, tests, and docs.
