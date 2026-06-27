# Roadmap

This project aims to build an Aeneas-like Go-to-Lean tool with broad Gobra/Go
coverage, executable semantics, and proof infrastructure in Lean.

The current architectural commitment is:

```text
Go/Gobra source
  -> Gobra frontend/export
  -> strict Gobra JSON wire AST
  -> GobraToIR lowering
  -> GoCore deep embedding
  -> Lean execution and proof infrastructure
```

Gobra is a frontend and source of typed artifacts. GoCore is the semantic
center.

## Strategy

- Differential testing is a first-class design constraint, not a later add-on.
- The Lean-side executable semantics should be small, explicit, and fail-closed
  on unsupported or surprising inputs.
- GoCore should model Go behavior, not Gobra's internal IR.
- New Goose/Perennial is the main reference for Go memory and proof structure:
  path-like field locations, typed points-to predicates, generated field access
  lemmas, and WP automation.
- Aeneas remains useful as a Lean-facing reference, but Go needs a heap model
  because addressability, pointers, structs, slices, maps, interfaces, and
  concurrency are central to ordinary Go.
- The proof layer should be generated on top of GoCore, potentially using
  Iris-Lean or Lean-native WP infrastructure, rather than making Gobra IR a
  first-class verification target.

## Phase 1: Strict Frontend Export

Goal: make Gobra JSON a reliable, narrow wire protocol.

Status: underway.

Deliverables:

- Maintain `third_party/gobra` as the `septract/gobra-json` fork.
- Keep `--printInternalJson` strict and restrictive.
- Treat Lean's wire ADT as the schema authority.
- Reject missing fields, extra fields, unknown tags, wrong scalar types, and
  unsupported nested nodes.
- Expand the smoke corpus and negative JSON tests.

Success criterion:

`scripts/gobra-smoke` exports, validates, and runs the current Gobra smoke
corpus without accepting unexpected JSON shapes.

## Phase 2: Executable GoCore Memory

Goal: make GoCore execute ordinary pointer/struct Go programs.

Status: in progress. Heap-backed locals, path-like field locations, struct
values, direct calls, and the `examples/swap` smoke execution path are now
implemented for the current supported subset.

Deliverables:

- Replace stable variable references with heap-backed local variables.
- Add `Loc.base` and `Loc.field` path-like locations.
- Add typed load/store/address-of/deref operations.
- Add `Value.struct` and a type environment for defined struct types.
- Add struct literals, field value projection, and field address projection.
- Add direct function calls with fresh call frames and left-to-right argument
  evaluation.
- Lower Gobra field, deref, address-of, struct literal, and call nodes into
  GoCore.

Success criterion:

The `examples/swap` style program lowers from Gobra JSON and executes in Lean
far enough to reach the expected final assertion failure for the right reason.

## Phase 3: Differential Testing Harness

Goal: compare Go execution and Lean GoCore execution over many small programs.

Status: partially started. Lean execution now emits classified observations for
successful returns, assertion failures, unsupported features, and stuck states.

Deliverables:

- Define a stable observation format:

```text
status : ok | panic | assertion_error | unsupported | stuck
returns : Array Value
message : Option String
```

- Add a Go-source harness that runs concrete test programs with selected inputs.
- Compare Go results against Lean GoCore observations.
- Keep `unsupported` acceptable only when the test manifest explicitly expects
  it.
- Add shrinking/minimization hooks once failures become common enough to need
  them.

Success criterion:

Each newly supported GoCore feature lands with tests that compare source Go
execution against generated Lean execution where the feature is executable.

## Phase 4: Coverage Expansion

Goal: cover as much Go/Gobra code as practical.

Feature order should be driven by corpus failures and semantic dependencies,
but the expected progression is:

- integer and boolean operators with Go-sized words;
- arrays and slices, including indexing, slicing, append, len, and cap;
- maps, including nil-map behavior and comma-ok lookup;
- named types, aliases, conversions, and zero values;
- methods and interfaces;
- panics/defer/recover where needed by real code;
- goroutines, channels, atomics, and selected sync primitives.

New Goose gives useful decomposition here: desugar simple constructs during
lowering, encode ordinary sequencing/calls in GoCore, and add semantic
primitives only for genuinely Go-specific behavior.

Success criterion:

Unsupported-feature results are tracked by corpus category, and the unsupported
surface decreases as the corpus grows.

## Phase 5: Proof Layer

Goal: generate Lean proof infrastructure over GoCore.

Deliverables:

- Generate per-type Lean definitions for struct values and field access.
- Generate typed points-to predicates for structs as field-wise ownership.
- Generate field load/store/access lemmas matching the GoCore `Loc.field`
  model.
- Define a WP or VCG layer over GoCore execution.
- Evaluate Iris-Lean for separation logic and concurrency-heavy proofs.
- Keep executable GoCore semantics and proof semantics connected by the same
  core syntax and memory model.

Success criterion:

Simple pointer/struct programs have both executable tests and generated proof
support, with manual proof effort focused on specifications rather than field
plumbing.

## Phase 6: Lean Output Surface

Goal: produce useful Lean artifacts for users.

Deliverables:

- Emit readable GoCore programs.
- Emit generated type/proof support files.
- Emit test harnesses for concrete differential checks.
- Provide clear unsupported-feature reports with source locations.

Success criterion:

A user can run the tool on a Gobra-supported Go package, inspect the generated
Lean, execute supported concrete tests, and start proofs against generated
specification hooks.

## Near-Term Work Queue

1. Add Go-source-vs-Lean differential execution for plain Go targets.
2. Expand expression/operator coverage beyond the current integer/bool subset.
3. Add arrays and slices using the same path-location model.
4. Start generating struct field proof support modeled after new Goose.
5. Prototype the first WP/VCG layer over GoCore.
