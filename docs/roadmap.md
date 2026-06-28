# Roadmap

This project aims to build an Aeneas-like Go-to-Lean tool with broad Go
coverage and executable semantics in Lean. Gobra is a temporary frontend
accelerator, not the intended semantic core or long-term frontend. Proof
infrastructure remains an important later phase, but the current priority is to
build and differentially test a substantial Go semantics first.

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
center. Longer term, we expect to replace Gobra with our own frontend as
coverage demands outgrow Gobra's exported shape.

## Strategy

- Differential testing is a first-class design constraint, not a later add-on.
- The Lean-side executable semantics should be small, explicit, and fail-closed
  on unsupported or surprising inputs.
- The proof-facing semantics should be relational, with the executable
  interpreter treated as a differential-testing implementation of that relation
  for supported concrete runs.
- GoCore should model Go behavior, not Gobra's internal IR.
- Gobra-specific assertions, specifications, predicates, invariants, and ghost
  artifacts are not GoCore runtime semantics. They are decoded only as strict
  wire data and erased or rejected at the frontend boundary.
- Old and new Goose/Perennial are the main semantic references as GoCore
  expands. New Goose's path-like field locations are especially important for
  memory, structs, arrays, slices, and later proof support.
- Aeneas remains useful as a Lean-facing reference, but Go needs a heap model
  because addressability, pointers, structs, slices, maps, interfaces, and
  concurrency are central to ordinary Go.
- The proof layer should come after GoCore has meaningful semantic coverage.
  When it arrives, it should be generated on top of GoCore rather than making
  Gobra IR a first-class verification target.
- Iris-Lean compatibility is a design constraint on the semantics shape:
  syntax, values, locations, errors, and outcomes should be reusable by both the
  executable interpreter and a future relational small-step or big-step
  semantics.
- Slice semantics should use a descriptor over backing locations, not copied
  vectors. This follows the Goose/Perennial shape and leaves room for
  `own_slice`/`own_slice_cap` predicates in Iris-Lean.
- Where Go leaves implementation latitude, keep the relation broader than the
  executable interpreter and use differential testing on real programs to
  decide which deterministic policies matter for the test runner.

## Hardening Gate

The adversarial audit changed the near-term order of work. Before expanding
substantially into slices, maps, interfaces, and generators, the project needs a
hardening pass that makes mistakes visible instead of easy to hide.

Required fixes:

- Thread structured `GoError` values through GoCore and the CLI. Error status
  must be data, not inferred from string prefixes.
- Model Go runtime traps such as nil dereference, divide by zero, and
  out-of-bounds indexing as `panic`. Reserve `stuck` for internal semantic gaps
  where Go behavior is not yet modeled.
- Replace raw `GoValue` equality with type-directed comparable equality.
- Decide the integer story explicitly: model Go-sized signed/unsigned behavior
  for supported integer types, or reject programs whose behavior depends on
  widths not yet represented.
- Replace statement execution's plain state return with an explicit
  `ExecOutcome` covering normal completion, return, break, and continue, with
  typed errors representing panic, unsupported, stuck, and internal failures.
- Make expression evaluation capable of effectful Go expressions such as calls,
  allocation, append, map operations, and channel operations before those
  features are added.
- Evaluate assignment lvalues and rvalues before committing stores, including
  multiple assignment and call assignment.
- Bounds-check indexed lvalues when the location is evaluated, including
  address-of-index forms.
- Make Gobra lowering fail closed: unsupported nodes, bodyless declarations,
  malformed lvalues, and surprising type-definition shapes should produce
  explicit failures.
- Harden differential testing with source/hash linkage, per-run artifacts,
  timeouts, structured observation comparison, and manifest-level reasons for
  any expected `unsupported` or `stuck` result.

## Phase 1: Strict Frontend Export

Goal: make Gobra JSON a reliable, narrow wire protocol.

Status: underway.

Deliverables:

- Maintain `third_party/gobra` as the `septract/gobra-json` fork.
- Keep `--printInternalJson` strict and restrictive, while allowing the fork to
  add plain-Go frontend nodes where Gobra's verifier-specific builtins would
  otherwise reject valid Go.
- Treat Lean's wire ADT as the schema authority.
- Reject missing fields, extra fields, unknown tags, wrong scalar types, and
  unsupported nested nodes.
- Keep Gobra verification-only constructs out of GoCore. The importer may
  decode spec fields fail-closed because Gobra emits them, but lowering must
  not make them executable Go behavior.
- Expand the smoke corpus and negative JSON tests.

Success criterion:

`scripts/gobra-smoke` exports, validates, and runs the current Gobra smoke
corpus without accepting unexpected JSON shapes. Manifest rows are executed
generically, so adding a new differential case should not require editing the
smoke script.

## Phase 2: Executable GoCore Memory

Goal: make GoCore execute ordinary pointer/struct Go programs.

Status: in progress. Heap-backed locals, path-like field locations, struct
values, direct calls, explicit `if`/`return`, unlabeled `break`/`continue`, and
the `examples/swap` smoke execution path are now implemented for the current
supported subset.

Deliverables:

- Replace stable variable references with heap-backed local variables.
- Add `Loc.base` and `Loc.field` path-like locations.
- Add typed load/store/address-of/deref operations.
- Add `Value.struct` and a type environment for defined struct types.
- Add struct literals, field value projection, and field address projection.
- Add direct function calls with fresh call frames and left-to-right argument
  evaluation.
- Add control-flow outcomes for explicit return, unlabeled break, and unlabeled
  continue.
- Lower Gobra field, deref, address-of, struct literal, and call nodes into
  GoCore.
- Lower Gobra `If`, `Return`, `Break`, and `Continue` nodes into GoCore where
  they have direct GoCore meaning. Labeled break/continue remains unsupported.

Success criterion:

The `examples/swap` style program lowers from Gobra JSON and executes in Lean as
ordinary Go after Gobra assertions/specifications are erased.

## Phase 3: Differential Testing Harness

Goal: compare Go execution and Lean GoCore execution over many small programs.

Status: partially started. Lean execution now emits classified observations for
successful returns, Go panics, unsupported features, and stuck states. The first
smoke harness compares plain Go fixtures against the corresponding Lean GoCore
observations.

Deliverables:

- Define a stable observation format:

```text
status : ok | panic | unsupported | stuck | error
returns : Array Value
message : Option String
```

- Add a Go-source harness that runs concrete test programs with selected inputs.
- Compare Go results against Lean GoCore observations.
- Drive paired differential cases from a manifest with explicit feature tags,
  expected status, argument values, and reasons for expected semantic gaps.
- Keep `unsupported` acceptable only when the test manifest explicitly expects
  it.
- Require manifest reasons for expected `unsupported` and `stuck` results.
- Parse and compare observations structurally on both sides.
- Regenerate or reject stale Gobra JSON using source hashes.
- Run Gobra, Go, and Lean stages with timeouts or fuel where applicable.
- Isolate artifact directories per run to avoid races between smoke scripts.
- Add shrinking/minimization hooks once failures become common enough to need
  them.

Success criterion:

Each newly supported GoCore feature lands with tests that compare source Go
execution against generated Lean execution where the feature is executable.

## Phase 4: Coverage Expansion

Goal: cover as much Go/Gobra code as practical.

Status: started, but gated by the hardening pass above. The executable subset
now includes scalar arithmetic and
comparisons, boolean connectives, divide-by-zero panic classification, and a
first fixed-size array subset: array types, array literals, indexing, indexed
assignment, and array equality through GoCore values. The control-flow subset
now includes `if`, explicit `return`, and unlabeled `break`/`continue`.
Fixed-size array `len` and `cap` are supported for array values.
Zero-value arrays, nested arrays, arrays through function parameters and
results, pointer-to-array indexing/assignment, array-to-slice aliasing,
nonzero-capacity and zero-length slice `make`, slice literals, typed nil slice
behavior, overlapping slice `copy`, and slice `append` aliasing/growth are
covered by differential smoke tests.

Feature order should be driven by corpus failures and semantic dependencies,
but the expected progression is:

- integer and boolean operators with Go-sized words;
- arrays and slices, including indexing, slicing, append, len, and cap. Slices
  should follow `docs/slice-model.md`: descriptor values over backing
  locations, with append growth treated carefully because post-growth capacity
  is observable but not fully specified by Go;
- maps, including nil-map behavior and comma-ok lookup;
- named types, aliases, conversions, and zero values;
- methods and interfaces;
- panics/defer/recover where needed by real code;
- goroutines, channels, atomics, and selected sync primitives.

New Goose gives useful decomposition here: desugar simple constructs during
lowering, encode ordinary sequencing/calls in GoCore, and add semantic
primitives only for genuinely Go-specific behavior.

Random Go generators enter after deterministic coverage has enough structure to
triage failures. The two concrete candidates are:

- Microsmith (`ALTree/microsmith`), as the newer Go AST/typechecker-backed
  generator;
- GoSmith (`dvyukov/gosmith`), as the older Csmith-like legal Go program
  generator.

Both should run behind the same feature tagging/filtering used by the
deterministic corpus. Arbitrary generated programs are expected to outrun
GoCore for a while, so the harness must classify unsupported features clearly
instead of treating every generator miss as an equivalence failure.

Success criterion:

Unsupported-feature results are tracked by corpus category, and the unsupported
surface decreases as the corpus grows.

## Phase 5: Proof Layer

Goal: generate Lean proof infrastructure over GoCore.

Status: deferred until GoCore has substantial semantic coverage and a working
differential-testing loop.

Deliverables:

- Generate per-type Lean definitions for struct values and field access.
- Generate typed points-to predicates for structs as field-wise ownership.
- Generate field load/store/access lemmas matching the GoCore `Loc.field`
  model.
- Define a WP or VCG layer over GoCore execution.
- Evaluate Iris-Lean for separation logic and concurrency-heavy proofs.
- Keep executable GoCore semantics and proof semantics connected by the same
  core syntax and memory model.
- Define a relational GoCore semantics suitable for Iris-Lean integration, then
  connect the executable interpreter to it for the supported deterministic
  subset.

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

A user can run the tool on a Go package accepted by the current frontend,
inspect the generated Lean, execute supported concrete tests, and start proofs
against GoCore-level specification hooks.

## Near-Term Work Queue

1. Complete the architecture hardening gate from
   `docs/architecture-audit.md`: split GoCore modules, make expression
   evaluation state-returning, make equality type-directed, and add a small
   relational semantics skeleton.
2. Keep expanding deterministic differential coverage, but prefer cases that
   force representation decisions we need anyway: typed integers, bytes,
   strings, conversions, and comparability.
3. Continue slices using the descriptor/backing-location model in
   `docs/slice-model.md`, especially string slicing, zero-capacity edge cases,
   and append growth policy refinement.
4. Track frontend gaps separately from semantic gaps. Gobra-fronted failures
   such as `delete` should pressure the Gobra fork or a future native frontend,
   not distort GoCore.
5. Add maps and named-type/conversion behavior driven by corpus failures.
6. Integrate Microsmith/GoSmith only after scalar, pointer, struct, array, and
   slice cases have deterministic coverage, typed integer policy, and feature
   filters.
7. Keep checking old/new Goose before adding each larger semantic feature.
