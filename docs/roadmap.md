# Roadmap

> **STALE — pending refresh (flagged 2026-07-19 by the pre-merge audit, D4-13).**
> This doc predates two major shifts and is partly out of date: **(1) Gobra has
> been dropped** — the native Go frontend (`tools/nativefrontend` +
> `NativeToIR.lean`) is the sole frontend, so all "Gobra frontend / Gobra export
> path / critical-path risk" framing below is obsolete. **(2) The Iris proof
> layer is underway** (in-repo `proofs/`), no longer just "a later phase." Read
> the body as historical context; current state of record lives in `TODO.md`,
> `CLAUDE.md`, and the dated design notes. Full rewrite tracked as a task.
> **(3) Coverage claims (2026-08-19):** language coverage is measured
> against the pinned spec in `docs/language-coverage-ledger.md`; every
> coverage statement in the body below is superseded by that ledger.

This project aims to build an Aeneas-like Go-to-Lean tool with broad Go
coverage and executable semantics in Lean. Proof infrastructure (the Iris layer)
is now an active track alongside broadening the differentially-tested semantics.

## North Star Target

Decided 2026-07-17: the long-range target program is `etcd-io/raft`, the Raft
consensus library extracted from etcd. It is real production Go with
well-studied correctness properties (election safety, log matching, leader
completeness), and its core below `RawNode` is a deterministic single-threaded
state machine: goroutines and channels live only in the `node.go` wrapper, so
the verification-relevant core fits the deterministic differential oracle and
keeps concurrency deferred, as already planned.

What the target forces, roughly in order:

- A native Go frontend. etcd raft is multi-package, uses modern Go, and
  includes generated protobuf structs; the Gobra export path will not scale to
  it. Multi-package support and the single-file harness limitation are on the
  critical path.
- A stdlib extern/model policy. The core needs at least `fmt`-style formatting
  stubs (Logger is injectable), `errors` values, and `sort` including
  `sort.Slice` with closures. `math/rand` is injectable.
- Order-insensitive map-iteration observations. Vote counting and committed
  index calculation fold over `map[uint64]`-keyed state; results are
  order-insensitive, but the oracle needs the planned nondet/relational lane or
  normalized observations.
- A concrete proof-layer goal: state raft's safety invariants over GoCore and
  prove them for the translated core, giving Phase 5/6 a real benchmark.

Suggested climbing ladder, each stage a differential milestone:

1. `quorum` package: pure map/slice vote math, few hundred lines. First
   multi-package and native-frontend pilot.
2. `tracker` package: Progress/Inflights structs, slices, invariants.
3. `log_unstable.go` plus `MemoryStorage`: a slice-aliasing stress test for
   the descriptor model.
4. `raft.go` step function driven by `raftpb.Message` values, replaying
   etcd's own datadriven interaction test traces as the differential oracle.
5. `RawNode` end to end. `node.go` and channels wait for the concurrency
   phase.
6. Eventually: the concurrent `node.go` layer, once GoCore has a small-step
   relational semantics compatible with Iris-Lean's `PrimStep` interface
   (forked goroutines are the `List Expr` component of the step relation) and
   Iris-Lean integration is toolchain-feasible. Concurrency reasoning is
   expected to come from Iris-Lean, following the Goose/Perennial precedent
   for verified Go distributed systems.

The north star does not change near-term ordering: the semantics cleanup in
`docs/archive/semantics-cleanup-plan.md` comes first, because string-based identity
and frontend-artifact debt would be fatal at raft scale.

The current architectural commitment is:

```text
Go source
  -> selected frontend adapter
  -> strict frontend wire artifact
  -> frontend-to-GoCore lowering
  -> GoCore deep embedding
  -> Lean execution and proof infrastructure
```

Gobra is a frontend and source of typed artifacts. GoCore is the semantic
center. Longer term, we expect to replace Gobra with our own frontend as
coverage demands outgrow Gobra's exported shape. The differential corpus is
therefore source-level Go plus metadata; frontend artifact paths and frontend
quirks must stay inside adapters.

## Strategy

- Differential testing is a first-class design constraint, not a later add-on.
- The Lean-side executable semantics should be small, explicit, and fail-closed
  on unsupported or surprising inputs.
- The executable interpreter is the semantic authority and the statement
  language: headline theorems are stated over `execStmt`/`stepFn` alone
  (termination, safety, and pre/post all interpreter-level). The Prop-level
  relation exists for Iris's sake, is proven equivalent to the executable
  step, and never appears in statements (sem-adequacy arc, 2026-08-03 —
  this inverts the earlier framing of this bullet).
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
- Where Go leaves implementation latitude, model it as explicit
  nondeterminism in the interpreter's `Choices` stream (map iteration order
  today; scheduler interleaving when concurrency lands) — statements
  ∀-quantify the stream, the relation tracks the interpreter exactly, and
  differential testing decides which resolved policies the oracle can
  observe. (Reframed 2026-08-03; the old bullet kept the relation broader
  than the interpreter, which the two-sided correspondence now forbids.)

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
- Continue making the integer story explicit. The first executable slice models
  fixed-width integer normalization and uses a 64-bit `int`/`uint` policy for
  differential testing. A first integer-to-integer conversion slice is in
  place, as are first shift and bitwise slices; constants, broader conversions,
  and the future architecture-parametric relation remain open.
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
- Harden differential testing with source/hash linkage, generated Go harnesses,
  per-run artifacts, timeouts, structured observation comparison, and metadata
  that cannot turn Lean `unsupported` or `stuck` outcomes into passing cases.
- Keep the coverage corpus and normalized manifests frontend-independent. Gobra
  may be the current adapter, but switching to a Go AST frontend or a later
  custom frontend must not require changing litmus inputs or Go observations.

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
- Expand `Corpus/coverage` and negative JSON tests.

Success criterion:

`scripts/coverage` reports every active canonical Go litmus case and every
compile-negative case without accepting unexpected JSON shapes. Manifest rows
are executed generically, so adding a new differential case should not require
editing the runner.

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
successful returns, Go panics, unsupported features, and stuck states. The
coverage harness compares canonical Go fixtures against the corresponding Lean
GoCore observations and reports all failing stages.

Deliverables:

- Define a stable observation format:

```text
status : ok | panic | unsupported | stuck | error
returns : Array Value
message : Option String
```

- Add a Go-source harness that runs concrete test programs with selected inputs.
- Compare Go results against Lean GoCore observations.
- Drive same-source differential cases from local metadata with explicit
  feature tags, argument values, and expected Go runtime status.
- Keep static compile/typecheck negative tests in a separate negative coverage
  lane, because rejected Go programs have no runtime observation to compare.
- Reject expected `unsupported`, `stuck`, or `error` statuses in executable
  metadata. These are Lean/model outcomes and must remain red in the
  conformance lane.
- Require manifest reasons for expected Go `panic` results.
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

Status (re-pointed 2026-08-19, bug-fix arc slice 6): **the current
coverage claim lives in `docs/language-coverage-ledger.md`** — one
classified row per section of the pinned go1.26.5 spec and memory
model (covered-with-grade / frontier / latitude / out-of-language,
zero unclassified), the frontier feature table with every refusal
point, the ordered sequential build queue, and the named
concurrency-entangled design questions. The feature-list prose that
used to sit here (and the "expected progression" below) is superseded:
any statement about what GoLean supports cites the ledger's rows and
grades, not this file.

Feature order is the ledger's build queue (smallest-diagnosed first,
raft-path rows boosted, complex last as the one large arc);
concurrency-entangled features advance by design ruling, not queue
position.

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

1. Complete the remaining architecture hardening gate from
   `docs/archive/architecture-audit.md`: continue the typed-integer/string slice with
   rune operations and remaining integer edge cases, and add a small relational
   semantics skeleton.
2. Keep expanding deterministic differential coverage, but prefer cases that
   force representation decisions we need anyway: typed integers, bytes,
   strings, conversions, and comparability.
3. Continue slices using the descriptor/backing-location model in
   `docs/slice-model.md`, especially zero-capacity edge cases and append growth
   policy refinement.
4. Track frontend gaps separately from semantic gaps. Gobra-fronted failures
   such as `delete` should pressure the Gobra fork or a future native frontend,
   not distort GoCore.
5. Add maps and named-type/conversion behavior driven by corpus failures.
6. Integrate Microsmith/GoSmith only after scalar, pointer, struct, array, and
   slice cases have deterministic coverage, typed integer policy, and feature
   filters.
7. Keep checking old/new Goose before adding each larger semantic feature.

## W7 — SpecTec-Go: the AST-level spec and frontend correctness (added 2026-08-20, Mike)

Mike is building a **Lean version of SpecTec** (the Wasm spec DSL:
human-readable formal specifications rendering LaTeX and generating
prover definitions; prior art reviewed in
`docs/2026-08-17_prior-art-spectec.md`). Plan of record:

- **The tool** (external, Mike's): first prototype expected within
  days of 2026-08-20.
- **The big rock: the Go spectec document** — an AST-level formal
  spec covering a large proportion of sequential Go (no concurrency
  initially). Convergence strategy: **differential testing** — the
  spec's generated Lean semantics runs the existing corpus against
  `go run` and against GoCore, so the corpus (2,300+ cases, the
  language-coverage ledger's sequential sections as the fragment
  map, `docs/spec-interpretations.md` as the pinned readings) drives
  the spec document to correctness the same way it drove the machine.
- **Frontend correctness enters scope**: preferred route is
  **translation validation** — per-program simulation certificates
  (spectec-AST semantics ≃ GoCore semantics of the emitted wire,
  checked in Lean per corpus case / subject file) rather than a
  verified re-implemented elaborator. This gives the twin's theorems
  "lowering checked" instead of "lowering trusted" and targets the
  TCB component where every recent silent-wrong-answer bug lived
  (BUG-057/058/062/063, the hoist family).
- **Interaction with W3.2 slice 6a (the opsem artifact): 6a HOLDS
  for the prototype** — if the tool lands on its expected timeline,
  spectec becomes the master notation (GoCore proven against it)
  rather than a bespoke LaTeX derivation; the rule-extraction
  machinery stays notation-agnostic either way.
