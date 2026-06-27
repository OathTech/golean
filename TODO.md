# TODO

See `docs/roadmap.md` for the phased project roadmap. This file tracks tactical
backlog items.

## Gobra JSON Schema

- Make the Lean wire ADT the schema authority for Gobra JSON. This is the project direction; see `docs/gobra-json-schema.md`.
- Generate strict Lean decoders from that ADT, rejecting missing fields, extra fields, wrong tags, and wrong scalar types.
- Generate the Scala export ADT/encoder from the same schema source, or generate a machine-readable schema from Lean that the Gobra exporter targets.
- Broaden the typed `GobraJson` importer from the smoke-corpus `Stmt`, `Expr`, `Assertion`, and `TerminationMeasure` tags to larger Gobra corpora.
- Add more negative tests for surprise JSON inputs: missing constructor fields, malformed source positions, unsupported type tags, unsupported statement tags in nested bodies, and unsupported expression tags in wire-only spec fields.
- Keep the Gobra wire model isolated from GoCore so replacing Gobra with our own Go frontend later does not require changing the semantic core.

## Differential Execution

- Keep Gobra-specific handling in `GobraToIR`; semantic work belongs in GoCore unless it is purely frontend lowering.
- Replace stringly typed evaluator failures with structured `GoError` values and
  stable observations. CLI classification must not depend on matching error
  message prefixes.
- Treat `unsupported` and `stuck` as failures by default. A differential case may
  expect them only with an explicit manifest reason.
- Use a structured observation parser/comparator for Go and Lean output instead
  of raw JSON string comparison.
- Add timeouts/fuel for Gobra export, Go execution, Lean execution, and Lean
  builds used by the harness.
- Prevent stale or cross-test artifacts by tying generated Gobra JSON to source
  hashes and using per-run temporary artifact directories with atomic publish.
- Extend `scripts/diff-smoke` with same-source fixtures where possible, so Go
  execution and Gobra/Lean execution cannot silently drift apart.

## Hardening Phase

- Keep the executable interpreter factored so it can be related to a future
  relational GoCore semantics for Iris-Lean. The interpreter is for testing; it
  should not be the only semantic authority.
- Thread structured errors through GoCore:
  `panic`, `unsupported`, `stuck`, and `internal`.
- Classify nil pointer dereference and Go-defined runtime traps as `panic`, not
  `stuck`.
- Replace raw `GoValue` equality with type-directed comparable equality.
- Decide and encode the integer model: Go-sized signed/unsigned words where
  available, or explicit rejection of programs whose behavior depends on widths
  not yet modeled.
- Replace `execStmt : ExecState -> Except ... ExecState` with an explicit
  `ExecOutcome` for normal completion, return, break, continue, panic,
  unsupported, and stuck behavior.
- Add broader control-flow coverage around nested `if`, early `return`, and
  later labeled control flow.
- Keep expression evaluation able to grow to calls-in-expressions, allocation,
  map operations, and channel operations without changing its public shape
  again.
- Continue slices with descriptor values over backing locations, following
  `docs/slice-model.md`. Do not model slices as copied vectors.
- Keep append capacity growth explicit in tests: either avoid observing capacity
  after a reallocating append, or tag the case as Go-runtime-specific until the
  executable policy is chosen.
- Track semantic policy choices that remain open for differential refinement,
  especially allocation limits, append growth, zero-capacity slices, string
  slicing, and panic-message details.
- Keep improving artifact-generation scalability. Gobra exports are now
  incremental by source hash, but a cold export still invokes SBT/Gobra once per
  fixture. Prefer batched package export or a native Go frontend path once
  practical.
- Treat Gobra's permission-argument variants of `copy` and `append` as
  frontend artifacts. The Gobra fork may enrich `--printInternalJson` with
  plain-Go nodes such as `GoSliceCopy` and `GoSliceAppend`; do not add Gobra
  permission semantics to GoCore just to support them.
- Evaluate lvalues and rvalues before committing stores, so multiple assignment
  and call assignment match Go's sequencing rules.
- Bounds-check indexed locations when evaluating the lvalue, including
  address-of-index operations such as `&a[i]`.
- Keep GoCore free of Gobra verification constructs. Gobra assertions,
  preconditions, postconditions, invariants, predicates, and ghost artifacts are
  frontend wire data only unless a later proof-extraction design explicitly
  reinterprets them outside the runtime semantics.

## Gobra Lowering Hardening

- Make lowering fail closed: unsupported body nodes should not hide in dead code
  as inert GoCore nodes unless a test explicitly expects unsupported output.
- Preserve and report bodyless functions, methods, and predicates instead of
  silently dropping them.
- Use typed lvalue syntax in the wire/lowering layer so field/index assignment
  cannot be represented by arbitrary malformed expressions.
- Replace adjacency-based type definition recovery with explicit validated
  structure from Gobra JSON.
- Keep `knownTagNames` complete relative to `GobraJson` decoders and test that
  unknown tags are rejected in nested positions.

## GoCore Memory Milestone

- Add regression tests that observe memory effects through ordinary Go returns
  or Go-side output, not Gobra assertions.
- Add richer call-frame tests, including returned values and nested calls.
- Add method-call tests from Gobra JSON beyond `examples/swap`.

## Completed GoCore Memory Milestone Items

- Replaced stable variable references with heap-backed locals.
- Added `Loc.base` and `Loc.field` path-like locations.
- Added load, store, address-of, dereference, struct field get, and field ref.
- Added `Value.struct` and struct literals.
- Added direct function and method calls with fresh local frames and shared heap.
- Made `examples/swap` execute as ordinary Go after Gobra assertions/specs are
  erased at lowering.
- Added GoCore `if`, explicit `return`, and unlabeled `break`/`continue`, with
  Gobra-fronted differential smoke coverage.
- Added fixed-array `len`/`cap`, with Gobra-fronted differential smoke
  coverage.
- Added fixed-array zero-value initialization, nested arrays, arrays through
  function parameters/results, and pointer-to-array indexing/assignment.
- Reviewed Goose/Perennial/Gobra slice designs and selected a descriptor over
  backing locations as the direction for GoCore slices.
- Added the first descriptor-backed slice subset: nil slice defaults, array
  slicing, slice indexing/addressing, two-index and full slicing, Gobra `Slice`
  JSON decoding/lowering, and differential array-to-slice alias coverage.
- Added Gobra `MakeSlice` decoding/lowering and nonzero-capacity `make` support
  with differential coverage.
- Added Gobra `NewSliceLit` decoding/lowering and slice literal differential
  coverage.
- Enriched the Gobra JSON fork so `--printInternalJson` accepts plain Go
  `copy`/`append` and emits `GoSliceCopy`/`GoSliceAppend`; added GoCore
  execution and differential coverage for overlapping copy and append
  in-place/growth aliasing.
- Made `scripts/gobra-smoke` manifest-driven for Lean execution and expanded
  the differential suite to 29 cases, including typed nil slices, nil/empty
  slice distinctions, nil append, variadic overlap append, full slicing,
  full-slice bounds panics, zero-length `make`, nil copy, and short copy.
- Added source-hash based Gobra artifact caching, so warm `scripts/gobra-smoke`
  runs reuse unchanged successful exports.

## Proof Generation

- Deferred until after the executable semantics and differential harness cover a
  substantial Go subset.
- Define a relational small-step or big-step GoCore semantics over the same
  syntax, values, locations, errors, and outcomes as the executable interpreter.
- Prove, where practical, that the executable interpreter is sound with respect
  to the relational semantics on supported deterministic terminating runs.
- Generate struct typed points-to predicates as field-wise ownership.
- Generate field load/store/access lemmas over `Loc.field`.
- Prototype a Lean WP/VCG layer over GoCore.
- Evaluate where Iris-Lean should enter for heap and concurrency reasoning.
