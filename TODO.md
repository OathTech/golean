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
- Promote cases from `Corpus/challenges/semantic-edges/` into the active
  Gobra/Lean differential suite one feature at a time. Keep the challenge
  corpus runnable by `scripts/semantic-edges-challenge-smoke`, but do not treat
  it as a supported-semantics claim until cases land in
  `Corpus/coverage/manifest.tsv`.
- Keep `Corpus/coverage` comprehensive. Do not remove cases because the
  frontend or semantics fails; let `scripts/coverage` report the failing stage.
- Do not maintain Gobra variants of coverage inputs. The canonical Go source is
  the input to both `go run` and the frontend/Lean path.
- Expand `Corpus/coverage/negative/compile` with static Go errors. Runtime Go
  errors that execute and panic belong in the differential manifest with
  `expected_status=panic`.
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
- Keep `scripts/diff-coverage` same-source: Go execution and frontend/Lean
  execution must consume the same canonical Go file.

## Hardening Phase

- Extend type-directed equality for interfaces, function values, and exact
  dynamic comparability panics once those value forms exist.
- Add a small relational GoCore semantics skeleton before concurrency or
  Iris-facing proof rules.
- Keep the executable interpreter factored so it can be related to a future
  relational GoCore semantics for Iris-Lean. The interpreter is for testing; it
  should not be the only semantic authority.
- Thread structured errors through GoCore:
  `panic`, `unsupported`, `stuck`, and `internal`.
- Classify nil pointer dereference and Go-defined runtime traps as `panic`, not
  `stuck`.
- Extend the integer/string model beyond the current fixed-width and byte-string
  slices: constants, rune iteration/conversions, broader conversion families,
  more integer edge cases, and exact architecture-dependent `int`/`uint` policy
  in the future relation.
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

- Enrich Gobra JSON string literals with exact Go bytes, not only Scala/JSON
  text. Go escapes such as `\xNN` can denote arbitrary bytes, and GoCore's
  byte-backed `GoString` should reject or avoid textual literal exports that
  cannot prove byte exactness.
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

- Track frontend gaps separately from semantic gaps. For example, Gobra
  currently rejects the Go `delete` builtin, so map deletion needs either Gobra
  fork enrichment or a future native Go frontend before it can enter the active
  Gobra-fronted differential suite.
- Add regression tests that observe memory effects through ordinary Go returns
  or Go-side output, not Gobra assertions.
- Add richer call-frame tests, including returned values and nested calls.
- Add method-call tests from Gobra JSON beyond `examples/swap`.
- Track Gobra frontend gaps found while promoting semantic-edge cases: Gobra accepts
  variadic calls/spreads but rejects `range` directly over a `...int`
  parameter, so `features/variadic.gobra` uses `len`/index iteration.
- Track Gobra frontend gaps found while promoting conversion cases: Gobra
  rejects legal Go integer-to-string conversions such as `string(65)` and
  `string(byte(255))`, so active differential coverage cannot use the Gobra
  frontend for this rune-conversion slice yet.
- Track Gobra frontend gaps found while promoting switch cases: Gobra accepts
  basic and expressionless switches but rejects explicit `fallthrough` in the
  parser.

## Completed GoCore Memory Milestone Items

- Split the former monolithic `GoLean/IR.lean` into GoCore syntax, value import
  point, state, operations, and executable evaluation modules. `GoLean/IR.lean`
  remains as a compatibility import.
- Converted GoCore expression and assignee evaluation to return an updated
  `ExecState`, preserving Go's evaluate-before-store assignment discipline while
  leaving room for calls-in-expressions, receives, and effectful builtins.
- Moved concrete `GoError`, `Loc`, `SliceValue`, `MapValue`, and `GoValue`
  definitions into `GoLean/GoCore/Value.lean`; `GoLean/Runtime.lean` is now only
  a compatibility import.
- Replaced raw value-shape equality with type-directed GoCore equality and
  type-directed map-key comparison.
- Added first typed integer support: GoCore integer kinds, Gobra integer-kind
  lowering, fixed-width normalization on typed stores/arithmetic, a 64-bit
  executable policy for `int`/`uint`, and `int8` overflow differential coverage.
- Added first integer conversion support: Gobra `Conversion` decoding/lowering,
  GoCore integer-to-integer conversion normalization, and `byte(300) == 44`
  differential coverage. Non-integer conversions remain explicitly unsupported.
- Added byte-backed string literals and string/`[]byte` conversions:
  Gobra JSON now exports exact `StringLit.bytes`, Lean rejects stale string
  literal JSON, GoCore has explicit byte-string conversion nodes, and the
  differential suite covers escaped arbitrary bytes plus conversion copy
  semantics.
- Added first shift support: Gobra `ShiftLeft`/`ShiftRight` decoding/lowering,
  fixed-width left/right shift normalization, signed arithmetic right shift,
  and negative-shift panic coverage.
- Added string byte indexing: indexing a Go string reads from its UTF-8 byte
  sequence and returns a `uint8`, with direct and differential coverage.
- Switched GoCore string values from Lean `String` to byte-backed `GoString`,
  matching Go's byte-level string operations and Perennial/new Goose's
  `go_string` model.
- Added two-index string slicing over bytes, including an invalid-UTF-8
  substring differential case.
- Added bitwise integer operators: `&`, `|`, `^`, `&^`, and unary `^`, using
  fixed-width modular bit patterns and type-directed result normalization.
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
