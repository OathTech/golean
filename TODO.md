# TODO

See `docs/roadmap.md` for the phased project roadmap. This file tracks tactical
backlog items.

## Gobra JSON Schema

- Make the Lean wire ADT the schema authority for Gobra JSON. This is the project direction; see `docs/gobra-json-schema.md`.
- Generate strict Lean decoders from that ADT, rejecting missing fields, extra fields, wrong tags, and wrong scalar types.
- Generate the Scala export ADT/encoder from the same schema source, or generate a machine-readable schema from Lean that the Gobra exporter targets.
- Broaden the typed `GobraJson` importer from the smoke-corpus `Stmt`, `Expr`, `Assertion`, and `TerminationMeasure` tags to larger Gobra corpora.
- Add more negative tests for surprise JSON inputs: missing constructor fields, malformed source positions, unsupported type tags, unsupported statement tags in nested bodies, and unsupported expression tags in specs.

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
- Replace `--ignore-assert-at` with a fail-closed mechanism: stable assertion
  identifiers or an exact single-match source assertion check.
- Extend `scripts/diff-smoke` with same-source fixtures where possible, so Go
  execution and Gobra/Lean execution cannot silently drift apart.

## Hardening Phase

- Thread structured errors through GoCore:
  `panic`, `assertion`, `unsupported`, `stuck`, and `internal`.
- Classify nil pointer dereference and Go-defined runtime traps as `panic`, not
  `stuck`.
- Replace raw `GoValue` equality with type-directed comparable equality.
- Decide and encode the integer model: Go-sized signed/unsigned words where
  available, or explicit rejection of programs whose behavior depends on widths
  not yet modeled.
- Replace `execStmt : ExecState -> Except ... ExecState` with an explicit
  `ExecOutcome` for normal completion, return, break, continue, panic,
  unsupported, and stuck behavior.
- Make expression evaluation able to grow to calls-in-expressions, allocation,
  append, map operations, and channel operations without changing its public
  shape again.
- Evaluate lvalues and rvalues before committing stores, so multiple assignment
  and call assignment match Go's sequencing rules.
- Bounds-check indexed locations when evaluating the lvalue, including
  address-of-index operations such as `&a[i]`.
- Separate executable Go behavior from Gobra/spec behavior with an explicit
  mode: `goOnly`, `gobraAssertions`, and later `proofObligations`.

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

- Add a regression test that proves `examples/swap` reaches the final
  assertion, not an earlier assertion, without relying on manual JSON rewriting.
- Decide whether top-level Gobra pre/postconditions should be executable
  assertions, verification-only metadata, or controlled by a CLI flag.
- Add richer call-frame tests, including returned values and nested calls.
- Add method-call tests from Gobra JSON beyond `examples/swap`.

## Completed GoCore Memory Milestone Items

- Replaced stable variable references with heap-backed locals.
- Added `Loc.base` and `Loc.field` path-like locations.
- Added load, store, address-of, dereference, struct field get, and field ref.
- Added `Value.struct` and struct literals.
- Added direct function and method calls with fresh local frames and shared heap.
- Made `examples/swap` execute to the expected final assertion failure.

## Proof Generation

- Deferred until after the executable semantics and differential harness cover a
  substantial Go subset.
- Generate struct typed points-to predicates as field-wise ownership.
- Generate field load/store/access lemmas over `Loc.field`.
- Prototype a Lean WP/VCG layer over GoCore.
- Evaluate where Iris-Lean should enter for heap and concurrency reasoning.
