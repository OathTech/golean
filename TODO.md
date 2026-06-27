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

- Broaden GoCore from integer expressions, assignments, blocks, assertions, and while loops to calls, structs, pointers, fields, slices, maps, and interfaces.
- Keep Gobra-specific handling in `GobraToIR`; semantic work belongs in GoCore unless it is purely frontend lowering.
- Add a Go-source execution harness and compare Go observable results with Lean-side GoCore execution.
- Emit stable machine-readable observations for both sides: return values, panics/errors, and unsupported-feature failures.

## GoCore Memory Milestone

- Replace stable variable references with heap-backed locals.
- Add `Loc.base` and `Loc.field` path-like locations.
- Add typed load, store, address-of, and dereference.
- Add `Value.struct`, struct literals, field get, and field ref.
- Add direct function calls with fresh call frames.
- Make `examples/swap` execute to the expected final assertion failure.

## Proof Generation

- Generate struct typed points-to predicates as field-wise ownership.
- Generate field load/store/access lemmas over `Loc.field`.
- Prototype a Lean WP/VCG layer over GoCore.
- Evaluate where Iris-Lean should enter for heap and concurrency reasoning.
