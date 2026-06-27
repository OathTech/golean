# TODO

## Gobra JSON Schema

- Make the Lean wire ADT the schema authority for Gobra JSON. This is the project direction; see `docs/gobra-json-schema.md`.
- Generate strict Lean decoders from that ADT, rejecting missing fields, extra fields, wrong tags, and wrong scalar types.
- Generate the Scala export ADT/encoder from the same schema source, or generate a machine-readable schema from Lean that the Gobra exporter targets.
- Broaden the typed `GobraJson` importer from the smoke-corpus `Stmt`, `Expr`, `Assertion`, and `TerminationMeasure` tags to larger Gobra corpora.
- Add more negative tests for surprise JSON inputs: missing constructor fields, malformed source positions, unsupported type tags, unsupported statement tags in nested bodies, and unsupported expression tags in specs.

## Differential Execution

- Broaden `gobra-json-run` from integer expressions, assignments, blocks, assertions, and while loops to calls, structs, pointers, fields, slices, maps, and interfaces.
- Add a Go-source execution harness and compare Go observable results with Lean-side Gobra JSON execution.
- Emit stable machine-readable observations for both sides: return values, panics/errors, and unsupported-feature failures.
