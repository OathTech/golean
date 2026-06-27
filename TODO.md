# TODO

## Gobra JSON Schema

- Make the Lean wire ADT the schema authority for Gobra JSON. This is the project direction; see `docs/gobra-json-schema.md`.
- Generate strict Lean decoders from that ADT, rejecting missing fields, extra fields, wrong tags, and wrong scalar types.
- Generate the Scala export ADT/encoder from the same schema source, or generate a machine-readable schema from Lean that the Gobra exporter targets.
- Replace the current structural `GobraJson.Value` importer with semantic `Program`, `Member`, `Stmt`, `Expr`, `Ty`, and `Source` types.
- Add negative tests for surprise JSON inputs: unknown top-level fields, unknown tags, extra constructor fields, missing constructor fields, non-integral numbers, and malformed source positions.
