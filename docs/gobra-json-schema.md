# Gobra JSON Schema Strategy

Lean is the schema authority for Gobra JSON.

The Gobra fork should emit JSON that targets the Lean wire model. Lean decoders must stay strict: unexpected fields, unknown tags, wrong scalar types, and malformed source positions are bugs. The Scala exporter should fail rather than emit data that Lean cannot classify.

Current status:

- Gobra emits transformed internal IR as `.internal.json`.
- `golean gobra-json-check` validates emitted artifacts in Lean.
- `golean gobra-json-tags` reports observed constructor tags and fails on tags outside the current Lean allowlist.
- The Lean importer decodes the top-level `Program`, source positions, types, parameters, proxies, and smoke-corpus member kinds into typed structures.
- Function bodies, specifications, and most expressions/statements are still carried as structural `Value` nodes.

Next implementation step:

- Replace structural `Value` fields in members with typed `Stmt`, `Expr`, and `Assertion` wire nodes.
- Generate or derive strict decoders from the Lean wire ADT.
- Generate the Scala export ADT/encoder from the same schema source, or generate a machine-readable schema from Lean that Scala targets.
