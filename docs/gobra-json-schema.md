# Gobra JSON Schema Strategy

Lean is the schema authority for Gobra JSON.

The Gobra fork should emit JSON that targets the Lean wire model. Lean decoders must stay strict: unexpected fields, unknown tags, wrong scalar types, and malformed source positions are bugs. The Scala exporter should fail rather than emit data that Lean cannot classify.

This wire model is an input boundary, not the core semantics. Successfully
decoded Gobra JSON is lowered into GoCore before execution. Gobra
verification-only constructs are decoded fail-closed because Gobra emits them,
but they are not GoCore semantics.

Current status:

- Gobra emits transformed internal IR as `.internal.json`.
- `golean gobra-json-check` validates emitted artifacts in Lean.
- `golean gobra-json-tags` reports observed constructor tags and fails on tags outside the current Lean allowlist.
- The Lean importer decodes the top-level `Program`, source positions, types, parameters, proxies, smoke-corpus member kinds, specifications, termination measures, method bodies, statements, assignees, expressions, permissions, and assertions into typed structures.
- `GobraToIR` lowers the currently supported executable Go subset into GoCore and erases Gobra-only assertions/specifications.
- Backend annotations are intentionally modeled as an uninhabited wire type for now. Empty arrays pass; any emitted annotation fails validation until we add an explicit typed representation.

Next implementation step:

- Generate or derive strict decoders from the Lean wire ADT.
- Generate the Scala export ADT/encoder from the same schema source, or generate a machine-readable schema from Lean that Scala targets.
- Broaden the typed `Stmt`, `Expr`, and wire-only `Assertion` nodes against a larger Gobra corpus.
