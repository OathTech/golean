> **ARCHIVED (2026-07-21).** Historical record — superseded or completed; see `docs/archive/README.md`. Do not treat as current guidance.

# Phase 1: Artifact Export and Corpus Harness

## Current Slice

The current implementation provides a small Gobra artifact exporter:

```sh
scripts/diff-coverage
```

For each corpus entry, the exporter:

- checks that the source exists;
- copies the canonical Go file into `artifacts/.../work`;
- invokes Gobra with `--noVerify --printInternal --printInternalJson`;
- records stdout, stderr, exit code, and artifact paths;
- writes per-entry `result.json` and an aggregate `manifest.json`.
- validates each emitted `.internal.json` with the strict Lean decoder.
- lowers Gobra JSON into the GoCore deep embedding.
- executes the integer `while1`, `multi-assign`, and expected-failing `pointer-identity` smoke functions through the Lean-side GoCore evaluator.

The source copy matters because Gobra writes `.internal` and `.internal.json`
files beside the input file. Running on the copied file keeps generated
artifacts out of `Corpus/coverage`.

Gobra is tracked as a submodule at `third_party/gobra`, using the
`https://github.com/septract/gobra-json` fork and the local `gobra-json` branch
for exporter work.

## Coverage Corpus

The active executable corpus is under `Corpus/coverage/exec`, with local
`cases.tsv` metadata files next to tiny canonical Go fixtures. Static negative
cases that should fail Go compilation/typechecking live under
`Corpus/coverage/negative/compile`, with local `case.tsv` metadata files.

## Next Work

- Avoid starting sbt once per corpus entry.
- Keep expanding the corpus with tiny feature-focused Go litmus tests.
- Add stable content hashes for generated `.internal` and `.vpr` artifacts.
- Broaden GoCore and `GobraToIR` beyond the current integer/control-flow subset.
- Keep frontend failures visible in coverage reports instead of maintaining
  alternate frontend-only sources.
