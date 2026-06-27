# Phase 1: Artifact Export and Corpus Harness

## Current Slice

The current implementation provides a small Gobra artifact exporter:

```sh
lake exe golean gobra-export --manifest Corpus/gobra-smoke.txt --out artifacts/gobra-smoke
```

or:

```sh
scripts/gobra-smoke
```

For each corpus entry, the exporter:

- checks that the source exists;
- copies the `.gobra` file into `artifacts/.../work`;
- invokes Gobra with `--noVerify --printInternal --printVpr`;
- records stdout, stderr, exit code, and artifact paths;
- writes per-entry `result.json` and an aggregate `manifest.json`.

The source copy matters because Gobra writes `.internal` and `.vpr` files beside
the input file. Running on the copied file keeps generated artifacts out of
`../deps/gobra`.

## Smoke Corpus

The smoke corpus is in `Corpus/gobra-smoke.txt`:

- `examples/swap`
- `features/while1`
- `features/multi-assign`
- `features/pointer-identity`

All four currently export successfully on this machine.

## Next Work

- Avoid starting sbt once per corpus entry.
- Add a richer corpus manifest with expected status and feature tags.
- Add stable content hashes for generated `.internal` and `.vpr` artifacts.
- Add a Gobra exporter that emits a machine-readable internal IR directly,
  rather than relying on pretty-printed `.internal` text.
