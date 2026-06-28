# Go Semantic Edges Challenge Corpus

This directory tracks interesting Go edge cases from AI-generated `gotchas.go`
and `bestiary.go` tours. These are not part of the active Gobra/Lean
differential manifest yet. They are challenge programs to promote one at a time
as GoCore and the frontend cover the relevant language surface.

The split cases under `cases/` are runnable Go programs with compact JSON-ish
observations. They intentionally avoid Gobra syntax and are useful as reference
behavior for future differential cases.

The full tours under `full/` are runnable reference programs. They print human
readable output rather than the compact observations used by the active
differential harness.

Promotion rule:

1. Add or enrich GoCore semantics for one focused feature.
2. Add a Gobra fixture under `Corpus/features/`.
3. Add the matching Go fixture under `Differential/plain/`.
4. Add the row to `Differential/manifest.tsv`.
5. Run `scripts/gobra-smoke` and `scripts/diff-smoke`.

The catalog in `manifest.tsv` includes the source gotchas and bestiary cases,
including ones that need substantial future work such as interfaces, channels,
defer/recover, concurrency, reflection-like formatting, floating point,
generics, and standard-library behavior.
