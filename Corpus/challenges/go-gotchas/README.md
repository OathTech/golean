# Go Gotchas Challenge Corpus

This directory tracks interesting Go edge cases from an AI-generated
`gotchas.go` tour. These are not part of the active Gobra/Lean differential
manifest yet. They are challenge programs to promote one at a time as GoCore
and the frontend cover the relevant language surface.

The split cases under `cases/` are runnable Go programs with compact JSON-ish
observations. They intentionally avoid Gobra syntax and are useful as reference
behavior for future differential cases.

Promotion rule:

1. Add or enrich GoCore semantics for one focused feature.
2. Add a Gobra fixture under `Corpus/features/`.
3. Add the matching Go fixture under `Differential/plain/`.
4. Add the row to `Differential/manifest.tsv`.
5. Run `scripts/gobra-smoke` and `scripts/diff-smoke`.

The catalog in `manifest.tsv` includes all source gotchas, including ones that
need substantial future work such as interfaces, channels, defer/recover,
concurrency, reflection-like formatting, floating point, and standard-library
behavior.
