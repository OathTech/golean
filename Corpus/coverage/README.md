# Coverage Corpus

This directory is the source of truth for coverage-oriented testing.

See `docs/coverage-suite-structure.md` for the target large-suite layout,
metadata format, naming scheme, subset runner UX, and migration plan.

## Layout

- `manifest.tsv`: active executable differential cases.
- `litmus/<case>/main.go`: tiny Go programs, usually one feature per package.
- `negative/compile/manifest.tsv`: tiny invalid Go programs that must fail
  during Go compilation or typechecking.
- `negative/compile/<case>/main.go`: compile-negative litmus programs.

Executable differential cases use one canonical Go source. The same `main.go`
is run by `go run` and exported through the frontend for Lean execution. There
are no hand-maintained Gobra variants.

Each executable row names a subject function in `manifest.tsv`. That function
must be defined in the canonical Go file and contain the feature behavior under
test. For successful executable cases, the file's `main` function is only an
observation harness that calls the subject function and prints JSON. For
expected panic cases, `main` calls the subject directly and lets the Go process
panic; the top-level runner normalizes that real process failure into the same
panic observation shape Lean emits. Lean runs the subject function directly; Go
runs `main`; both paths consume the same source file.

Runtime-negative Go behavior, such as bounds errors or divide-by-zero panics,
belongs in `manifest.tsv` with `expected_status=panic` and a concrete
`expected_reason`. Static Go errors that prevent execution belong in
`negative/compile`.

Grouped litmus files are allowed when the file remains small and each manifest
row names the feature being exercised. Large tours stay under
`Corpus/challenges` until they are broken into coverage cases.

## Commands

```sh
scripts/coverage
scripts/diff-coverage
scripts/coverage-negative
scripts/diff-one litmus/if-return
```

The coverage scripts report every row before exiting. A nonzero exit means at
least one feature is not fully covered by the requested lane.
