# Differential Testing

The active testing strategy is to compare executable observations from real Go
programs with observations from Gobra JSON lowered into GoCore and executed in
Lean.

Observation format:

```text
status : ok | panic | unsupported | stuck | error
values : Array Value
message : Option String
```

## Current Harness

`Corpus/coverage` is the source of truth for coverage tests. The active
executable differential corpus lives in `Corpus/coverage/litmus`, and rows are
listed in `Corpus/coverage/manifest.tsv`.

`scripts/diff-coverage` is the main conformance loop. It exports every
canonical Go source through the frontend, runs every Go fixture with `go run`,
runs every successfully exported artifact through Lean, compares observations
structurally, and reports every case before exiting. It does not stop at the
first failure, and its nonzero exit code means at least one feature is not fully
covered.

`scripts/coverage-negative` runs static negative Go cases under
`Corpus/coverage/negative/compile`. These are invalid Go programs that should
fail during compilation or typechecking. They are not executable differential
tests, but they are part of the coverage picture because a full Go frontend must
diagnose them cleanly.

`scripts/coverage` runs both lanes. `scripts/diff-smoke` is retained as a
compatibility alias for `scripts/diff-coverage`.

`scripts/diff-one <id> ...` filters `Corpus/coverage/manifest.tsv` to one or
more exact manifest ids and then delegates to the differential coverage runner.
Use it for the tight edit/test loop while implementing a feature.

Executable cases are listed in `Corpus/coverage/manifest.tsv`. The manifest is
intentionally strict and small:

```text
id<TAB>go_dir<TAB>gobra_json<TAB>function<TAB>arg_ints<TAB>expected_status<TAB>features<TAB>expected_reason
```

Use `-` for no integer args. Feature tags are comma-separated. Use `-` for
`expected_reason` unless the expected status is `unsupported` or `stuck`; those
statuses must include a concrete reason so they cannot become invisible
coverage debt. The smoke script fails on malformed rows, missing files, unknown
statuses, invalid integer arguments, and observation mismatches.

There are no hand-maintained Gobra variants. Differential cases compare the
same ordinary Go source against Lean execution after frontend artifacts have
been lowered to GoCore.

Runtime-negative behavior, such as divide-by-zero or bounds panics, belongs in
the executable manifest with `expected_status=panic`. Static negative behavior,
such as unused locals, invalid comparisons, or non-addressable assignments,
belongs in `Corpus/coverage/negative/compile`.

The script requires `go` on `PATH`.

The harness runs fixtures with module mode disabled and stores Go's build cache
under `artifacts/go-build-cache` so tests do not depend on writable user-level
cache directories.

The Gobra exporter is incremental by source hash. Each entry records the source
hash, scratch-source hash, and generated artifact paths in
`artifacts/gobra-smoke/results/<id>/result.json`; unchanged successful entries
are reused on later runs. `scripts/diff-coverage` also checks artifact source
hashes before running Lean and refreshes artifacts once if they are missing or
stale.

Remaining scalability limitation: even with per-entry caching, a cold export
still invokes SBT/Gobra once per corpus entry. A later native Go frontend or a
batched Gobra export mode would make cold starts much cheaper.

## Random Program Generators

There are existing Go random-program generators worth reusing.

### GoSmith

Repository: `dvyukov/gosmith`

GoSmith generates random but legal Go programs to test Go compilers. Its README
reports historical compiler and spec bugs found by this approach. It is older,
but directly analogous to Csmith and is explicitly designed for compiler
differential testing.

Useful points:

- Generates complete legal Go programs.
- Has a driver for compiler/checker comparison.
- License is BSD-style.

Risks:

- The repository is old and exported from code.google.com.
- It likely generates a much broader Go subset than GoCore supports today.
- We would need filtering, feature flags, or post-generation triage.

### Microsmith

Repository: `ALTree/microsmith`

Microsmith is a newer fuzzer that generates valid Go programs and stress-tests
Go toolchains. It uses Go's parser/typechecker internally and has a debug mode
that prints generated programs.

Useful points:

- Newer and actively updated.
- Generates valid Go programs through Go AST/typechecking infrastructure.
- Has options for single-package generation and compiler/toolchain fuzzing.

Risks:

- It targets compiler crashes, not semantic equivalence against a restricted
  interpreter.
- It currently requires a Go 1.25-era toolchain according to its `go.mod`.
- Like GoSmith, it will need filtering or configuration to stay within GoCore's
  supported subset.

## Recommended Use

Do not start by fuzzing arbitrary generated Go. First:

1. Build a deterministic corpus of small canonical Go litmus programs.
2. Add feature tags and expected runtime status to each case.
3. Use Goose and new Goose as semantic references before adding each feature.
4. Once GoCore supports enough scalar, pointer, struct, array, and slice
   behavior, integrate Microsmith or GoSmith behind a feature filter.
5. Treat every unexpected `unsupported` as a coverage bug and every `stuck` as a
   semantics/lowering bug unless the manifest explicitly expects it.
