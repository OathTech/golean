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

`scripts/gobra-smoke` exports every Gobra corpus entry, validates each emitted
JSON file, then runs every manifest row through Lean and checks that the
observed status is the expected status. It deliberately does not hardcode
expected values; value equality belongs in the differential step.

`scripts/diff-smoke` compares plain Go fixtures under `Differential/plain`
against Lean execution of the corresponding Gobra smoke artifacts. This is the
main conformance loop: add a small Go program, add the matching Gobra frontend
fixture, add a manifest row, and require real Go and Lean observations to
match.

Cases are listed in `Differential/manifest.tsv`. The manifest is intentionally
strict and small:

```text
id<TAB>go_dir<TAB>gobra_json<TAB>function<TAB>arg_ints<TAB>expected_status<TAB>features<TAB>expected_reason
```

Use `-` for no integer args. Feature tags are comma-separated. Use `-` for
`expected_reason` unless the expected status is `unsupported` or `stuck`; those
statuses must include a concrete reason so they cannot become invisible
coverage debt. The smoke script fails on malformed rows, missing files, unknown
statuses, invalid integer arguments, and observation mismatches.

Gobra assertions and specifications are not observations. Differential cases
compare ordinary Go execution against Lean execution after Gobra verification
artifacts have been erased by lowering.

The script requires `go` on `PATH`.

The harness runs fixtures with module mode disabled and stores Go's build cache
under `artifacts/go-build-cache` so tests do not depend on writable user-level
cache directories.

Current scalability limitation: Gobra export is slow because the harness invokes
SBT/Gobra once per corpus entry. `scripts/diff-smoke` reuses
`artifacts/gobra-smoke` when it exists and checks artifact source hashes before
running Lean; if artifacts are missing or stale, it refreshes them once. The
next harness improvement should make Gobra export incremental or batched so
adding one fixture does not require re-exporting the entire corpus.

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

1. Build a deterministic paired corpus of small Go/Gobra programs.
2. Add feature tags to each case.
3. Use Goose and new Goose as semantic references before adding each feature.
4. Once GoCore supports enough scalar, pointer, struct, array, and slice
   behavior, integrate Microsmith or GoSmith behind a feature filter.
5. Treat every unexpected `unsupported` as a coverage bug and every `stuck` as a
   semantics/lowering bug unless the manifest explicitly expects it.
