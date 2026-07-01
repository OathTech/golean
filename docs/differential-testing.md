# Differential Testing

The active testing strategy is to compare executable observations from real Go
programs with observations from the same source after a frontend lowers it into
GoCore and Lean executes it. Gobra JSON is the current frontend, but the
coverage corpus and Go observation harness are frontend-independent.

Observation format:

```text
status : ok | panic | unsupported | stuck | error
values : Array Value
message : Option String
```

Every observation carries `schema = "golean-observation-v1"`. Lean validates
the observation recursively and rejects unknown value tags, missing fields, and
extra fields.

## Current Harness

`Corpus/coverage` is the source of truth for coverage tests. The active
executable differential corpus lives in `Corpus/coverage/exec`. Each test
package contains `main.go` plus a local `cases.tsv` metadata file. Stable case
ids are derived from the path under `exec`.

`scripts/diff-coverage` is the main conformance loop. It exports every
canonical Go source through the selected frontend, generates a temporary Go harness that
strips the handwritten `main` and calls the metadata subject with the metadata
integer args, runs that harness with `go run`, runs every successfully exported
artifact through Lean, compares observations structurally, and reports every
case before exiting. It does not stop at the first failure, and its nonzero exit
code means at least one feature is not fully covered.

Set `GOLEAN_FRONTEND=gobra` to use the current Gobra JSON path. Other frontend
values currently fail closed as `frontend-export` failures until an adapter is
implemented. Gobra itself is treated as a temporary single-file frontend: if a
corpus package has multiple non-test Go files, the case is red rather than
silently comparing Go's package execution against Gobra's single-file export.

`scripts/coverage-negative` runs static negative Go cases under
`Corpus/coverage/negative/compile`. These are invalid Go programs that should
fail during compilation or typechecking. Each package has a local `case.tsv`
metadata file. They are not executable differential tests, but they are part of
the coverage picture because a full Go frontend must diagnose them cleanly. The
lane uses `go build`, not `go run`, so a runtime panic cannot count as a static
negative pass.

`scripts/coverage` runs both lanes by default. It also supports focused
subcommands:

```sh
scripts/coverage list --tag slices
scripts/coverage run --prefix maps/
scripts/coverage run --status panic
scripts/coverage run --last-failed
scripts/coverage report --full
scripts/coverage report --by tag
scripts/coverage report --by stage
```

`scripts/diff-one <id> ...` remains a short exact-id runner for the tight
edit/test loop while implementing a feature.

Executable cases are described by `cases.tsv` files next to their Go source.
The local metadata is intentionally strict and small:

```text
id<TAB>subject<TAB>args<TAB>expected_status<TAB>expected_reason<TAB>features
```

Use `-` for no integer args. Feature tags are comma-separated. `expected_status`
is the expected Go runtime status and must be `ok` or `panic`; use `-` for
`expected_reason` unless the expected status is `panic`. Frontend export
failures, Lean `unsupported`, Lean `stuck`, Lean `error`, and differential
mismatches are red conformance failures, not expected metadata statuses.
`scripts/coverage-manifest` derives the normalized manifest consumed by the
selected frontend/Lean runner. Frontend artifact paths are computed by the
frontend adapter, not stored in the corpus-derived manifest. The manifest
generator fails on malformed rows, missing files, invalid statuses, invalid
integer arguments, and observation mismatches.

An `ok` subject must return at least one observable value. A subject that only
mutates local state and returns nothing is not a differential test; it can pass
without observing the behavior it intended to test. Return a checksum or other
small deterministic summary instead.

The `subject` column is a source-level function name, not a Gobra
hash-suffixed internal name. It must be defined in the canonical Go file. The
Go side does not trust handwritten observation code: the runner generates a
temporary harness that calls the subject with the metadata args. For expected
panic cases, the generated harness lets the process panic. The runner checks
that the panic contains the manifest reason, then compares Lean against the
actual normalized Go panic message.

There are no hand-maintained Gobra variants. Differential cases compare the
same ordinary Go source against Lean execution after frontend artifacts have
been lowered to GoCore.

Runtime-negative behavior, such as divide-by-zero or bounds panics, belongs in
an executable `cases.tsv` row with `expected_status=panic`. Static negative behavior,
such as unused locals, invalid comparisons, or non-addressable assignments,
belongs in `Corpus/coverage/negative/compile`.

The script requires `go` on `PATH`.

The harness runs fixtures with module mode disabled and stores Go's build cache
under `artifacts/go-build-cache` so tests do not depend on writable user-level
cache directories.

The default executable lane is deterministic. Cases tagged `nondet` are
rejected unless `GOLEAN_ALLOW_NONDET=1` is set, and that mode is reserved for a
future relation-style oracle rather than ordinary equality.

Each run writes `artifacts/coverage/latest.tsv` plus
`artifacts/coverage/latest.meta.tsv`. The metadata records whether the run was
full or filtered, the filters, frontend, manifest hash, manifest case count,
total corpus size, git commit, and dirty flag. Reports warn when `latest.tsv`
came from a filtered run.
`scripts/coverage report --full` reports the latest complete corpus run even
after focused reruns overwrite `latest.tsv`; it regenerates the current full
manifest and warns/fails if the saved full report is stale.
`scripts/coverage negative` accepts the same style of `--id`, `--prefix`, and
`--tag` filters for compile-negative cases. `scripts/coverage all` intentionally
rejects filters so a partial lane cannot look like a full conformance pass.

The Gobra exporter is incremental by source hash. Each entry records the source
hash, scratch-source hash, and generated artifact paths in
`artifacts/coverage/results/<id>/result.json`; unchanged successful entries
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
5. Treat every Lean `unsupported`, `stuck`, or `error` as a red conformance
   result in the executable lane.
