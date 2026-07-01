# Coverage Suite Structure

This document describes the target structure for a large Go differential
coverage suite. The goal is to make adding tests cheap, make failures explicit,
and avoid a central manifest becoming a second source of truth.

## Goals

- Every executable test uses ordinary canonical Go source.
- The Go and Lean paths consume the same source file.
- Runtime behavior is classified per case: `ok`, `panic`, `unsupported`,
  `stuck`, or `error`.
- Static invalid-Go cases live in a separate negative lane.
- Test ids, source paths, and artifact paths are derived mechanically.
- Subsets are runnable by id, directory prefix, feature tag, expected status,
  or last failure stage.
- Reports summarize both individual red/green cases and feature coverage.

## Directory Layout

Target layout:

```text
Corpus/coverage/
  exec/
    <area>/
      <feature>/
        <case>/
          main.go
          cases.tsv
  negative/
    compile/
      <area>/
        <feature>/
          <case>/
            main.go
            case.tsv
  suites/
    smoke.lst
    frontend.lst
    semantics.lst
  README.md
```

The current `Corpus/coverage/litmus` directory is the first executable suite.
We should migrate it into `exec/` incrementally once the metadata generator is
in place.

## Naming

Use stable, lowercase kebab-case path components. The executable case id is
derived from the path under `exec` plus the row id from `cases.tsv`.

For a one-case package:

```text
Corpus/coverage/exec/slices/append/overlap/
  main.go
  cases.tsv
```

The full id is:

```text
slices/append/overlap
```

For grouped litmus packages, add a short row id:

```text
Corpus/coverage/exec/strings/bytes/indexing/
  main.go
  cases.tsv
```

with rows `ascii`, `utf8-leading-byte`, and `utf8-continuation-byte`, giving:

```text
strings/bytes/indexing/ascii
strings/bytes/indexing/utf8-leading-byte
strings/bytes/indexing/utf8-continuation-byte
```

Prefer one case per package unless grouping removes real boilerplate while
remaining easy to inspect.

## Case Metadata

Each executable package has a `cases.tsv` file. The runner validates exact
column count, valid statuses, known feature tags, subject presence in `main.go`,
and expected reason policy.

Columns:

```text
id<TAB>subject<TAB>args<TAB>expected_status<TAB>expected_reason<TAB>features
```

Rules:

- `id` is `-` for a one-case package, otherwise a kebab-case suffix.
- `subject` is the source-level Go function Lean should run.
- `args` is `-` or comma-separated integer arguments.
- `expected_status` is one of `ok`, `panic`, `unsupported`, `stuck`, `error`.
- `expected_reason` is `-` for `ok` and `error`; it is required for `panic`,
  `unsupported`, and `stuck`.
- `features` is a comma-separated list of canonical feature tags.

Derived fields:

- `go_dir` is the directory containing `cases.tsv`.
- `gobra_json` is `artifacts/coverage/work/<full-id>/main.go.internal.json`.
- Result logs are under `artifacts/coverage/results/<full-id>/`.

This removes the current manifest duplication where ids, source directories,
and artifact paths can drift independently.

## Go Source Contract

Every executable package contains `main.go`.

Each row names a subject function. The subject function contains the behavior
under test. Lean executes that function directly after frontend lowering.

For `ok` cases, `main` prints one canonical JSON observation after calling the
subject. For `panic` cases, `main` calls the subject and lets the Go process
panic; the top-level runner normalizes the real process failure into a
canonical panic observation after checking the panic text contains
`expected_reason`.

Grouped packages should use a small `main` dispatcher keyed by the row id:

```go
func main() {
	switch os.Args[1] {
	case "ascii":
		printInt(ascii())
	case "utf8-leading-byte":
		printInt(utf8LeadingByte())
	default:
		panic("unknown case")
	}
}
```

The dispatcher is observation plumbing only. It must not contain feature logic.

## Feature Tags

Feature tags should be controlled vocabulary, not free text. Initial top-level
tags:

```text
arrays
assignment
bools
calls
channels
comparability
concurrency
constants
control_flow
defer
errors
fields
functions
generics
interfaces
maps
methods
nil
panic
pointers
range
returns
scoping
slices
strings
structs
types
unsafe
zero_values
```

Secondary tags are allowed when they are stable and useful in reports, for
example `append`, `copy`, `aliasing`, `full_slice`, `unicode`, `iota`,
`evaluation_order`, `overflow`, and `comma_ok`.

The runner should warn or fail on unknown tags once `tags.tsv` exists.

## Runner UX

Target commands:

```sh
scripts/coverage list
scripts/coverage list --tag slices
scripts/coverage run
scripts/coverage run slices/append/overlap
scripts/coverage run --prefix slices/
scripts/coverage run --tag maps --tag nil
scripts/coverage run --status panic
scripts/coverage run --last-failed
scripts/coverage report
scripts/coverage report --by tag
scripts/coverage report --by stage
```

`scripts/diff-one <id> ...` should remain as a compatibility alias for exact
ids. The main implementation should be a single coverage driver that builds a
temporary normalized manifest and delegates to the existing differential
runner.

## Reports

The runner should continue printing one line per case:

```text
PASS<TAB><id><TAB><features>
FAIL<TAB><id><TAB><features><TAB>stage=<stage><TAB>detail=<detail>
```

It should also write machine-readable results:

```text
artifacts/coverage/latest.tsv
artifacts/coverage/latest.json
```

Summary reports should include:

- total cases, pass count, fail count;
- pass/fail by feature tag;
- fail count by stage;
- expected status distribution;
- top red cases by stable id.

This makes it reasonable to keep a large suite where many features are still
red, because the red cases are categorized and measurable.

## Migration Plan

1. Add a manifest generator that reads `cases.tsv` files and emits the current
   normalized manifest format.
2. Move `Corpus/coverage/litmus` to `Corpus/coverage/exec` by area in small
   batches.
3. Derive artifact paths from ids instead of storing them in case metadata.
4. Add filtering by exact id, prefix, tag, expected status, and previous
   failure stage.
5. Add `artifacts/coverage/latest.{tsv,json}` reports.
6. Add controlled `tags.tsv` validation.
7. Expand the corpus aggressively from `Corpus/challenges/semantic-edges`.

The current central `manifest.tsv` should remain until the generator can
round-trip the existing suite without changing pass/fail classifications.
