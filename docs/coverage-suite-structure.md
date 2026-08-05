# Coverage Suite Structure

This document describes the target structure for a large Go differential
coverage suite. The goal is to make adding tests cheap, make failures explicit,
and avoid a central manifest becoming a second source of truth.

## Goals

- Every executable test uses ordinary canonical Go source.
- The Go and Lean paths consume the same source file.
- Expected Go runtime behavior is classified per case as `ok` or `panic`.
  Lean `unsupported`, `stuck`, and `error` observations are failures, not
  expected conformance outcomes.
- Static invalid-Go cases live in a separate negative lane.
- Test ids, source paths, and artifact paths are derived mechanically.
- Subsets are runnable by id, directory prefix, feature tag, expected status,
  or last failure stage.
- Reports summarize both individual red/green cases and feature coverage.
- Gaps are exposed, not hidden. Unsupported features, frontend failures,
  semantic stuckness, and differential mismatches stay red in the default
  report. Known-gap annotations may categorize work, but they must not make the
  main conformance lane green.

## Directory Layout

Current executable layout:

```text
Corpus/coverage/
  tags.tsv
  exec/
    <area>/
      <case>/
        main.go
        cases.tsv
  negative/
    compile/
      <area>/
        <case>/
          main.go
          case.tsv
  suites/
    smoke.lst
    frontend.lst
    semantics.lst
  README.md
```

Deeper grouping such as `exec/<area>/<feature>/<case>` is allowed when it makes
the suite easier to browse. The id is always derived from the relative path
under `exec`.

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
path and row id syntax, duplicate ids, subject syntax, integer args, and
expected reason policy.

Columns:

```text
id<TAB>subject<TAB>args<TAB>expected_status<TAB>expected_reason<TAB>features
```

Optional lane columns (membership lane, arc slice 3,
`docs/2026-08-04_membership-lane-design.md`) may follow `features`:

```text
...<TAB>lane<TAB>why<TAB>params
```

- `lane` is `strict` (the default when the columns are absent or `-`) or
  `membership`. Membership cases are oracled by SET MEMBERSHIP — every
  `go run` sample must lie in the machine-enumerated observation set
  (`golean coverage-observations`) — instead of equality against one run.
- `why` is mandatory free text for `membership` (which observable depends
  on which consumption site); it must be `-` for `strict`.
- `params` is comma-separated `key=value` settings: `width` (enumerator
  pick alphabet `[0,B)`; REQUIRED for membership rows, no silent default —
  author-asserted to cover every consumption-site bound in the case, with
  the bound argued in `why`; the enumerator's alias-guard ladder is a
  heuristic cross-check of the assertion, not a proof), `sites` (max
  consumption depth, default 8), `cap` (max distinct observations,
  default 64), `samples` (Go-side sample count, default 5; `samples=1` is
  the version-tracking mode for features Go decides deterministically per
  toolchain), `work` (enumerator work cap, default 200000).
- Fail-closed both ways: `lane=membership` requires the `nondet` feature
  tag and a `why`; a `nondet`-tagged case requires `lane=membership`; a
  membership case whose enumerated set is a singleton fails ("belongs in
  the strict lane"); a strict case that varies across the adversarial
  choice streams keeps failing at stage `nondet`.

Rules:

- `id` is `-` for a one-case package, otherwise a kebab-case suffix.
- `subject` is the source-level Go function Lean should run.
- `args` is `-` or comma-separated integer arguments.
- `expected_status` is one of `ok` or `panic`.
- `expected_reason` is `-` for `ok`; it is required for `panic`.
- Frontend export failures, Lean `unsupported`, Lean `stuck`, Lean `error`, and
  differential mismatches are reported as red cases. They are not encoded as
  expected statuses in executable metadata.
- `features` is a comma-separated list of canonical feature tags.
- `ok` subjects must return at least one observable value. Use a checksum or
  deterministic summary for mutation-heavy tests.

Derived fields:

- `go_dir` is the directory containing `cases.tsv`.
- Frontend artifact paths are adapter-owned. For the current Gobra adapter this
  is `artifacts/coverage/work/<full-id>/main.go.internal.json`, but the
  normalized manifest does not store that path.
- Result logs are under `artifacts/coverage/results/<full-id>/`.

This removes manifest duplication where ids, source directories, and
frontend-specific artifact paths can drift independently.

## Go Source Contract

Every executable package contains `main.go`.

Each row names a subject function. The subject function contains the behavior
under test. Lean executes that function directly after frontend lowering.

For Go execution, the runner generates a temporary harness from metadata rather
than trusting a handwritten `main`. The generator strips the source `main`,
copies every non-test Go file in the package into the temporary directory,
calls the named subject with the metadata integer args, and encodes the return
values as schema-versioned observations. For `panic` cases, it lets the process
panic; the runner extracts the actual Go panic line and compares that
normalized observation against Lean.

Handwritten `main` functions may remain useful for `go run` debugging, but they
are not part of the differential contract.

The corpus unit is a Go package directory. The current Gobra frontend can only
export a single `main.go`; multi-file executable packages therefore fail red in
the `frontend-export` stage until a package-aware frontend adapter exists.

## Feature Tags

Feature tags are controlled by `Corpus/coverage/tags.tsv`. The manifest
generator rejects unknown tags, malformed tags, and duplicate entries in the
vocabulary. Add tags intentionally; do not use ad hoc spellings in case files.
The `nondet` tag marks membership-lane cases (it was reserved for a future
relation-style oracle until 2026-08-05, when the membership lane landed):
a `nondet`-tagged executable case must declare `lane=membership`, and vice
versa. The compile-negative lane rejects the tag outright.

## Runner UX

Target commands:

```sh
scripts/coverage list
scripts/coverage list --tag slices
scripts/coverage run
scripts/coverage run slices/append-overlap
scripts/coverage run --prefix slices/
scripts/coverage run --tag maps --tag nil
scripts/coverage run --status panic
scripts/coverage run --last-failed
scripts/coverage negative
scripts/coverage negative --id slices/slice-compare
scripts/coverage negative --tag compile_error
scripts/coverage report
scripts/coverage report --full
scripts/coverage report --by tag
scripts/coverage report --by stage
```

`scripts/diff-one <id> ...` should remain as a compatibility alias for exact
ids. The main implementation should be a single coverage driver that builds a
temporary normalized manifest and delegates to the existing differential
runner.
`scripts/coverage all` runs both executable and compile-negative lanes and
rejects filters, because executable and negative ids live in separate
namespaces.

## Reports

The runner should continue printing one line per case:

```text
PASS<TAB><id><TAB><features>
FAIL<TAB><id><TAB><features><TAB>stage=<stage><TAB>detail=<detail>
```

It also writes machine-readable results:

```text
artifacts/coverage/latest.tsv
artifacts/coverage/latest.meta.tsv
```

Filtered runs still write `latest.tsv`, but the metadata records `full_run`,
filters, frontend, manifest hash, manifest case count, total corpus case count,
git commit, and dirty flag.
Reports warn when `latest.tsv` is not a full corpus run. Full runs also update
`artifacts/coverage/latest-full.tsv`, which can be summarized with
`scripts/coverage report --full`; full reports are checked against the current
generated full manifest so stale reports cannot look authoritative.

Summary reports should include:

- total cases, pass count, fail count;
- pass/fail by feature tag;
- fail count by stage;
- expected status distribution;
- top red cases by stable id.

This makes it reasonable to keep a large suite where many features are still
red, because the red cases are categorized and measurable.

The default executable lane is a conformance signal, not an expected-failure
test suite. A case that does not match Go remains a failure even when the
failure is understood.

## Migration Plan

1. Add JSON output next to `artifacts/coverage/latest.tsv`.
2. Expand the corpus aggressively from `Corpus/challenges/semantic-edges`.
3. Add optional suite files under `Corpus/coverage/suites/` for curated subsets.

The central executable and compile-negative manifests have been removed.
Generated normalized manifests are an implementation detail of the current
frontend/Lean and Go-negative runners.
