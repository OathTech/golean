# grossmith differential findings — 2026-08-07

Handed over from the grossmith project (generator of small,
outcome-deterministic Go programs for differential conformance testing;
first campaigns against this checkout at `a38e086e`, native frontend,
via `scripts/diff-coverage` with grossmith-written strict-lane manifest
rows). Three items: one machine bug with a minimal repro, one harness
sharp edge traced into `scripts/ci`, one corpus-promotion offer.

## 1. BUG: `++`/`--` on a defined integer type gets stuck in evaluation

Minimal repro (7 lines, well-typed Go, gc-clean; grossmith seed 559
minimized):

```go
package main

type T1 int8

func fuzzSubject() int8 {
	v := T1(5)
	v++
	return int8(v)
}
```

Manifest row (strict lane): `min-incdec\t<dir>\tfuzzSubject\t-\tok\tints\t-\tstrict\t-\t-`

Result:

```
FAIL  min-incdec  ints  lean-observation
expected status ok, got {"message":"mismatched + integer kinds: int8 and int",
                         "schema":"golean-observation-v1","status":"stuck"}
```

Controls run on the same harness invocation path:

- `v := int8(5); v++` (unnamed int8) — **PASS**. The bug needs the
  defined type.
- `v := T1(127); v++` (overflow wrap) — same stuck message, so the
  failure is at the kind level, not overflow handling.

Hypothesis from the message shape: the `IncDec` desugar produces
`v + 1` where the literal's kind resolves to default `int` instead of
the operand's underlying kind when the operand type is a *defined*
type — i.e. the kind lookup at the add site sees `int8` (through the
named type) on the left and `int` (default) on the right. The
plain-`int8` PASS says the desugar itself picks up the operand kind
when the type is unnamed, so the suspect is wherever named types are
resolved to underlying kinds on the literal side of the desugared add.

Note this is **past the frontend gate**: the case exports and the
machine evaluates until the add — so per the fail-closed doctrine this
is a machine/lowering defect, not a `frontend-export` coverage gap.
Suggested corpus case: defined-type inc/dec (both directions, signed
and unsigned underlying, with and without wrap) — it appears the
current corpus never exercises `++` on a named type, or the nightly
would have this red.

## 2. Harness sharp edge: exit 1 is ambiguous, and `scripts/ci` judges a stale `latest.tsv` after a no-publish failure

`scripts/diff-coverage` exits 1 from three places, and only one of them
publishes results:

- FAIL rows exist — `publish_results` ran; results are authoritative.
- `lake build` failed or timed out (`LAKE_BUILD_TIMEOUT_SECONDS`,
  default 120s) — exits **before** `publish_results`; nothing written.
- built `golean` binary missing — same.

`scripts/ci:385-391` explicitly treats exit 0|1 as "differential run
completed (failing-set judged by baseline diff)", and `scripts/ci:429`
then baseline-diffs `artifacts/coverage/latest.tsv` — which, on the
no-publish paths, is the **previous** run's file. Consequence: a lake
timeout inside diff-coverage can produce "same set = no regression"
for a run that never ran. Mitigating factor in practice: `scripts/ci`
lake-builds earlier in the pipeline, so the in-script build usually
succeeds when ci reaches the differential — the timeout path and
standalone invocations are where this bites.

This exact ambiguity caused a (pre-release) wrong-conformance-statement
bug in grossmith, which consumed diff-coverage programmatically and
took exit 1 to mean "results are authoritative". grossmith now defends
by deleting `results.tsv`/meta before each run and requiring the
published meta's `manifest_sha256` to match the manifest it just wrote
(the meta file already carries everything needed — nothing on the
GoLean side had to change).

Suggested fixes, any one of which closes it:

- distinct exit code for the no-publish paths (they are infrastructure,
  not case failures — exit 2 like the other infra exits), and/or
- remove/invalidate `latest.tsv` at the top of the run so a dead run
  leaves no readable results, and/or
- have `scripts/ci` (and other consumers) check the meta
  `manifest_sha256` before judging a results file.

## 3. Corpus promotion offer

Two grossmith-generated cases from the first campaigns are already in
corpus-compatible form (a `main.go` with a `fuzzSubject`, no imports,
gofmt-clean) and classify as visible reds worth pinning:

- the §1 defined-type inc/dec case (above, 7 lines);
- a `frontend-export` gap: call/allocation in a short-circuit operand
  (`frontend-quarantined: call/allocation in short-circuit operand
  (would change evaluation order)`) — an expected coverage gap per the
  baseline doctrine, but apparently not yet represented as a tracked
  case; a corpus pin would make the gap's eventual closure visible as
  a deliberate baseline move.

grossmith can regenerate either deterministically (seed + config are
recorded per case), and can supply more of any construct class on
request — its capability profile for this checkout masks slices/maps
out of observed positions and excludes its observation-event
constructs, everything else generates freely.
