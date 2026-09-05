# Independent adversarial review: BUG-103 array value conversion

[AGENT], 2026-09-05. Reviewed commit
`7b7bc42c3f77154099ccbb3c6f6a302a8d1987d4`, branch
`bug103-array-conversion`, against base
`8db2d6dad165393f4d3cdffee63b8e7d624f39e6`.

## Verdict

**PASS for the bounded BUG-103 change. No blocking or non-blocking defect
introduced by this commit was found.** The implementation is suitable for
integration subject to the project's explicit merge authorization and any
required checks after integration. This review is not merge authorization.

All changed runtime/proof/test files, the fixture and baseline changes, and
the design, handoff, ledger, bug record and evidence were inspected. Source
and evidence hashes were independently checked. The full expensive corpus
and compile-negative execution were not rerun; their sealed records were
checked against the committed source and baselines.

## Semantic and proof assessment

`GoLean/GoCore/Ops.lean:1507` selects only an array operand and a resolved
array target, checks length through the existing normalizer and recursively
normalizes the copied value. It does not allocate, mutate the state, or
consume choices. Persistent array/struct values provide independent value
updates, while contained pointer, slice, map, function and channel references
retain their identities. The new arm does not shadow the separate slice
conversion cases at lines 1509 and 1515.

`GoLean/GoCore/Machine.lean:4048` already gives `Step.strictApply` the total
`applyStrictOp` premise used by execution, including its error/result delivery.
The new case therefore does not create an evaluator-only transition or a
second semantic definition. `GoLean/GoCore/StateWf.lean:1360` discharges the
array result's location bound through `normalizeValueForTy_locSup`; the
existing preservation and coherence theorems still build. A separate import
probe found only the standard `propext`, `Quot.sound`, and (where used)
`Classical.choice` dependencies for the conversion bound, normalization
bound, `Step.preserves_wf`, `stepFn_sound`, and `step_complete`.

The pinned spec checkout is exactly
`c19862e5f8415b4f24b189d065ed739517c548ba`; the installed oracle reports
`go1.26.5`. The source rules at `doc/go_spec.html` Conversions and Type_identity
support the admitted array conversions. The implementation's documented
boundary matters: array values carry no source type, so normalization is not
an admission judgment. For example, the positive malformed-IR test at
`Tests/GoCoreEval.lean:2203` deliberately accepts and narrows integer elements
that Go would not admit as an array conversion. Scalar fallback validation
is also incomplete. This is explicitly recorded existing typed-admission
debt, not a theorem that arbitrary GoCore input is valid Go.

## Reproduced validation

All Lean/Lake commands below used `scripts/capped` with
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3`.

- `lake build`: succeeds, 62 jobs, using the existing independent local cache.
- `lake build gocore-eval-tests`, then the executable: all 202 checks pass.
- `lake env lean .tmp/bug103-review.KMnRI4/ProofCheck.lean`: the five theorem
  axiom-dependency checks described above pass.
- `scripts/diff-one` with the 23 IDs in the sealed `focused.tsv`: 22 PASS,
  one unchanged FR-10 successful slice-conversion refusal. All six BUG-103
  cases pass. The overall command exits 1 because that known refusal is
  still a FAIL; it was not counted as conformance success.
- Five additional native differential probes: **5/5 PASS**, covering named
  targets and aliases with boxed type identity; interface-array elements
  with typed nil and a dynamic named array; map/function/channel references;
  recursively defined array pointers; and zero-length arrays of functions.
  These runs also use the harness's ordinary oracle-invariance checks.
- An additional array conversion with differently tagged anonymous struct
  elements fails at `frontend-export` with the existing FR-13 quarantine,
  `anonymous non-empty struct type`. This is a frontier control, not a
  conformance pass or a newly introduced failure.
- `scripts/coverage-baseline-diff --full` on sealed `full.tsv`: all 3598
  records match. The same check on the fresh focused result matches all 23.
  The negative baseline comparison matches all 394 sealed negative records.
- Independently derived baseline delta: exactly one existing FAIL to PASS
  (`structs/decl-order-reversed/conversion-array-target`), five added PASS
  entries, no removed entries or other result/stage changes. The unchanged
  `channels/select-select/beside-loop` stage alternative is honored rather
  than mistaken for raw string drift.
- All 70 semantic-input hashes, their aggregate fingerprint, and all 31
  changed-file/evidence hashes match. `git diff --check` passes, and the
  reviewed worktree remains clean.

## Limits and follow-up

No source fix is requested by this review. The additional five passing probes
are useful candidates for a later corpus expansion; they are scratch review
evidence and are not silently included in the 3598-case baseline count.

Typed admission remains necessary before the customer can make claims about
arbitrary machine input. Successful slice conversions remain FR-10, and
struct-tag/anonymous-struct support remains FR-13. The latter also means this
review does not endorse a claim of complete array-conversion coverage.
No new concurrent adequacy or full Go semantic equivalence is established.
The recorded ordinary full run retains one cached slow-tier certification;
this review does not recertify it or re-execute the negative corpus.

An optional standalone Go execution of the tagged-struct frontier control
could not initialize the AGENTS-prescribed `/private/tmp/go-build` cache
because nono denies creating `/private` in this session. That failure is
preserved as `tagged-go.log`; no successful direct Go result is claimed for
that optional command. All five additional supported differential probes
ran successfully using the harness's permitted cache. The nono sandbox
skill was consulted; no permissions, profiles or live sources were changed.

Scratch review files are under `.tmp/bug103-review.KMnRI4/`.
Differential result/meta records are under `artifacts/bug103-adversarial/`,
`artifacts/bug103-adversarial-extra/`, and
`artifacts/bug103-adversarial-tagged/`. Original sealed implementation
evidence was left unchanged.

## Coordinator preservation note

[AGENT] The report above is the independent `bug103_adversarial` review,
recorded after the [USER] authorized it. Its logs, probe sources and fresh
result metadata are preserved in
`docs/evidence/2026-09-05_bug103-array-conversion-review/`; the README there
maps the original scratch paths and explains reproduction. This review note
updates the status of the original handoff without rewriting any file bound
by the sealed implementation evidence. No source fix was requested or made.
Main remains unchanged, and merge/push authorization is still separate.
