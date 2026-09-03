# diff-coverage timeouts were cause-blind on four paths — red-first record (2026-09-03)

[AGENT] Lane-tooling fix slice, branch `timeout-cause` off main @
b5abacc1. The defect was found by the noodler lane and confirmed by
its auditor; this dir is the fix lane's own first-hand reproduction.
Consuming docs: `docs/operational-lessons.md` ("A killed command has
decided nothing"), the fixture comment at `scripts/test-lane-validation`
T1-T4, the `run_with_timeout` / `obs_eq` comments in
`scripts/diff-coverage`, and the timeout-reporting convention in
`docs/coverage-suite-structure.md` (Reports).

## The defect (pre-fix `scripts/diff-coverage`, main @ b5abacc1)

`run_with_timeout` (line 79) exits 124 silently. It was fail-CLOSED
everywhere (a timeout never passed), but four consumers read the
killed command's EMPTY capture as a verdict:

| path | line | reported (wrong or empty cause) |
|---|---|---|
| strict-lane Lean run | 741-757 | `lean-observation` — `expected status ok, got ` (empty; `lean_status` read only at 758) |
| oracle-invariance re-run | 824-826 | `nondet` — "observation varies with iteration order … variant=" (empty) |
| membership driver-coupling pin | 1283-1300 | `membership` — "… NOT in the enumerated set (copied-driver drift, or …): " (empty) |
| membership Go-sample loop | 1308-1323 | `membership` — "Go observation is NOT in the machine's enumerated set (the too-narrow soundness alarm)" |

Three sibling paths already did it right (confluent :686-695, racy
:803-808, membership enumerator :1224-1230: "enumerator TIMED OUT
after Ns …"). Every other consumer (lake build, harness generation,
both native exports, the Go oracle in both lanes, and every boolean
`lean observation-eq`) was likewise cause-blind and is fixed in the
same slice.

## The fix (cause-naming only)

No budget value, pass criterion, stage word, or baseline expectation
changes. Every consumer tests exit 124 BEFORE reading the capture and
reports at the stage of the check that could not complete with a
reason carrying `TIMED OUT after <N>s (<KNOB>)` and what was NOT
established — the vocabulary the three already-correct paths used.
The strict Lean run stays at stage `lean-observation` on purpose:
`tools/reconcile-records` FIDELITY_STAGES and the check-bugs ratchet
count that stage; moving it to `lean-run` would have dropped Lean
timeouts out of the untriaged-fidelity surface (a gate weakening).
`run_with_timeout` additionally announces the kill on stderr, so any
future `2>&1` consumer carries the cause even if it forgets the test.

## Red-first fixtures

`scripts/test-lane-validation --with-go` T1-T4 build a FAKE ROOT (a
temp dir whose `scripts/diff-coverage` symlinks the runner under test
and whose `.lake/build/bin/golean` is a shim that delegates to the
real binary except the one call the fixture targets, which `exec
sleep`s past `LEAN_TIMEOUT_SECONDS=1`). The runner gains no
binary-override knob; the shim is reached only through the runner's
own ROOT derivation.

- `red-main-runner.log` — the suite with main's runner (b5abacc1)
  swapped in: T1-T4 FAIL with exactly the four texts above; exit 1.
- `green-fixed-runner.log` — the suite with this branch's runner:
  T1-T4 ok (rows printed), every pre-existing fixture still ok; exit 0.

Re-run: `scripts/test-lane-validation --with-go` (needs go on PATH and
the built `.lake/build/bin/golean`).
