# Panic renderer repair evidence

Author-run evidence, 2026-09-06 UTC, from the isolated
`typed-panic-rendering` worktree based on
`5158589a83df9e54f5763f684286d35acb6b5afa`.
See [the repair note](../../2026-09-06_panic-rendering-repair.md) for the
precise claim and remaining O2 obligations. These files are not an
independent implementation review.

- `red.tsv` and `red.meta.tsv`: all ten repair cases reach Lean and refuse
  on the base renderer, before editing runtime source. The working tree was
  dirty because the nine new native fixtures had already been added.
- `kernel-red.log`: the six positive declarations in
  `Tests/PanicRendering.lean` fail kernel checking against that old renderer;
  its two refusal controls do not fail.
- `focused-green.tsv` and `focused-green.meta.tsv`: the same ten cases,
  plus four existing defined-payload/recovery controls, pass after repair.
  Every row has completed the harness's default oracle-invariance checks.
- `oracle-bytes.json`: actual recorded Go stdout/stderr bytes for the ten
  repair cases from the focused green run. Its text field is extracted from
  the first `panic: ` line; its hex fields preserve the full raw report.
  This is Go evidence, not a second independent Lean runner.
- `coherence-build.log`: rebuilding `GoLean.Interface` recompiles Machine,
  MachineSound, MultiSound, and the trace/coherence modules successfully.
- `interface.log`: all eight new kernel declarations elaborate, the
  post-import dependency audit passes, and five compiled poison controls
  are then rejected. The fresh standalone kernel command also exited 0
  with empty stdout (`artifacts/panic-rendering/kernel-green.log`).
- `source.SHA256SUMS`: tested source files, relative to the worktree root.
  Check with `sha256sum -c docs/evidence/2026-09-06_panic-rendering/source.SHA256SUMS`.
- `control-bytes.go`, `ControlBytes.lean`, `control-bytes-observer.json`:
  separate, pre-existing valid-UTF-8 control-byte transport defect. The Go
  payload and kernel-rendered String retain NUL and byte `01`; the shell
  drops NUL and constructs invalid JSON for byte `01`. These probes are not
  counted among this repair's differential greens. The JSON record states
  exactly which existing harness functions and shell step were exercised.

- `full.tsv`, `full.meta.tsv`: the complete 3607-case run, 3363 PASS /
  244 FAIL. Some optional metadata scope fields say `unknown`; completeness
  is independently established by all 3607 current manifest rows, their
  recorded/current matching SHA256
  `2e04e8e0401480118c6aa96f8c3041f79b8e5c50954032e4adcabacbdf94444e`,
  and the full comparison (not by rewriting those metadata fields).
- `initial-drift.log`: exactly one existing FAIL→PASS and nine added PASS
  rows against the unchanged baseline. `reconciled-drift.log`: the same
  full table matches the narrowly updated baseline.
- `ci-initial.log` and `setup-deps.log`: initial CI retained its early
  missing-reference-checkout failures and expected drift. Pinned isolated
  dependencies were restored before the differential started. This log is
  not advertised as passing CI.

- `ci-final.log`: final ordinary CI passed, exit 0. It judges the same full
  differential evidence and rechecks the setup-dependent gates; runtime,
  fixtures and tests remain at the recorded source hashes.
- `reconcile-final.log`: the subsequent record-only coverage-ledger update
  removes the two arithmetic warnings introduced by this repair. Two
  unrelated MEDIUM record findings remain. No runtime or test changed.
- `SHA256SUMS`: immutable evidence-file hashes, relative to this directory.
  The independent integrator review is retained separately on its branch
  under `docs/evidence/2026-09-06_panic-rendering-review/`.
All paths in recorded metadata are original local paths; the checks do not
depend on those temporary directory names.

Commands, from the worktree root:

```sh
export GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2
scripts/capped lake build GoLean.Interface
scripts/capped lake env lean Tests/PanicRendering.lean
scripts/capped bash scripts/check-interface
```

The focused red and green commands are:

```sh
GOLEAN_COVERAGE_ARTIFACTS=artifacts/panic-rendering/red scripts/capped scripts/diff-one \
  panic-recover/panic-newline-abort \
  panic-recover/panic-text/unicode-two \
  panic-recover/panic-text/unicode-three \
  panic-recover/panic-text/unicode-four \
  panic-recover/panic-text/unicode-mixed \
  panic-recover/panic-text/unicode-newline \
  panic-recover/panic-text/trailing-newline \
  panic-recover/panic-text/recovered-newline \
  panic-recover/panic-text/recovered-unicode \
  panic-recover/panic-text/output-prefix

GOLEAN_COVERAGE_ARTIFACTS=artifacts/panic-rendering/green scripts/capped scripts/diff-one \
  panic-recover/panic-newline-abort \
  panic-recover/panic-text/unicode-two \
  panic-recover/panic-text/unicode-three \
  panic-recover/panic-text/unicode-four \
  panic-recover/panic-text/unicode-mixed \
  panic-recover/panic-text/unicode-newline \
  panic-recover/panic-text/trailing-newline \
  panic-recover/panic-text/recovered-newline \
  panic-recover/panic-text/recovered-unicode \
  panic-recover/panic-text/output-prefix \
  panic-recover/panic-defined-payload-methods/plain \
  panic-recover/panic-defined-payload-methods/error-forced-half \
  panic-recover/panic-defined-payload-methods/stringer-forced-half \
  panic-recover/repanic-same-value-abort/forced-half
```

To reproduce the red result, use an isolated checkout of the recorded base
with only this change's native fixture directory and `Tests/PanicRendering.lean`
copied into it; build the base there before elaborating the test. Running the
red command on the repaired source is expected to pass instead.

The required full command is `scripts/capped scripts/ci --diff`.
It preserves the project's existing distinction between freshly run cases
and the `tier=slow` cases checked against their tracked certified records;
this repair does not claim a fresh `--slow` re-enumeration.
