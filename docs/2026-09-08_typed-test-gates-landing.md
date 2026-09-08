# Typed-contract CI gates — implementation and review record

[AGENT] 2026-09-08. IN PROGRESS under the [user-authorized
charter](2026-09-08_typed-test-gates-charter.md). Branch
`land/typed-test-gates`, base main `dc83782d`; no merge or push.
The user supplies the adversarial review after this implementation handoff.

## Problem and implemented boundary

The typed semantics and its theorems already build on main. However, CI's
test import closure reached 31 of 35 top-level Lean test modules, missing
`Tests.BooleanTyping`, `Tests.BooleanTypingAudit`, `Tests.BooleanInvariant`
and `Tests.BooleanSafetyAudit`. Seven declared typed libraries lacked named
CI steps; five were reached indirectly through other tests. L1/L2's split
left the supporting gate scripts behind. This is master-plan-v2 T8/W3/N6.

Seven restored scripts now build and freshly elaborate the landed modules,
then invoke their complete post-import audits. The archived scripts are a
source quarry only. None of `GoLean/`, `Tests/`, the production frontend or
the baselines has changed in this implementation. In particular, L1's
interface audit and L3's recovery-terminal contracts remain exactly those
on main; the existing interface and terminal gates still execute in CI.

`scripts/ci-libraries.json` maps all 14 libraries to 13 named CI steps.
`EvalTests` gives `Tests.GoCoreEval` library ownership alongside its existing
executable role. The coverage check rejects unowned Lean modules anywhere
under `Tests/`, absent/duplicate ownership, missing sources, unregistered
libraries, duplicate registry keys, aliases, and unsupported Lake source/glob
forms. There is no allowlist. Each step executes its registered Lake targets
and records the actual exit code in a fresh invocation directory. Libraries
explicitly build their `:leanArts` facet, so an empty `defaultFacets` cannot
turn a library build into a no-op. The final
check requires every successful receipt from that invocation and detects
configuration changes during the run. A registry entry alone is not enough:
skipped steps, failed builds/checks and copied old receipts all fail.

## Source selection and compatibility

[AGENT] Selected 21 paths from committed `typed-consumer-sprint` at
`7edc298f`: seven scripts, seven audit wrappers, three fixture tools and
four contract notes already cited by `GoLean/Interface.lean`. Blob identities
are in the [evidence index](evidence/2026-09-08_typed-test-gates/README.md).
Restored scripts preserve their existing full/`--lean-only` interfaces;
CI invokes the static forms for Boolean/recovery typing. Full native fixture
comparisons and functional controls are separately validated in this lane.
The optional recovery fixture check reads the existing customer artifact;
it does not build or import Iris into CI.

The four Boolean modules absent from CI are byte-identical to the sprint.
The supporting modules explicitly cited in the restored Boolean-program,
recovery-static and recovery-entry notes also match their committed sources;
`RecoveryInvariant` matches the control note's source. Historical validation
counts and source references are labeled as such. Entry/control notes point
to L3's subsequent terminal restatement rather than reviving earlier renderer
claims. No theorem statement adaptation has been necessary.

## Audit controls and scratch

[AGENT] The seven original concrete poison lists remain in their family
wrappers: 3 Boolean typing, 6 Boolean runtime, 5 recovery typing, 8 recovery
storage, 9 recovery setup, 17 recovery control and 6 abort observation —
54 controls total. Every family contains both a private axiom and a private
proof hole. Each mutation is compiled first, then rejected by the importing
audit with both the declaration name and expected forbidden axiom in the
diagnostic. Each family finishes with an unpoisoned import to detect leakage,
including leakage from its last control. These are separate from the existing
interface, admission, declaration and recovery-terminal negative controls.

`tools/typed_audit.py` shares the reviewed I1 overlay mechanism. It excludes
the mutated module and all its sidecars from symlinks before compilation.
Dependencies are aliases; new source/artifacts are private files. Both shell
gates and audits allocate below this worktree's `.tmp` regardless of foreign
TMPDIR, delete their newly allocated scratch on success, and retain failure
logs/reasons on failure. No earlier scratch or other worktree is cleaned.
Fresh elaboration retains Lake's `--setup` metadata and writes this worktree's
actual oleans, preserving the native initializer names (the L3/I1 remedy).

Eighteen coverage self-tests exercise ownership, real target arguments,
missing/failed/stale/mismatched receipts, source aliases and changes during
the invocation. Five scratch controls exercise foreign TMPDIR, success-only
cleanup, retained subprocess output/reason, all-sidecar write isolation,
missing real build artifacts and the shell's failed-command reason. The
unit controls do not replace the 54 actually compiled Lean negatives.

## Author finding F1 — a bare library build can do nothing

[AGENT] The pinned Lake 4.32.2 `LeanLibConfig.defaultFacets` permits `[]`.
A three-line fixture module with `def broken : Nat := "not a natural number"`
and an empty default-facet list reproduced the bypass: bare
`lake build FixtureTests` exited 0, while `lake build FixtureTests:leanArts`
exited 1 with the named source type error. Both ran capped in an isolated
project. The runner now requests `:leanArts` for every library, including
the existing groups. A standing test uses the actual runner and compiler
and requires the source type-error diagnostic, so a missing tool or unrelated
failure cannot count as the expected rejection. No main-side theorem changes.
Logs: `artifacts/typed-test-gates/facet-{bare,explicit}.log`; structured
control record: `facet-control.json` in that directory.

## Validation and cost

[AGENT] Initial focused proof gates all pass against main without changing
any theorem or semantic source. The six gates after Boolean typing took
183.960 seconds together on a warm copied build cache, 32 GiB cap and three
Lean threads; this is a preliminary standalone measurement, not CI overhead.
The full native fixture checks and integrated full `--diff` runs are next.
Per-step receipts report build, check and combined seconds, and CI reports
total wall time. Final measurements and source-bound results will replace
this in-progress status before the user review handoff. Cost acceptance is
reserved to the user; no timing is silently treated as approved.

Hard boundary checks compare against `dc83782d`: no `GoLean/` changes, no
`Tests/` statement changes (currently no changes at all), and unchanged
3,654-row executable / 394-row negative baselines. Full gates use the
box-wide lock, the verified cap, three Lean threads and twelve differential
workers. Cached slow-row certification is labeled; neither merge-protocol
5a path changes in this lane. Full logs live in ignored
`artifacts/typed-test-gates/`; tracked evidence stays compact.

[AGENT] Initial full candidate `--diff` gate PASS, actual exit 0, at frozen
index tree `91148c133529a557b14b15998c13901899d83c83` over `03570a9f`.
All 3,654 executable / 394 negative results and allowed stages match;
207 eval PASS, 54 new compiled controls, two unchanged reconciler findings
(C13/C5), zero HIGH. The new steps took 267.953 seconds in total; the full
gate took 956.046 seconds externally. This records the first candidate,
before F1's explicit-facet correction, and does not certify that correction.

The F1 correction and auxiliary timing output are now covered by 18 coverage
and five scratch controls. Next: the complete corrected CI sequence in fast
mode (reusing the initial run's differential records against byte-identical
semantic/frontend sources), then a fresh full `--diff` at the clean committed
implementation. This separates new gate integration from fresh runtime
certification, rather than relabeling cached results. Auxiliary coverage
initialization, self-tests, verification and cleanup have their own measured
times in addition to the seven named proof/audit steps.

[AGENT] Corrected candidate fast gate PASS, actual exit 0, at frozen index
tree `274dbb7d8bc2d3fdea23cc1125985b882f5d7aaa` over `03570a9f`.
All 13 named steps, 54 compiled audit controls, 18 coverage and five scratch
controls passed. The seven new gates took 261.439 seconds; coverage actions
took 0.397 seconds combined; total fast CI took 457.165 seconds externally.
These measurements use a warm cache and fresh poison compilation. The
native/negative results are the initial full run's records, compared again
against unchanged baselines; this was not a new corpus run. Evidence:
[candidate fast gate](evidence/2026-09-08_typed-test-gates/candidate-fast-gate.txt)
and [measurements](evidence/2026-09-08_typed-test-gates/candidate-fast-measurements.json).
Only these documentation/evidence additions follow that frozen candidate.
The implementation commit and its clean full `--diff` run are next.
