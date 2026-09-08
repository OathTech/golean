# Typed-contract CI gates — implementation and review record

[AGENT] 2026-09-08. BRANCH COMPLETE under the [user-authorized
charter](2026-09-08_typed-test-gates-charter.md). Branch
`land/typed-test-gates`, base main `dc83782d`; no merge or push.
Clean implementation `76f81a7d` passes full capped `--diff` CI. Only
documentation/evidence updates follow that validated source. The user's
adversarial review and measured-cost acceptance are pending.

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

[AGENT] The clean implementation `76f81a7d807a9b619be909ccb76e7695966fba9f`
passed `scripts/capped scripts/ci --diff`, actual exit 0. Native and negative
metadata both identify this commit with `git_dirty=false` and the pinned
`go1.26.5`, with no toolchain drift. The 3,654 executable rows reproduce
3,403 PASS / 251 expected FAIL; all 394 negative cases pass. Results and
allowed stages match the unchanged baselines. All 207 eval tests, 54 compiled
poisons, 18 coverage controls and five scratch controls pass. The existing
reconciler reports C13/C5, zero HIGH; those report-only findings are unchanged.

Evidence: [clean gate summary](evidence/2026-09-08_typed-test-gates/committed-gate.txt)
and [source-bound measurements](evidence/2026-09-08_typed-test-gates/committed-measurements.json).
Measurements use the box-wide lock, a 32 GiB cap, three Lean threads and
twelve differential workers. The worktree build cache is warm; every poison
module is freshly compiled. The seven new named steps include their explicit
library builds and checks:

| New CI step | Seconds |
|---|---:|
| Boolean typing | 79.069 |
| Boolean runtime | 30.225 |
| Recovery typing | 49.306 |
| Recovery storage | 27.361 |
| Recovery setup | 29.409 |
| Recovery control | 28.915 |
| Abort observation | 22.679 |
| **Seven steps combined** | **266.964** |
| Coverage initialization, self-tests, verification and cleanup | 0.416 |
| **New steps plus coverage actions** | **267.380** |
| **Entire full CI, external wall clock** | **911.316** |

The new work therefore occupies about **4m 27s** in a **15m 11s** full run.
These are measured step durations, not a paired before/after performance
comparison or a cold-cache benchmark. Coverage helper timings exclude Python
process startup; total CI wall time includes it. Per-step build/check splits
and individual auxiliary action times are in the JSON record. Cost acceptance
remains the user's decision. This `--diff` run visibly reuses tracked slow-row
certification; it makes no fresh `--slow` claim. Neither merge-protocol 5a
path changes. `GoLean/`, `Tests/`, the production frontend and baselines are
byte-identical to base `dc83782d`.

The optional full native fixture checks also pass: Boolean 3/3 and recovery
5/5, including complete artifact equality, the named `panic(true)` profile
refusal, and functional input/defer-order/directness controls. Their separate
[fixture record](evidence/2026-09-08_typed-test-gates/native-fixture-checks.json)
identifies the dirty candidate over `03570a9f`, with the semantic, Tests and
production frontend sources unchanged. This is separately scoped evidence;
ordinary CI uses the two `--lean-only` forms. These optional checks took
87.377 and 57.840 seconds respectively and are excluded from the CI totals.

Earlier validation is retained with its actual source and mode:

- Initial full candidate: frozen tree `91148c13` over `03570a9f`, exit 0,
  3,654 / 394 baseline rows match; full gate 956.046 seconds. This precedes
  F1's explicit-facet correction and does not certify that correction.
- Corrected candidate fast CI: frozen tree `274dbb7d` over `03570a9f`,
  exit 0; seven new gates 261.439 seconds, coverage actions 0.397 seconds,
  full fast gate 457.165 seconds. It reuses the first run's corpus records.
- The clean committed full run above certifies the final implementation;
  the following commit changes only documentation and compact evidence.

Full logs and generated fixtures remain ignored under `artifacts/`.
All successful new audit scratch and the CI receipt directory were removed;
the measurement record includes each family's owned regular-file bytes at
cleanup, excluding symlinked dependencies and filesystem metadata. This
landing changes the seven restored families' scratch lifecycle; existing
interface/admission/terminal helpers retain their landed behavior.

[AGENT] Completion-record checks pass: staged changes are documentation only,
local links resolve, clean-source/log/baseline hashes and timing sums verify,
and protected source paths have no delta. The evidence-size gate passes with
zero new exceptions; this lane's evidence directory is 25,012 bytes. The
AGENTS alias gate and `git diff --check` also pass.

## User review handoff

[AGENT] The mandatory adversarial-review ask is posed to the user, who
reserved this review in the authorization. No independent verdict is claimed.
Suggested review scope:

- Compare `dc83782d..land/typed-test-gates`: no semantic, Tests, production
  frontend or baseline delta; current L1 interface and L3 terminal statements
  and their gates remain intact.
- Challenge bidirectional coverage: nested/untracked Tests modules, source
  aliases, missing mappings or steps, failed builds/checks, stale receipts,
  configuration changes and empty `defaultFacets` must fail closed.
- Check that all 54 mutations compile, then fail their importing audits by
  declaration and forbidden-axiom name, followed by each family's clean import.
- Check symlink/sidecar isolation, foreign TMPDIR, success cleanup and retained
  failure output/reason, without deleting pre-existing scratch.
- Accept or revise the measured CI cost above.

The branch is committed and ready for that review. Merge requires a subsequent
explicit sign-off after the review; no merge or push has occurred.
