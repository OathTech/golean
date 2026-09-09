# F8 certificate provenance — work charter

[USER] 2026-09-09, firsthand authorization: “Great, can you write a charter
for this work and then execute on it”. This approves the F8 proposal at
`f1b1a1da:docs/2026-09-09_next-increment-certificate-provenance.md`, including
dependency-sensitive certification and widening the standing release rule.

[AGENT] IMPLEMENTED; independent review pending on `fix/certificate-provenance`, worktree
`.claude/worktrees/fix-certificate-provenance`, initially from main
`56b4d5c57e3239f4a7308d9c847b8db3c9bcbffe`. The other agent owns the ongoing
round-29 merged-tip certification; its final records will be incorporated
before this branch's final gate if main advances. Primary stays on main;
the untracked disk-growth review and all other worktrees remain untouched.

## Objective and end state

Cached observations count as certified only when the complete claim and
semantic/build dependencies match a successful certification. Missing, stale
or malformed evidence fails by name before cache reuse. A fresh run compares
its observations with the tracked set; any changed set is a finding, not an
automatic re-pin.

Finish with the implementation and compact evidence committed, full capped
CI and fresh slow certification passing at a clean source commit, measured
costs, and the user's independent-review ask posed. No merge or push.

## Authorized boundary

[AGENT] The approved feature comprises one versioned manifest/validator,
build provenance for the executable actually used, integration into both
membership and confluent caching, a deliberate refresh workflow, mutation
controls, CI enforcement, and the matching `CLAUDE.md` 5a / reconciler C9
policy. The same dependency inventory must serve these consumers.

Apparatus and necessary build/CLI provenance plumbing may change. The
interpreter semantics, relational rules, theorem statements, Go oracle and
Lean toolchain pins, frontend wire, corpus and outcome baselines do not.
Baseline acceptance remains 3665 executable rows (3417 PASS / 248 tracked
FAIL), 394 negative PASS rows, and the six-member slow observation set with
unchanged wire and parameters. Metadata additions are reviewed separately
from those unchanged observations. No source or theorem is altered merely
to make a control pass.

B7, C1, G-P, F9, R10's declaration re-pin authorization, and T8.1's typed
gate residuals are outside this work. The approval does not reopen other
pending roadmap decisions or authorize prototype cleanup.

## Contract requirements

1. Fingerprint the complete enumeration request: wire, entry, arguments,
   lane, expected statuses, observation policy and effective bounds.
2. Cover interpreter, decoder, observer, comparison, checker/enumerator,
   relevant apparatus, toolchain and build inputs. A source manifest beside
   an unrelated executable is insufficient: the executable must carry or
   have verified provenance binding it to its compiled inputs. Do not
   confuse Git HEAD with a source/content identity.
3. Reuse survives docs-only commits and equivalent checkout locations.
   Missing/new dependencies cannot silently escape the manifest. Duplicate
   fields, unknown schema versions and incomplete metadata fail closed.
4. Both actual cache consumers use one validator. Keep sampled coupling
   checks and the explicit CERTIFIED-CACHED label. No bypass environment
   switch may turn invalid certification into a passing cached result.
5. Fresh enumeration may produce a refresh candidate only after successful
   completion, comparison with the tracked set, and stable input/build
   checks. Failed, interrupted or mismatched runs cannot mint reusable
   evidence. Ordinary CI never rewrites tracked certificates.
6. The same inventory governs recertification and C9. The broader 5a rule
   replaces the two-file heuristic as an explicit part of this approved
   increment; preserve the rule that a changed certified set is a finding.

## Implementation and validation sequence

[AGENT] Record the concrete schema and build binding in the design note,
then implement the manifest/build interface, shared validation and deliberate
refresh, followed by integration and acceptance controls. These are reviewable
implementation stages within the authorized feature, not additional user
approval gates.

Controls exercise unchanged reuse and docs/checkout portability; individual
semantic, observer, checker, build/toolchain and invocation mutations; old
binary/new source; added/omitted dependencies; malformed metadata; interrupted
and failed enumeration; unchanged-set refresh; and changed-set rejection.
At least one core mutation must actually compile while leaving the wire
unchanged, then be rejected as stale. Positive controls and explicit causes
distinguish intended rejection from an infrastructure failure. Exercise both
membership and confluent caching even though only membership currently has
a tier=slow corpus row.

Run focused checks during development. Before committing runtime/apparatus
changes run full `scripts/capped scripts/ci --slow`; repeat a full clean-source
gate for the review handoff, and demonstrate the ordinary cached path.
Measure new validation overhead and total wall time, reporting the actual
envelope and cache state. Start at 32 GiB / three Lean threads / twelve
corpus workers; full builds own the box-wide primary build lock. Every
Lean/Lake invocation goes through `scripts/capped`.

Scratch belongs under this worktree's `.tmp`, using symlink dependency
overlays rather than copied oleans. The approved proposal authorizes deletion
of successful owned scratch; failures retain output and a reason file. Never
delete another lane's artifacts, registered worktrees, or the user's review.
Keep bulky outputs ignored under `artifacts/`; tracked evidence must pass
the unchanged size gate. Log decisions with [AGENT]/[USER] provenance and
record real exit codes. No subagents are commissioned for this work; the
independent adversarial review remains the user's.

## Findings requiring a changed brief

Resolve implementation errors and routine design choices autonomously inside
this contract. A required semantic/theorem change, changed certified set,
or inability to provide honest build binding within the approved feature is
a named finding, not permission to weaken acceptance. Complete independent
work and bring any necessary design decision to the user. Named external
design gates and eventual merge/push approval remain hard stops.

## Execution log

[AGENT] 2026-09-09: incorporated the completed round-29 records by rebasing
onto main `8cc3d5c8` (snapshot `snapshot/f8-before-r29-records` preserved).
The implementation leaves every `GoLean/` and `Tests/` file unchanged.
The first completed focused suite passed 64 controls in 61.484 seconds,
including both shell consumers, a compiled Ops diagnostic mutation at the
same wire, real timeout cleanup, coverage in both directions, pre-merge
release comparisons, and a complete confluent positive/negative differential.
Owned successful scratch was removed (92,315,309 bytes, no copied oleans).
Four failed development fixtures remain under this worktree's `.tmp` with
reason files: an unsupported map-iteration dedup fixture, transposed manifest
fields, the fixture package name, and Go's refusal of symlinked embed data.
Those were infrastructure/fixture failures, never counted as successful
negative controls. Full-gate and clean-source receipts follow in the
completion record.

[AGENT] Final source review added four Lake-configuration escape controls: the focused suite now passes 68 in 64.430 seconds. The earlier full gate was intentionally interrupted after 332.011 seconds before source edits (captured exit -9, not a gate pass). The tightened source then re-certified all six observations in 135.826 seconds. The TSV human-readable certification header is refreshed alongside JSON; its observation data and exact params/wire pins remain unchanged.

[AGENT] The first full gate passed in 1228.433 seconds, with 3665 native rows matching (3417 PASS / 248 tracked FAIL), all 394 negative rows matching, and zero HIGH reconciler findings. A final diagnostic correction preserves the enumerator refusal text through the new wrapper (formerly only its exit reached the row detail); its focused control and final-source gate follow.

[AGENT] Diagnostic correction validated: all 68 focused controls pass (62.457 seconds), including refusal-text preservation, and fresh checked enumeration reproduces the same six observations in 132.231 seconds. Implementation is frozen for its final gate.

[AGENT] Final implementation gate: PASS, captured exit 0, 1179.888 seconds (32 GiB / 3 Lean threads / 12 corpus workers). All 3665 native and 394 negative rows match their frozen baselines; the slow six-member set is unchanged; 207 evaluator tests pass; the reconciler has two report-only findings and zero HIGH. No GoLean or Tests source changes. Implementation commit follows; the clean-source run and final evidence remain required.

[AGENT] Completion: implementation committed as `7d60c8bf`; the full clean
`ci --slow` passed at that commit (exit 0, 1204.046 seconds, git_dirty=false).
The six-member checker run took 157.464 seconds. Ordinary cached reuse also
passed at the clean code commit (31.386 seconds including 32 oracle draws;
five of six members exhibited, one unexhibited). The new CI step costs 73
seconds; standalone cache validation costs 5.035 seconds. Final changes are
records only: clean provenance receipt, matching human header, compact evidence
and roadmap status. See `docs/2026-09-09_certificate-provenance-completion.md`.
Branch is ready for the user's independent adversarial review. No merge/push.
