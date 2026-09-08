# Typed-contract CI gates — work charter

[AGENT] 2026-09-08. Status: IN PROGRESS. Branch `land/typed-test-gates`,
worktree `.claude/worktrees/land-typed-test-gates`, from main
`dc83782dadc27f6a90eda4493a3b6cfa2e5d9697`. Plan: master-plan-v2
§2.6, T8, W3 and N6. Source quarry: committed `typed-consumer-sprint`
at `7edc298f`, selected by path and checked against today's landed modules.

## Authority and objective

[USER] 2026-09-08, firsthand: “Approved, go ahead and build this.” The
same instruction supplies the seven refinements below and reserves the
adversarial review to the user. This authorizes implementation and CI
widening; measured cost is presented for acceptance at the handoff.

Every module under `Tests/` belongs to a declared library, and every
declared library is built by a named CI step. Restore the seven missing
typed gate families and their actual post-import audits/fixture checks:
Boolean typing/runtime, recovery typing/storage/setup/control, and abort
observation. Prove the negative controls work. Preserve semantic behavior.

## Hard boundaries ([USER], supplied refinements)

- No edits anywhere under `GoLean/`. No theorem statement changes under
  `Tests/`. Build adaptations may change implementation/proof plumbing;
  a statement requiring alteration to pass is a finding, never a fix.
- Each restored script targets the modules now on main. L1's interface
  audit and L3's recovery-terminal restatements take precedence over the
  sprint. Do not restore archived definitions or older terminal contracts.
- New gate scratch lives under this worktree's `.tmp`. Dependencies use
  symlink overlays, never full olean copies. Remove each invocation's new
  scratch on success; retain failure logs and a reason file on failure.
  Existing scratch and other worktrees are untouched.
- Coverage fails closed both ways: all `Tests/` modules have library
  ownership; all libraries have an executed named CI build step. Any
  exceptions would need a frozen, shrink-only allowance; prefer none.
- Each restored audit has compiled private-axiom and proof-hole negatives,
  rejected by their expected names after successful compilation. The
  current declaration audit is the reference (eight controls after its
  review fixes; the user's six-poison reference describes its earlier form).
- Measure every new CI step and total cost. Record cache conditions and
  actual exit codes. Added minutes are presented to the user for acceptance.
- Baselines stay at 3,654 executable rows (3,403 PASS / 251 expected FAIL)
  and 394 negative PASS. No baseline re-pin, production frontend changes,
  new admission profile, Iris dependency, merge or push.

## Implementation and validation

[AGENT] Source selection, current-module compatibility and any findings
will be recorded in a compact landing note. Restore only relevant scripts,
audit/fixture tooling and the four missing contract notes already cited by
the public interface, checking historical prose against landed statements.
Add an executable library/CI coverage contract and adversarial self-tests
for both missing ownership and missing/failed builds. Check scratch success,
failure, foreign TMPDIR and no write-through into real build artifacts.

Every Lean/Lake invocation uses `scripts/capped`. Full builds/gates acquire
the box-wide lock; target builds at at most 48 GiB follow the standing
exemption. Initial envelope: 32 GiB, three Lean threads, twelve differential
workers. Warm builds may reuse copied artifacts from the identical main
source; no hardlinks or writable aliases to another worktree's outputs.

Before the implementation commit: focused controls, source-boundary checks,
and `scripts/capped scripts/ci --diff` PASS. Repeat the full gate at the
clean committed implementation tip, then make records-only updates.
Evidence on main contains small summaries, hashes, measurements and findings;
full logs and generated fixtures stay ignored. Report new-step times and
total wall time, clearly separating cold/warm and cached slow certification.

The endpoint is a clean, committed, validated branch with the review handoff
posed to the user. The user conducts the adversarial review, as for I1;
the author does not commission a substitute review or merge/push.

## Validation refinement after author finding F1

[AGENT] The first full `--diff` candidate passed at frozen index tree
`91148c13`. An isolated compiler probe then confirmed that a bare library
build can succeed without checking modules when `defaultFacets=[]`.
Explicit `:leanArts` targets and a real compiler regression close that gap;
all semantic/frontend/Test sources remain unchanged. Validate the corrected
gate sequence in full fast mode using the already measured differential
records, then run a fresh `--diff` at the clean committed implementation.
Record each source and mode separately. This avoids misrepresenting the
first candidate as certification of the later gate correction.
