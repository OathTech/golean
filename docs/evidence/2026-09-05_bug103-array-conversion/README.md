# BUG-103 validation evidence

[AGENT], 2026-09-05. Source base: main
`8db2d6dad165393f4d3cdffee63b8e7d624f39e6`, tested with the lane's uncommitted
changes. These are local incremental builds with an independently copied
`.lake` cache. Pinned dependency checkouts are read through lane-local
symlinks; no clean dependency bootstrap is claimed.

- `before.log`: the original BUG-103 fixture fails at `lean-observation`
  against the unchanged runtime, before adding the five new cases.
- `red-first.log`: all six conversion cases fail at `lean-observation`
  after adding the tests, before the runtime edit.
- `build.log`: capped `lake build`, including the coherence and StateWf
  modules; 62 build jobs complete.
- `eval-build.log`, `eval.log`: capped eval-test executable build and run;
  202 checks pass, including the four new malformed-machine-value checks.
- `focused.log`, `focused.tsv`, `focused.meta.tsv`: 23 differential cases,
  22 PASS and one existing FR-10 FAIL. The fixture's source comments were
  clarified after this run to distinguish the original six reverse-ordered
  type declarations from the additional BUG-103 types; executable code is
  identical.
- `focused-baseline-diff.log`: the original failing ID becomes PASS, five
  new IDs PASS; all 17 other cases match the unchanged baseline.
- `ci-diff-before-repin.log`: full `scripts/ci --diff` exits 1, solely for
  those six baseline deltas. All other gate steps pass.
- `full.tsv`, `full.meta.tsv`, `full-baseline-diff.log`: complete differential
  result and attribution, 3598 = 3353 PASS / 245 FAIL, and the exact six
  deltas against the previous baseline. One slow-tier row is CERTIFIED-CACHED.
- `negative.tsv`, `negative.meta.tsv`: all 394 compile-negative Go oracle
  checks pass. These do not test the native frontend's rejection behavior.
- `full-baseline-diff-after-repin.log`, `check-bugs.log`: all 3598 recorded
  results match the targeted baseline update; the bug index is consistent.
- `ci-after-repin-initial.log`: standing gate passes, but its report-only
  reconciler cannot parse the first spelling of the new ledger count line.
- `reconcile-after-record-fix.log`: restoring the existing parseable count
  syntax removes those two C4 findings; two pre-existing medium record
  findings remain (C13 historical version citations, C5 FR-7 citation).
- `ci-after-repin.log`: final standing gate after the record correction.
- `artifact-hashes.json`: base commit, semantic input fingerprint, and
  SHA-256 hashes of the lane's changed source/record files and evidence
  (excluding this hash manifest itself).

Build commands used `scripts/capped`, with a 24 GiB memory cap and three
Lean threads. The focused harness used six workers; the full gate uses eight.
The runtime tests are differential evidence against go1.26.5, not a proof of
Go source correctness or complete conversion coverage. The full gate's
`tier=slow` results are cached certifications unless explicitly stated
otherwise.
