# I1 declaration landing evidence

[AGENT] 2026-09-08. Scope: the separate L1b declaration boundary under
[`land/i1-declarations`' charter](../../2026-09-08_i1-declaration-landing-charter.md).
This directory contains compact records, not source or corpus copies.

- `source-selection.tsv`: fifteen original committed blobs at `7ac3eb46`.
- `candidate-gate.txt`: tail of the corrected full `--diff` gate, captured
  exit 0; dirty candidate at `31ecd39d`, frozen index tree
  `91c21fbbc0773ad375561adc478c9a7a5dbbe83f`.
- `author-controls.json`: eight actual fixture-reader challenges and their
  named refusals; these are author checks, not independent review.
- `candidate-measurements.json`: freshly derived counts, baseline status/stage
  comparison, source-bound log hashes and fixture identity.

The first full run was interrupted for the reproduced named-constraint bug
(exit 143, 1,010 partial published rows); it is not a full PASS. Full logs,
red-first outputs and the dead-owned-lock recovery record remain in ignored
`artifacts/i1-landing/` in the worktree. Findings and their resolutions are
explained in the [landing record](../../2026-09-08_i1-declaration-landing.md).
Final clean-commit certification and audit disposition will be appended there.
