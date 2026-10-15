# D1 detector contracts

Baseline: audited C1 `55ad72493061b59363e846341380a9edce12a2de`.
Branch: `spike/relational-detector-contracts-1015`, isolated worktree of the
same name under `.claude/worktrees/`. Its `.lake`, experiment `.lake`, Go
build cache and temporary files are private to this lane.

## Decisions and provenance

- [USER] 2026-10-15: execute the relayed D1 charter independently of C2,
  permitting limited behavior-preserving operational changes; no merge,
  push, live repin or peer writes.
- [AGENT] 2026-10-15: carry the experiment sources and historical stage/review
  verbatim from `f6f37e36f4844d7e3730496a4fa23b48e5a48e0e` via `git restore
  --source`, preserving its original branch/worktree. Historical reports
  describe that pin; this document records D1 and supersedes their open
  obligations only when proved here.

## Status

Work in progress. The original implementation scan failed with 17 findings.
No operational preservation or detector contract is claimed complete yet.
