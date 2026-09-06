# B7 design inputs

[AGENT], 2026-09-06. This inventory supports the
[implementation design](../../2026-09-06_b7-context-store-design.md), not a
completed representation change or acceptance of uncommitted runtime work.

`source-inventory.json` records exact source hashes, per-file import edges,
worktree heads/statuses and the design's hash. It includes the stable helper
increment, the coordinator's exact-initialization work in progress, and the
runtime lane's concrete invariant/preservation/progress/safety inputs. All
were read only. The inspected source snapshots are not relabeled as built or
independently reviewed merely because they supplied design inputs.

No runtime, frontend, baseline, dependency pin, or gate script changed in
this slice. Validation consists of checking local documentation links,
source/inventory construction and `git diff --check`. The preflight and helper
reviews have their separate source-bound packages.

Check `SHA256SUMS` from this directory, then verify the design bytes against
the `design_sha256` field before using this plan for implementation.
