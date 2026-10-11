# Storage operations

Builds use the existing 16 GiB / three Lean threads / two coverage-worker
limits. Storage controls are separate. The shared coordinator directory is
the primary checkout's `artifacts/storage`, resolved through Git's common
directory. It is shared by linked worktrees; standalone clones coordinate
within their own checkout.

| Resource | Admission/retention policy |
|---|---|
| Owned audit scratch | 20 GiB aggregate; each audit reserves 1 GiB and keeps one isolated complete package fixture at a time. |
| Compact audit evidence | 10 GiB aggregate; 128 MiB reserved per audit. No silent evidence eviction. |
| Retained generated outputs | 50 GiB aggregate across persistently registered gate/campaign output roots, including worktree scratch and Lake builds. Previously completed runs still count. |
| Whole gate/campaign growth | 8 GiB reservation; actual new output is checked during and after execution. |
| Common Go build cache | Warning at 50 GiB; refuse/stop at 75 GiB. No mass copying of old caches. |
| Filesystem free space | Preserve 100 GiB on the coordinator filesystem. |

The 50 GiB output limit is an [AGENT] operating choice under the maintenance
charter: a per-run growth limit alone would allow successive retained
campaigns to accumulate without limit. It is distinct from compact evidence
and the Go cache. Unknown/pinned material is not deleted to meet a budget.
Admission fails visibly when maintenance or an explicit disposition is needed.

Run `python3 tools/storage.py report` for current bytes, reservations and
paths. `scripts/ci`, `scripts/diff-coverage`, negative coverage, detector
soundness and grossmith campaigns enter `scripts/storage-run` automatically.
Use `scripts/storage-run -- <foreground command> ...` for ad hoc heavy work.
Commands must wait for their children. Register outputs outside the worktree
through `GOLEAN_STORAGE_EXTRA_PATHS`, a JSON array of absolute directories;
the grossmith wrapper registers its resolved output automatically.

These are **cooperative guards, not filesystem quotas**. Scans run between
operations and periodically during execution; writers can overshoot between
samples. A guard stops its observed process tree, including descendants in
other sessions, with a grace period for audit evidence preservation. An OS
quota would provide an independent hard ceiling; it is not configured by
this repository change. Uninstrumented historical scripts, separate projects
and intentionally detached work are outside this guard's guarantee.

Use `scripts/go-cache` for cache selection: explicit `GOLEAN_SHARED_GOCACHE`,
then `GOCACHE`, then the primary checkout's `artifacts/go-build-cache`.
Check resolver failure before invoking Go. All participating worktrees should
use the same resolved cache. Distinct absolute source/import paths may still
produce distinct Go cache keys; sharing does not promise perfect deduplication.
Go's own age trimming is not a byte quota. Ordinary observations, native wire
artifacts and mutable Lean builds remain worktree-specific.

Audit evidence contains the actual source archive/hashes, resolved Lean
executable hash, toolchain declaration, copied build inventories, mutation
source, harness, exact commands/relevant environment, logs, actual exits,
named rejection expectations and final state. Compilation must still succeed
before each exact audit rejection. Evidence and integrity manifests are
written before owned copies are removed. Preservation/cleanup failure is an
infrastructure failure; it keeps the reservation and discoverable scratch.

Do not remove a reservation merely because its PID disappeared. Inspect its
run record, descendants, scratch and sealed evidence first; interrupted or
unknown ownership remains charged. Successful/failed audit fixtures are
released after compact preservation; uncategorized shell scratch and ordinary
case results remain charged against their budgets. A maintainer may preserve
needed records and perform the explicitly authorized generated-data cleanup;
source, repositories, pinned evidence and unknown material need their own
disposition. No command here silently expires them.

The one-time 2026-09-06 reclaim packets live in primary artifacts:
`storage-maintenance-recovery-20260906-v2` and
`storage-maintenance-cache-executables-20260906`. Their sealed manifests,
journals and result files describe exact deletions. Historical compiled audit
files and helper binaries have exact compressed recovery objects; sources and
logs remain in their original directories. To selectively restore an exact
relative file/path prefix, use the maintenance branch's
`python3 tools/storage_reclaim.py restore <packet> --prefix <relative-prefix>`.
Restore checks hashes and refuses to overwrite changed files. Keep the
recovery objects until their archival disposition is explicitly agreed.

The scoped pruning preflight binds the approved pause snapshot, unchanged
lane Git/source state, stopped job records and public process trees. Nono
blocks other sessions' private `/proc` paths, so complete host FD visibility
is not claimed. Broader inspection would require restarting nono with the
needed read grant, or a reviewed derived profile; Codex approval cannot grant
it. This cleanup uses the documented owner-pause evidence instead of reading
those private descriptors. The original semantics sprint remains user-paused.

## Retire merged worktrees instead of archiving them

[USER] follow-up ruling: “My strong assumption is that retired worktrees
(ie. merged to main) contain no useful information that should be retained.”
The user prioritizes retiring these directories over optimizing every remaining
GiB. This supersedes the initial maintenance charter's archive exclusion for
finished, merged worktrees.

At main-merge closeout, make sure durable results are already tracked in main,
verify the lane has no new uncommitted work or active jobs/live dependents,
then remove the worktree and its ignored payloads. Do not move them into
`.claude/worktree-archive`, or create replacement bundles of the same data.
Retain Git commits/refs and a small record of the removed path, merged commit
and outcome. Active/paused/unmerged work remains protected. Fresh worktrees
use the existing shared-cache and storage-guard policies; retirement prevents
the inactive checkout population from accumulating indefinitely.

At retirement, include shared coordinator scratch/evidence owned exclusively
by that lane after its jobs finish; those records live outside the checkout.
The common Go cache remains shared and subject to its separate budget.
