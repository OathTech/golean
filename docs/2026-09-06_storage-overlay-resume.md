# Paused lane: storage overlay and resume obligations

[AGENT] 2026-09-06, under the user-authorized storage maintenance charter.
**The semantics sprint remains user-paused. No semantic jobs were resumed.**

Lane: `typed-byte-runtime`. Maintenance installed unstaged tooling and operating notes;
lane HEAD, exact Git index bytes, and captured semantic sources are unchanged.
The original lane handoff remains authoritative about semantic WIP. The
[overall pause state](2026-09-06_typed-sprint-pause-state.md) records the
interrupted jobs, evidence boundaries and remaining sprint obligations.

The tooling now uses one complete isolated compiled mutation fixture at a
time, sealed compact evidence before release, a shared Go cache, and shared
storage admission/monitoring. Read [storage operations](storage-operations.md).
The main maintenance worktree is `../storage-maintenance`; its
`docs/evidence/2026-09-06_storage-maintenance/rollout-before.json` and
`rollout-verification.json` bind the exact overlay. Independent maintenance
validation does not certify this lane's different semantic sources.

Keep the frozen byte-append candidate and its independent review packet intact. Re-freeze after the tooling overlay, including byte-array-store-audit.py; full capture and BUG090 remain owed. The retention/representation assessment is unchanged; no runtime GC or representation redesign is authorized here.

On explicit user resumption, inspect current storage usage with
`python3 tools/storage.py report`, verify the preserved source/index state,
re-freeze actual tooling plus semantic inputs, and run the fresh gates owed
by this lane. Member pins in this paused lane were deliberately left as-is:
review source-only apparatus changes separately, preserving native wire,
control, observation and policy fields. Old certificates remain bound to old
sources. Never count interrupted output as success or restart old process
handles. Main merge/push still need their separate user approvals.
