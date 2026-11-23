# Code-only archive copy: `archive/byte-runtime-code`

The runtime byte-array store of 2026-09-06 (`GoLean/GoCore/ByteArrayStore.lean`, `Tests/ByteAppend*.lean`): three review commits and a recovery snapshot of the uncommitted worktree state, which is where the store itself lives. The snapshot also carries unrelated uncommitted edits from that worktree.

This branch was published on 2026-11-23 from a retired development machine.
It is a commit-for-commit copy of `refs/snapshots/2026-10-11-recovery/wip-typed-byte-runtime` on the pushed commit `c969079a1`,
with authors, dates and messages unchanged and `docs/evidence/` held at
that base's contents: the run evidence the original commits added is not
here, so links into it from these commits are dead. Nothing outside
`docs/evidence/` differs from the original trees.

The typed-profiles lane this belongs to was parked on 2026-09-16 and not
migrated ([USER] ruling D1, 2026-10-11, in
`docs/2026-10-11_recovery-and-migration-plan.md` on `main`). It is kept
because BUG-090 was still open when it was archived and this was the only
attempt at it. No build, gate or review was run for this copy.

Documents on `main` cite the original hashes:

| Original | Here | Subject |
| --- | --- | --- |
| `352d09f9c` | `ac81fbaf4` | Independently review O2 terminal additive integration union |
| `138db3185` | `426d788c0` | docs: independently review I1 diagnostic vocabulary proposal |
| `35aee5d31` | `d74aa740c` | Independently review exact runtime byte append refinement |
| `2a97e1431` | `79a174146` | [AGENT] recovery snapshot 2026-10-11: uncommitted state of worktree typed-byte-runtime (br |

[USER 2026-11-23] Publish the byte-store work; evidence blobs are not published.
