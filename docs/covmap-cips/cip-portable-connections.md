# CIP draft: portable, rev-aware cross-repo connections

Drafted by the golean spec-truth campaign, 2026-08-17, against covmap
`2978393a`. Grounded in `docs/2026-08-17_covmap-pilot.md` (golean repo).
DRAFT — not yet handed to the covmap repo.

## Idea

Reference the target repo of a connection by a named alias resolved
through per-checkout config (git-remote-style), optionally carrying an
expected git rev — instead of a baked-in absolute path.

## Motivation

A connection stores `# target_repo=<abs/path>` (`src/connection.rs:4-8`,
`:40`) and `status` builds the target `Repo` straight from that string.
Two failure modes for any team that tracks `.covmap/` in git (which the
sorted-text store deliberately makes attractive):

1. **Worktrees and clones break every connection.** golean runs a
   worktree-per-lane discipline — ~20 checkouts of the same repo at
   different absolute paths. A connection created in one lane resolves
   in none of the others, nor in any fresh clone, nor in CI. The pilot
   worked around it by keeping both coverings in ONE repo and using a
   self-connection (`covmap connect main "$PWD:main"`) — fine for a
   pilot, wrong shape for the real spec-repo ↔ semantics-repo mapping.
2. **The target is unpinned.** `status` compares against whatever
   bytes are on disk at that path today. Our target repo is a *pinned*
   checkout (the Go spec at a named release); if someone advances it,
   link health silently reports against the wrong revision. The
   correspondence claim "our envelope arguments cite spec revision X"
   needs X recorded in the connection, and a loud failure when the
   checkout disagrees.

## Sketch

- `.covmap/remotes` (per-checkout, gitignore-able): `name<TAB>path`
  lines mapping alias → local path, like `.git/config` remotes.
- Connection file: `# target_repo=@<alias>` (existing absolute paths
  stay valid for compatibility), plus optional
  `# target_rev=<git-rev>`.
- `connect <C_A> @<alias>:<C_B>` records the alias; resolution happens
  at read time through `.covmap/remotes`, failing with a clear message
  naming the missing alias.
- When `target_rev` is present and the target is a git checkout,
  `status` verifies `HEAD` matches and reports a distinct state
  (`rev-mismatch`, non-zero under the status-contract CIP) rather than
  comparing content silently.
