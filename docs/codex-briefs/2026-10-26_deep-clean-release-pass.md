# Brief — the deep-clean release pass (2026-10-26)

STATUS: **PREPARED** ([AGENT] coordinator, 2026-10-26; asked for by the [USER]
the same day: a fresh-eyes pass before the first release, with a deep-clean
emphasis). The [USER] runs it. This brief is setup and the question; it does not
limit where you look or what you may say.

## The question

Before a first release of this repository, find what has been missed. The
owner's standing concern, in their words from the previous pass, is that the
semantics be fail-closed wherever confidence is not high. «Deep clean» means
the whole tree is in scope: wrong answers, fail-open paths, stale or
overstated claims in living documents, gate steps that cannot catch what they
claim, dead or misleading code and records, anything a release reader would
trust and should not.

## Where things are

Start at `README.md`, `CLAUDE.md` (the charter), `docs/README.md` (the index)
and `docs/release.md` (what a release is, its predicates and stated limits).
Everything else is reachable from those. Earlier passes exist under `docs/`
(`2026-10-12_release-trust-review.md`, `2026-10-13_fresh-eyes-fail-closed-pass.md`,
`2026-10-13_codex-zero-context-pass.md`); reading them is your choice, and
nothing in them is settled for you.

## Setup (exact)

- Work in the worktree `.claude/worktrees/deepclean-1026` (branch
  `audit/deepclean-1026`, at `main`'s tip of the day), prepared with the built
  `.lake`, `deps/` linked to the reference checkouts, the last recorded corpus
  runs under `artifacts/coverage/`, and the frontend built at
  `.tmp/nativefrontend`. If anything is missing: `git worktree add
  .claude/worktrees/deepclean-1026 -b audit/deepclean-1026 main`, copy `.lake`
  from the primary checkout, `ln -s <primary>/deps deps`, then
  `GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend`.
- Every `lake`, `lean`, gate or corpus run goes through the memory cap: on this
  box `capped` is on PATH and the scripts detect it (`scripts/cap.sh`); run
  `CAPPED_MEM_MAX=64G capped scripts/ci --diff` for the merge tier, `capped
  scripts/ci` for the fast tier, `capped lake build` for builds. Exit 137 with a
  KILLED banner is a failure, never a pass. Never set `CAPPED_MEM_MAX=none`.
- A full build, gate, `lake check` or `lake comparator` run takes the box-wide
  lock first: `mkdir /home/mike/projects/golean/artifacts/build-lock.d`
  (atomic, at the PRIMARY root) and write an `owner` file inside
  (`deepclean <pid> <ISO date>`); on failure wait and retry, never take over;
  release it under a trap. Single-program runs and single-module builds skip
  the lock, not the cap.
- Never kill processes by name or pattern (`pkill -f`, `killall`): other agents
  share this box. Kill only PIDs you started, after checking them.
- Scratch lives under the worktree's `.tmp/` (gitignored), never `/tmp`. The
  oracle is the pinned `go1.26.5` on `PATH`; the differential runner pins
  `GODEBUG=panicnil=0`. The sandbox has no network; `lake check`'s `bwrap` cannot
  start here, so its in-tree form is `--inadvisably-no-sandbox`.
- The tree is read-only to you except your report. No push, no merge, no tag,
  no baseline re-pin, no edit to `CLAUDE.md`, no change to machine-global state.

## Deliverable

One file, `docs/<run date>_deep-clean-release-pass.md`, committed on
`audit/deepclean-1026` with `[AGENT <your name>]` provenance: your method,
ranked findings each with a reproduction a reader can run, what held, what you
could not reach, and a verdict in your own words. A failure is reported as a
failure. Do not quote the owner or any private message in the file; paraphrase.
If two readings of this brief differ materially, write both in the report
rather than choosing. Remove your `.tmp/` probes when done; the report is the
only artifact.
