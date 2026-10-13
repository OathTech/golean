# Codex brief — the zero-context release pass (2026-10-13)

STATUS: **PREPARED** ([AGENT] coordinator, 2026-10-13; asked for by the [USER], Mike, 2026-10-13:
«We should do another zero-context fresh eyes release pass with a Codex agent, check if we've
missed anything»). The [USER] runs it. This brief is setup and the question; it does not limit
where you look or what you may say.

## The question, verbatim ([USER] Mike, 2026-10-13)

«It's particularly important the semantics is fail-closed in cases where we are not high-confidence.»
And, for a first release: «check if we've missed anything».

## Where things are

Start at `README.md`, then `CLAUDE.md` (the charter: what is trusted, the doctrine, the gates),
`docs/README.md` (the index) and `docs/release.md` (what a release is and the limits ruled so far).
Everything else is reachable from those. One earlier pass exists
(`docs/2026-10-13_fresh-eyes-fail-closed-pass.md`); reading it is your choice, and nothing in it
is settled for you.

## Setup (exact)

- Work in the worktree `.claude/worktrees/codexpass-1013` (branch `audit/codexpass-1013`, at
  `main`'s tip of the day), prepared with the built `.lake` copied from `main` and the frontend
  built at `.tmp/nativefrontend`. If it is missing: `git worktree add .claude/worktrees/codexpass-1013
  -b audit/codexpass-1013 main`, copy `.lake` from the primary checkout, link the reference
  checkouts (`ln -s /home/mike/projects/golean/deps deps`; the gate's pin checks need them), then
  `GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend`.
- Every `lake`, `lean`, gate or corpus run goes through `capped` (`capped lake build`,
  `capped scripts/ci --diff`; `scripts/capped` is the shim). Exit 137 with a KILLED banner is a
  failure, never a pass. Never set `CAPPED_MEM_MAX=none`.
- A full build or gate run takes the box-wide lock first: `mkdir /home/mike/projects/golean/artifacts/build-lock.d`
  (atomic, at the PRIMARY root) and write an `owner` file inside (`codexpass <pid> <ISO date>`);
  on failure wait and retry, never take over; release it under a trap. Builds of explicit targets
  and single-program runs skip the lock, not the cap.
- Never kill processes by name or pattern (`pkill -f`, `killall`): other agents share this box.
  Kill only PIDs you started, after checking them.
- Scratch (probe programs, wires, outputs) lives under the worktree's `.tmp/` (gitignored), never
  `/tmp`. The oracle is the pinned `go1.26.5` on `PATH`; the sandbox has no network.
- The tree is read-only to you except your report. No push, no merge, no tag, no baseline re-pin,
  no edit to `CLAUDE.md`.

## Deliverable

One file, `docs/<run date>_codex-zero-context-pass.md`, committed on `audit/codexpass-1013` with
`[AGENT Codex]` provenance: your method, ranked findings each with a reproduction a reader can
run, what held, what you could not reach, and a verdict in your own words. A failure is reported
as a failure. If two readings of this brief differ materially, write both in the report rather
than choosing. Remove your `.tmp/` probes when done; the report is the only artifact.
