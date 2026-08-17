# CIP draft: an exit-code and machine-output contract for `status`

Drafted by the golean spec-truth campaign, 2026-08-17, against covmap
`2978393a`. Grounded in `docs/2026-08-17_covmap-pilot.md` (golean repo).
DRAFT — not yet handed to the covmap repo.

## Idea

Make `covmap status` (and error paths generally) usable as a CI gate:
a documented exit-code contract and a machine-readable output mode.

## Motivation

Our workflow wires covmap into a fail-closed CI preflight: "any drift
or broken link in the spec-to-semantics mapping turns the gate red
until healed." Today that is impossible to script honestly:

- `cmd_status` returns `Ok(0)` unconditionally (`src/cli.rs`, tail of
  `cmd_status`) — observed in the pilot printing `drift: 1 file(s)
  edited` and exiting 0, and re-verified during the pre-landing audit.
  (TOP-LEVEL errors are fine — they propagate `io::Error` through
  `main.rs` and exit non-zero; the fail-open surface is `status`'s
  unconditional 0 plus the per-item paths below. Note remap's exit is
  `Ok(if unresolved_count > 0 {1} else {0})`, `src/cli.rs:1679` — a
  skipped file alone still yields 0.)
- Output is human prose; a gate script must regex fragile text.

covmap already has the right precedent in-tree: `iter next` exits
non-zero on exhaustion precisely "so a shell loop stops"
(`src/cli.rs:2207`). This CIP extends that plumbing attitude to the
main reporting command.

## Sketch

- `status` exit codes: 0 = clean (no drift, no broken links, no
  unreadable coverings); 1 = drift or broken links present; 2 = usage
  or store error. A `--strict`-free design is fine — dirty state IS
  the non-zero case.
- `status --format tsv` (or `--porcelain`): one row per covering
  (`covering<TAB>segments<TAB>drifted_files<TAB>missing_files`) and
  per connection (`connection<TAB>links<TAB>broken<TAB>src_cov<TAB>
  tgt_cov`). TSV over JSON keeps the sha2-only dependency policy.
- Per-item failures must surface in the exit code. (Top-level
  `covmap:`-prefixed errors already exit non-zero via `main.rs` — no
  ask there; a draft of this CIP claimed otherwise and was corrected
  by audit.) The genuine fail-open holes are the *per-item* paths that
  print to stderr and continue: `cmd_status` on an unreadable covering
  (`eprintln!` then `continue`, function still returns `Ok(0)`,
  `src/cli.rs:369-374`), and `cmd_recut_remap`'s "cannot read as
  UTF-8 — skipped" / "object store incomplete — skipped" paths.
- `status -v` (or the tsv rows) should enumerate *which segments*
  drifted, not just per-file counts: the pilot's heal path (`recut
  <C>:<seg>` for an in-place edit) requires knowing the segment, and
  today that knowledge must come from outside covmap.
- Bonus, found while scripting: `ls` panics on SIGPIPE when piped to
  `head` (`failed printing to stdout: Broken pipe`); plumbing should
  treat EPIPE as a clean exit.
