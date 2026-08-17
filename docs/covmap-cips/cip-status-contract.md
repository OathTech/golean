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
  edited` and exiting 0.
- Some error paths also exit 0: `recut --remap main` prints
  `covmap: no segment matches 'main' in covering 'main'` and exits 0
  (misparsed argument reported as a per-item message, not a failure).
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
- Any command that prints a `covmap:`-prefixed error exits non-zero.
- `status -v` (or the tsv rows) should enumerate *which segments*
  drifted, not just per-file counts: the pilot's heal path (`recut
  <C>:<seg>` for an in-place edit) requires knowing the segment, and
  today that knowledge must come from outside covmap.
- Bonus, found while scripting: `ls` panics on SIGPIPE when piped to
  `head` (`failed printing to stdout: Broken pipe`); plumbing should
  treat EPIPE as a clean exit.
