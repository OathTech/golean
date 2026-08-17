# CIP draft: structural segmentation (batch cuts from a rule or list)

Drafted by the golean spec-truth campaign, 2026-08-17, against covmap
`2978393a`. Grounded in `docs/2026-08-17_covmap-pilot.md` (golean repo).
DRAFT — not yet handed to the covmap repo.

## Idea

A plumbing command that cuts a file's segments at every line matching
a pattern (or from a precomputed cut-list on stdin), optionally naming
each new segment from a capture group — turning "N hand-addressed
splits" into one declarative call.

## Motivation

Documents with intrinsic structure (HTML headings, markdown headings,
function definitions) are the common case for spec-to-code coverings,
and their boundaries are mechanical. RE-SCOPED after delta-review
(2026-08-17): `split` addresses accept segment hash, `@name`, AND
positional `file:line` (`covering::resolve_segment` →
`resolve_position`; verified end-to-end) — so a bulk-cut script can
address every cut positionally and never touch a hash. Our pilot
script (python, ~30 lines; 158 sections, 317 invocations, 0.4 s) did
it the hard way, and an earlier draft of this CIP presented that
hash-re-resolution loop as forced. It is not; the honest residual
case for a built-in is smaller:
(a) **naming**: positional cutting still needs a second per-segment
pass to attach `@name`s, and deriving names from the boundary line's
capture group is the part no shell loop does cleanly;
(b) **idempotence** across re-runs (cut-at-existing-boundary as a
no-op) is easy to get subtly wrong in ad hoc scripts (our first
attempt double-ran and corrupted its own address book; a second bug
named segments off by one column);
(c) one declarative call is documentation of the covering's
derivation rule — reproducible by anyone, including CI.

Two adjacent findings from the same exercise:

- **`@name` uniqueness is per covering, across files**: naming the
  spec's lead section `preamble` blocked using `preamble` for the
  other covered file. Multi-file coverings need a documented
  convention (we prefixed `lat-*`) — or names scoped per file.
- **Coverage denominators pool all files in a covering** (the pilot's
  "8/207" mixed both files), so "how much of THE SPEC is mapped"
  needs per-file scoping in `status`/`ls` or single-file coverings —
  which this CIP's batch cutting makes cheap to maintain.

## Sketch

- `covmap split --at <regex> [--name-from <n>] <C> <file> [<label>]`:
  cut before every line matching `<regex>`; if `--name-from` is given,
  name each segment from capture group n of its boundary line's match.
  Our use: `--at '<h[234][^>]*id="([^"]+)"' --name-from 1` reproduces
  the whole pilot segmentation, anchor names included, in one call.
- Alternative/complement: `covmap split --cuts - <C> <file>` reading
  `line[<TAB>name]` rows from stdin — no regex engine needed (keeps
  the sha2-only dependency policy; the caller owns the pattern
  matching).
- Idempotence: cutting at an existing boundary is a no-op, so re-running
  the same rule after edits converges instead of erroring.
