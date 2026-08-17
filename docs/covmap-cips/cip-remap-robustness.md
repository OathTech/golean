# CIP draft: robust remap diff + an `--apply` mode for proposals

Drafted by the golean spec-truth campaign, 2026-08-17, against covmap
`2978393a`. Grounded in `docs/2026-08-17_covmap-pilot.md` (golean repo);
all numbers below re-measured during the pre-landing audit (two
independent re-runs agreed). DRAFT — not yet handed to the covmap repo.

## Idea

Three changes that together make `recut --remap` work on the document
class it will most often meet — a versioned document whose header
changes on every revision: (1) replace the prefix/suffix + capped-LCS
line matcher with unique-line anchoring; (2) make segment resolution
resilient to a changed *start line* (today a segment whose first line
changed is unresolved even when its body is intact); (3) let the
already-good fingerprint proposals be applied, thresholded, instead of
demanding per-segment manual relocation — with an explicit answer to
the partition invariant.

## Motivation — a measured failure on a realistic input

(Timing across three re-runs: 246–259 s user; the structural numbers
— 117 / 127+1 / 128 of 159 — were identical in every run.)

Pilot setup: the Go language spec (`go_spec.html`, ~8.9k lines) cut
into 159 segments (158 anchor-named sections + the preamble); the
drift event is a release-to-release re-pin (go1.25.13 → go1.26.5, a
92-insertion/78-deletion delta across 31 hunks touching 12 sections —
a *small* real edit).

`diff.rs::line_map` trims common prefix/suffix and runs LCS on the
middle, bailing above `DP_CELL_CAP` (4 M cells) to "fully changed".
The spec's subtitle — "Language version go1.25 (Aug 12, 2025)" — sits
at **line 3**, so the prefix trim stops there; the suffix trim still
maps the last 1,078 lines, but the residual middle is 7834×7848 =
**61.5 M cells**, 15× the cap. Everything between line 3 and the
common suffix is treated as changed. Consequence, measured:

- `recut --remap`: **~4 min CPU (246–259 s user across runs), 0 files
  healed, 0 segments refreshed, 128 of 159 spec segments unresolved**
  (the first segment and 30 suffix-mapped sections resolve), followed
  by 127 relocation proposals + 1 "no candidate ≥ 0.40".
- The proposals *classify* perfectly: the 117 segments proposed at
  **100 %** are exactly the unchanged ones, and the 11 changed
  segments are exactly the rest — 10 with sub-100 scores spanning
  **69–99 %** (`@Type_parameter_declarations` 69 %,
  `@Composite_literals` 85 %, `@Close` 92 % — exactly the
  close-builtin change) plus one (`@Allocation`) with **no candidate
  at all** at the 0.40 default — a fingerprint false negative. All of that signal is then discarded:
  each proposal ends with "covmap unlink/link to relocate".

Any header-versioned document (specs, standards, generated docs,
changelogs) reproduces this: one early changed line defeats the
prefix trim and the cap makes everything outside the common suffix
"changed". This is not a pathological input; it is the primary covmap
use case (spec-to-code mapping).

## The second failure mode: boundary-line edits (control experiment)

A one-line in-place edit (same line count) to the *first line* of a
segment is also unresolved: `remap_file` resolves each segment by
mapping its **start line** only (`covering.rs:885-898`), so a changed
start line ⇒ `Unresolved` ⇒ the per-file all-or-nothing bail discards
the resolutions of every other segment in the file. (Correction
recorded 2026-08-17: an earlier draft of this CIP misdiagnosed this as
"remap does not refresh in-place content changes" — false; the
refresh path exists and works, `covering.rs:920-936`, verified with an
interior-line edit that healed cleanly: `1 refreshed, 0 unresolved`.
The defect is start-line resolution + the per-file bail, not a missing
refresh.) Since structural coverings cut at heading lines, and heading
lines are precisely where titles get edited, boundary-line edits are
common, not corner-case.

## Sketch

1. **Anchoring diff.** Before (or instead of) the LCS: match lines
   that are *unique in both files* (patience-diff style), then recurse
   into the gaps between anchor pairs; only gaps get the DP, and each
   gap is small for a localized edit regardless of where in the file
   it sits (this pair has 31 hunks by `diff -U0`; the gaps around them are all
   tiny).
   Fall back to the current behavior only within an oversized gap.
2. **Start-line-resilient resolution + per-segment bail.** Resolve a
   segment by any preserved line it contains (or its neighbors'
   boundaries), not its first line alone; and degrade per-segment
   (resolve what resolves, propose for the rest) instead of the
   per-file all-or-nothing `RemapError::Unresolved`.
3. **`recut --remap --apply [--threshold <f>]`** — with the partition
   invariant answered explicitly, since a covering must tile each file
   and `fsck` enforces it (`cli.rs:2788-2796`): apply proposals only
   when **every** segment of the file resolves at ≥ threshold (then
   the new tiling is total), and otherwise either stay propose-only
   for that file or synthesize explicit `unknown`-labeled filler
   segments for the unresolved gaps so the tiling stays legal. Default
   threshold conservative (1.0 = exact-content matches only — 117 of
   this pilot's 128 would heal, leaving the 11 changed segments — 10
   scored below 100 % + 1 no-candidate — for review, which is the
   correct residue). Named segments keep
   their names, so `@name` link endpoints heal for free.

## What we do meanwhile (workaround on record)

Re-segment the new revision into a fresh covering with the same
anchor-derived script (0.4 s) and compare same-named segment hashes
across coverings — exact, fast, no heuristics. Two preconditions,
stated honestly: boundaries must be mechanically derivable
(hand-curated coverings have no such escape, which is why the fix
belongs in remap), and the anchor set must be stable across the pair
(verified for go1.25→1.26; under anchor renames the named diff
degrades to drop/add pairs).
