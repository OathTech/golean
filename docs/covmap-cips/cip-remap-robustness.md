# CIP draft: robust remap diff + an `--apply` mode for proposals

Drafted by the golean spec-truth campaign, 2026-08-17, against covmap
`2978393a`. Grounded in `docs/2026-08-17_covmap-pilot.md` (golean repo).
DRAFT — not yet handed to the covmap repo.

## Idea

Two changes that together make `recut --remap` work on the
document class it will most often meet — a versioned document whose
header changes on every revision: (1) replace the prefix/suffix +
capped-LCS line matcher with unique-line anchoring; (2) let the
already-good fingerprint proposals be applied, thresholded, instead of
demanding per-segment manual relocation.

## Motivation — a measured failure on a realistic input

Pilot setup: the Go language spec (`go_spec.html`, ~8.9k lines) cut
into 158 anchor-named sections; the drift event is a release-to-release
re-pin (go1.25.13 → go1.26.5, a 92-insertion/78-deletion delta across
12 sections — a *small* real edit).

`diff.rs::line_map` trims common prefix/suffix and runs LCS on the
middle, bailing above `DP_CELL_CAP` (4 M cells) to "fully changed".
But the spec's subtitle — "Language version go1.25 (Aug 12, 2025)" —
sits at **line 3**, so the prefix trim stops there; the residual
middle is 7834×7848 = **61.5 M cells**, 15× the cap. Every line below
3 is treated as changed. Consequence, measured:

- `recut --remap`: **4 m 06 s CPU, 0 files healed, 0 segments
  refreshed, 128 unresolved**, followed by 128 fingerprint proposals.
- The proposals themselves were *accurate*: 100 % matches for the 146
  unchanged sections, 92–98 % for the truly-changed ones (ground truth
  cross-checked against a difflib hunk→section mapping: exact
  agreement). All of that signal is then discarded — each proposal
  ends with "covmap unlink/link to relocate".

Any header-versioned document (specs, standards, generated docs,
changelogs) reproduces this: one early changed line defeats the trim
and the cap makes the whole file "changed". This is not a pathological
input; it is the primary covmap use case (spec-to-code mapping).

## Sketch

1. **Anchoring diff.** Before (or instead of) the LCS: match lines
   that are *unique in both files* (patience-diff style), then recurse
   into the gaps between anchor pairs; only gaps get the DP, and each
   gap is small for a localized edit regardless of where in the file
   it sits. The 61 M-cell case above becomes ~12 small DPs. Fallback
   to the current behavior only within an oversized gap.
2. **`recut --remap --apply [--threshold <f>]`**: apply relocation
   proposals scoring ≥ threshold (default conservative, e.g. 1.0 —
   exact-content matches only; the pilot's 146 exact matches would
   heal in one command). Below-threshold segments stay unresolved and
   propose-only, preserving today's safety. Named segments keep their
   names, so `@name` link endpoints heal for free.

Control experiment: a one-line in-place edit (same line count) was
also NOT healed by `recut --remap` — boundary-carry does not refresh
segments whose boundaries survive but whose bytes changed ("segment
drift"); only per-segment `recut <C>:<seg>` does, and `status` doesn't
say which segment to aim it at. Remap should refresh carried-boundary
changed-content segments as part of the same pass.

## What we do meanwhile (workaround on record)

Re-segment the new revision into a fresh covering with the same
anchor-derived script (0.4 s) and compare same-named segment hashes
across coverings — exact, fast, no heuristics. Works only because our
boundaries are mechanically derivable; hand-curated coverings have no
such escape, which is why the fix belongs in remap.
