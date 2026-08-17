# covmap pilot — results and go/no-go (2026-08-17)

Campaign doc §8.5's pilot, executed 2026-08-17. covmap @ `2978393a`
(deps/covmap, built with repo-local `CARGO_HOME`/`CARGO_TARGET_DIR`
under `artifacts/` — the sandbox denies `~/.cargo`, same pattern as
`GOCACHE`). Pilot repo: `artifacts/covmap-pilot/` (gitignored):
`spec.html` = `doc/go_spec.html` @ go1.25.13 (simulated old pin),
`latitude.md` = the latitude inventory. The simulated re-pin event:
overwrite with the go1.26.5 spec — our REAL pin, so the drift is the
real 92/78-line release delta. Ground truth (difflib, hunks mapped to
nearest enclosing anchor): **12 changed sections** — 11 anchored
sections plus the pre-anchor preamble segment — (preamble,
Alias_declarations, Allocation, Appending_and_copying_slices, Close,
Composite_literals, For_clause, For_range, Min_and_max,
Operator_precedence, Type_definitions, Type_parameter_declarations).

## What worked

- **Structural segmentation is scriptable and fast**: all 158 spec
  sections cut at `<h[234] id=…>` boundaries (159 segments counting
  the pre-anchor preamble — the two counts are distinct; audit nit
  2026-08-17) and named after their anchors in 0.4 s / 317 covmap
  calls (`artifacts/covmap-pilot/covlib.py`
  — ~30 lines of hash-re-resolution gymnastics; the speed is fine, the
  gymnastics is the CIP-3 evidence). Latitude side: 48 segments,
  `@C1…@C11`, `@E1…` etc.
- **@name link endpoints work as advertised**: 8 links (C1→
  @Go_statements, C4→@Program_execution, C5→@Channel_types,
  C6/C7→@Select_statements, E1/E2→@Order_of_evaluation,
  E5→@Assignment_statements) created directly with `@name` addresses.
  Self-connection (`connect main "$PWD:main"`) works — the one-repo
  workaround for the absolute-path gap is viable.
- **Drift detection is instant and correct**: `status` flagged the
  edited file immediately after the re-pin.
- **The workaround re-pin flow reproduces ground truth EXACTLY**:
  re-segment the new spec into a fresh covering (same 0.4 s script) →
  compare hashes of same-named segments across coverings → the 12
  changed sections, no more, no less, zero false positives.
  Precondition, stated honestly: the anchor set must be stable across
  the pair (true here; under anchor renames the named diff degrades
  to drop/add pairs — the anchor-stability probe in
  `docs/spec-sources.md` is what makes this workaround trustworthy). Then:
  changed ∩ link-targets = ∅ → "no envelope arguments need re-reading
  this cycle" — the campaign's §8.2 answer, mechanized.
- **`iter` is the re-review queue**: label the changed segments
  `review` (relabeling causes no drift — content-only hashes),
  `iter repin new spec2 --label review` → a 12-task resumable worklist
  with per-task notes. This is the P2 retrofit tool, confirmed.

## What broke (each is CIP evidence, `docs/covmap-cips/`)

- **`recut --remap` degenerates on version-headered documents — i.e.
  on every real spec re-pin.** The spec's subtitle ("Language version
  go1.25 (Aug 12, 2025)", line 3) defeats the common-prefix trim; the
  suffix trim still maps the last 1,078 lines, but the residual middle
  is 7834×7848 = 61.5 M DP cells, 15× over `diff.rs`'s 4 M
  `DP_CELL_CAP`, so the LCS bails and everything between line 3 and
  the common suffix is treated as changed. Result, measured (audit
  re-runs agreed): **~4 min CPU, 0 files healed, 0 segments refreshed,
  128 of 159 spec segments unresolved** (the first segment + 30
  suffix-mapped sections resolve) — pure fingerprint grind, ending in
  127 proposals + 1 "no candidate ≥ 0.40". The proposals *classify*
  perfectly — the 117 scored at 100 % are exactly the unchanged
  segments, the 11 sub-100 (spanning **69–99 %**; @Close 92 % is
  exactly the close-builtin change) are exactly the changed ones — but
  one genuinely changed section (@Allocation) got **no candidate at
  all** (fingerprint false negative at the 0.40 default), and all the
  signal is then discarded: remap is propose-only. (An earlier draft
  of this note reported the changed-section range as "92–98 %" from a
  truncated output tail and "146 exact matches" from arithmetic —
  both corrected here from full measured output, audit 2026-08-17.)
  → CIP: unique-line/patience-style anchoring in `line_map` + an
  `--apply --threshold` mode with the partition invariant answered.
  (Positive note: this failure exits 1.)
- **`status` fails open on exit code** (confirming the code reading):
  it exits 0 with drift present (re-verified rc 0 with `drift: 1
  file(s) edited`). No machine-readable output. CORRECTION (audit
  2026-08-17): this note originally also claimed `recut --remap main`
  misparses and exits 0 — false; it exits 1 (the observed 0 was the
  background-shell wrapper's exit, not covmap's — the exact
  async-stdout misfire CLAUDE.md's housekeeping section warns about).
  Error paths propagate `io::Error` and exit non-zero; the fail-open
  is `status` specifically.
- **`@name`s are unique per covering, across files** — the spec's
  `preamble` collided with latitude's; cross-file coverings need a
  prefix convention (we used `lat-*`) or per-file namespacing.
- **Coverage denominators pool all files in a covering** (8/207 counts
  latitude + spec together); the "unlinked spec sections" query needs
  per-file scoping.
- Minor: `ls | head` panics on SIGPIPE (plumbing should tolerate it).

## Verdict: GO, conditioned

covmap is the 4.1 mechanism: the identity model (content-only hashes,
names outside identity), drift detection, `@name` links, and `iter`
worklists all did exactly what the workflow needs, and the one broken
built-in (remap) has a working scripted substitute (re-segment +
named-hash diff) that is *arguably better* — it is exact, 0.4 s, and
needs no relocation heuristics as long as segmentation is
anchor-derived. Conditions carried as CIPs, priority order:
CIP-1 status/exit contract (blocks gate wiring), CIP-4 remap
robustness/apply (blocks the no-script workflow), CIP-2 portable
connections (blocks multi-worktree use; self-connection suffices for
one-lane P2), CIP-3 structural segmentation (our script covers it
meanwhile). Fallback (bare anchor lint) not needed.

## Control experiment: the small-edit case (diagnosis CORRECTED by the
pre-landing audit, 2026-08-17)

To separate "remap's diff degenerates on this document" from "remap is
broken generally", a one-line in-place edit to `latitude.md` (line
213, same line count): bare `recut --remap` — 4 m again (it re-grinds
the still-drifted spec every run) and did not heal the one-line edit
("0 refreshed, 129 unresolved"). **This note originally misdiagnosed
that as "remap does not refresh in-place segment drift" — false.**
The refresh path exists and works (`covering.rs:920-936`; audit probe:
an *interior*-line edit heals cleanly, "1 refreshed, 0 unresolved").
The real cause: line 213 is @C6's **first line**, and `remap_file`
resolves a segment by mapping its start line only
(`covering.rs:885-898`) — a changed start line ⇒ unresolved ⇒ the
per-file all-or-nothing bail. Since structural coverings cut at
heading lines, heading edits hit this constantly; the corrected
upstream ask (CIP-4) is start-line-resilient resolution + per-segment
degradation, not a refresh feature that already ships. What survives
of the original observation: plain `recut main:@C6` healed instantly
with the name preserved, but required knowing which segment to aim
at — **`status` reports drift at file granularity only** (remap's
proposals do name segments, but only after the 4-minute grind), so
CIP-1 keeps the ask that status enumerate drifted segments.

Not exercised, honestly: multi-repo connections (worked around by
design), `html` rendering, `fsck`, format migration, remap on a
small edit with NO other drifted file present (the 4 m spec grind
dominated every remap run once the re-pin landed).
