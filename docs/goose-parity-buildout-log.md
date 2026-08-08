# Goose-parity buildout — batch log

Charter: `docs/2026-08-07_goose-parity-charter.md`. One section per
landed batch: units, rungs reached per unit, R2/R3 skips with one-line
reasons, counts, gate status. Setup notes precede batch 1.

Upstream pins for every import in this buildout: goose @
`3be88bbb4982f58e5813b6f0344302d5582c8e8a`, perennial @
`43d4efabc22eb148eb239ebee89d1dd2ee54c900` (the scoping note's Part B
revs; `deps/goose` is READ-ONLY throughout).

## Setup (pre-batch)

- Parking ledger + this log created.
- Charter header gained the grossmith re-pin addendum (the charter's own
  instruction: re-pin at buildout launch).
- `scripts/import-goose` + `scripts/test-import-goose` (reject-shape
  fixtures per the lane-validation mold). FLAG for the checkpoint
  reviewer: the charter gates commits touching `scripts/` behind an
  audit checkpoint; the coordinator's launch instruction explicitly
  ordered this helper built as setup with the checkpoint after ~3
  batches, so the script commit is flagged here for that review rather
  than checkpointed in advance.
- `imported_goose` feature tag joins `Corpus/coverage/tags.tsv` in the
  SAME commit as the first cases carrying it (batch 1) — the ci
  dead-tags gate (`scripts/check-coverage`) rejects an unexercised tag,
  so it cannot land at setup time. (Part C: "features gain an
  `imported_goose` tag; no schema change".)
- Starting gate: `scripts/ci` PASS at a9ad607 (baseline 1205 cases,
  1107 pass / 98 fail, recorded at 968142a; a9ad607 is doc-only atop
  it).

---

(no batches landed yet)
