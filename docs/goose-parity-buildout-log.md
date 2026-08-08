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

## Batch 1 (2026-08-08) — semantics tree, scalar ops & control flow

Units (10, all imported self-contained, no sibling assembly needed;
upstream `testdata/examples/semantics/*.go` @ 3be88bb):

| unit | rows | R1 | notes |
|---|---|---|---|
| semantics/comparisons | 5 | 5 PASS | |
| semantics/operations | 11 | 7 PASS, 4 frontend-export | quarantine: call in short-circuit operand (`ok && f(...)` oracle style) |
| semantics/precedence | 4 | 4 PASS | |
| semantics/shortcircuiting | 4 | 0 PASS, 4 frontend-export | same quarantine class — the unit's whole point is side-effecting `&&`/`\|\|` operands |
| semantics/int-conversions | 5 | 5 PASS | |
| semantics/conversions | 1 | 1 PASS | |
| semantics/loops | 10 | 10 PASS | |
| semantics/switch | 4 | 4 PASS | |
| semantics/block | 1 | 1 PASS | + R2 pilot pin |
| semantics/vars | 3 | 3 PASS | |

Totals: 48 rows — 40 R1 PASS, 8 FAIL, every FAIL at stage
`frontend-export` in the ONE recorded fail-closed class
"call/allocation in short-circuit operand (would change evaluation
order)" (`tools/nativefrontend/emit.go` `emitGuarded`). NO new refusal
reason surfaced (the Part-B acceptance condition); no divergence, no
suspected GoLean bug.

Rungs:
- **R2**: pilot `proofs/GoLeanProofs/Specs/ImportedGooseBlock.lean`
  (semantics/block): ∀-streams `Terminates` via `allStreamsOk`
  `decide +kernel` + canonical-stream `.normal` readout `= 1`; builds
  in ~0.4 s under the 16 GiB kernel cap. R2 SKIPPED for the other 9
  units: pending the P1 parked decision (staleness-guard wiring for
  generated Program terms — docs/goose-parity-parked.md); the pilot
  proves the route.
- **R3**: skipped batch-wide — no existing automation discharges a
  GoSpec instance for an arbitrary imported program; per-oracle WP
  walks are new per-program proof effort (attempt-or-skip judgment).

Gate: full `scripts/ci --diff` green; baseline re-pinned same-commit
(1205 → 1253 ids; all 1205 pre-existing ids unchanged — zero drift).
