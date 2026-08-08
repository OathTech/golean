# Goose-parity buildout — parking ledger

Charter: `docs/2026-08-07_goose-parity-charter.md`. Format per the
charter: unit; the precise question; evidence gathered (probes, cites);
options WITH costs; **NO decision**. A parked entry is a SUCCESS outcome
for a unit — this ledger is the deliverable the end-of-buildout check-in
resolves. Nothing here has been acted on.

Entries are appended in discovery order, dated.

---

## P1 (2026-08-08) — R2 pins: staleness-guard wiring for generated Program terms

- **Unit:** every R2 kernel pin in this buildout (pilot:
  `proofs/GoLeanProofs/Specs/ImportedGooseBlock.lean` for
  `imported-goose/semantics/block`).
- **Question:** should imported-oracle R2 pins be wired into
  `scripts/check-golden`'s staleness guard (baseline `.repr` +
  PINS entry per unit), and if so, per-unit or via a batch manifest?
  Without wiring, a pin's `Program` term certifies the lowering AS
  GENERATED at import time; a later frontend change can silently date
  it (the exact drift class check-golden exists to catch — its header
  says so).
- **Evidence:** `scripts/check-golden` PINS array (3 entries today,
  each = source dir | repr baseline | Lean term; both links checked);
  the existing pins' convention is baseline + term regenerated in the
  same commit as any frontend change. The pilot pin's docstring records
  the gap explicitly.
- **Options + costs:**
  1. Wire each R2 unit into check-golden (one PINS line + one tracked
     `.repr` per unit): full drift protection; cost = a `scripts/`
     commit per batch (checkpoint-gated shared infra) + check-golden
     runtime grows linearly (one frontend emit + decode + term print
     per pin; currently ~seconds each).
  2. A single "imported-goose pins" manifest loop in check-golden
     (one scripts/ change total, data-driven): same protection,
     one-time gate cost, near-zero marginal cost per unit.
  3. No wiring; document the generated-at-rev caveat per pin file (the
     pilot's current state): zero gate cost; drift detection deferred
     to pre-merge audits.
- **NO decision** — pilot shipped under option 3 with the caveat in its
  docstring; further R2 pins in this buildout follow the same recorded
  caveat until the checkpoint resolves this.
