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

## P2 (2026-08-08) — channel-tree units whose confluent certification exceeds sane enumeration cost

- **Units/rows:** `channel/fibonacci` (whole unit, not landed),
  `channel/higher-order` (whole unit, not landed), `channel/muxer`
  rows `client-old` and `make-greeting` (unit landed with its two
  certifiable rows, `async` + `client`; ALL upstream bodies remain in
  the landed main.go verbatim — only the two rows are absent).
- **Question:** how should a deterministic concurrent import be
  classified when the confluent lane is doctrinally right but the
  schedule-tree enumeration does not converge within sane bounds
  (work cap / the 300 s `LEAN_ENUM_TIMEOUT_SECONDS` budget)?
- **Evidence (all measured, goose @ 3be88bb):**
  - fibonacci (`fib_consumer`): width assertion mechanically refuted
    at 8 → append-spill envelope bound 32 (the growing `results`
    slice); at width=32,sites=64 the tree is still unexplored after
    20M steps (~32-way branching per spill site × schedule tree).
  - higher-order: >8M steps at sites=96 (3 threads, closure-carrying
    requests).
  - muxer/client-old: >8M (4.34M steps + 3.66M probes measured
    directly; 3 threads × two rendezvous streams).
  - muxer/make-greeting: killed by the 300 s enumerator timeout at
    work=20M (runner shows an empty detail when the enumerator is
    timeout-killed before printing — observability nit, recorded
    here, no fix attempted).
  - Contrast (landed): google-search CONVERGES at 34.7M steps /
    ~2-4 min (members=6 exactly, all 3! arrival orders) and is landed
    with work=40000000 — itself ~10× the corpus's largest prior
    work param (sb-chan's 4M); its recurring full-run cost is flagged
    in the batch-4 log for the next checkpoint.
- **Options + costs:**
  1. Raise caps/timeouts per case until convergence: unbounded and
     recurring — every full `ci --diff` pays it; make-greeting-class
     trees likely exceed any sane budget.
  2. Leave the rows in place permanently red (visible FAIL/confluent
     "not certified"): honest but pollutes the baseline's FAIL set
     with resource-bounded non-answers that look like coverage gaps.
  3. A weaker sanctioned classification for deterministic concurrent
     programs too large to certify (e.g. strict + three-stream
     invariance, explicitly labeled as an approximation): needs a
     doctrine decision — the confluent lane was introduced precisely
     to replace that approximation.
  4. Enumerator improvements (partial-order reduction / sleep sets —
     these trees are classic POR wins): machine/tool change,
     MUST-PARK in this buildout.
- **NO decision** — units skipped, buildout continues.
