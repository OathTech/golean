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

**RESOLVED AS PARKED (user check-in ruling, 2026-08-08):** the units
STAY parked — fibonacci, higher-order, and muxer's client-old /
make-greeting rows are not landed; the measurements below stand as the
motivating cases for the partial-order-reduction backlog (option 4).
No cap raises, no weaker reclassification. (The related
iteration-speed concern is addressed separately by the tiered-checking
directive — see the membership-lane design note's 2026-08-08
addendum.)

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
    with work=40000000 — ~2.7× the corpus's largest prior work param
    (goroutines/worker-pool/sum's 15M; magnitude corrected at the
    phase-C fix round — this entry first said "~10× sb-chan's 4M",
    misnaming the case and its value: sb-chan is 5M, the 4M row is
    sched-dependent/first-come) and ~1.3× the prior heaviest wall
    time (~84 s vs worker-pool/sum's ~65 s); its recurring full-run
    cost is flagged in the batch-4 log.
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

## P3 (2026-08-08) — BUG-047: conversion-of-call double emission (suspected GoLean bug surfaced by imports) + the handling lapse

- **Unit:** `unittest/const` (batch 6, the surfacing wrapper) and
  `semantics/copy` (batch 2, green-by-idempotence instances); the bug
  itself is corpus-wide (any `x := T(f())` / `x = T(f())`).
- **The precise question:** none open for this buildout — the item is
  the charter's MUST-PARK "suspected GoLean bugs surfaced by imports
  (park with repro; the fix belongs to a maintenance round)". Filed as
  **docs/BUGS.md BUG-047** with the phase-B verifier's six-shape repro
  matrix and root cause (emit.go:2112 conversion-path hoist + generic
  re-emit), and red-first pinned by the fresh canonical case
  `assign-order/conversion-call-eval-once/{define,assign}`
  (FAIL/differential, Lean 202 vs Go 101).
- **Evidence:** BUG-047's entry (matrix verbatim); the buildout
  worker's independent re-reproduction; the landed-corpus sweep (the
  only in-corpus instances are the two green-by-luck sites, both
  annotated at their cases.tsv + the R2 pin docstring).
- **Options + costs:** fix in the maintenance round (guard the
  conversion path's already-hoisted case at emit.go:2116, or report
  effectful=true from the conversion branch) — small, but frontend
  changes are charter-forbidden here; the pin case turns green when
  fixed and BUG-047's Cases discipline enforces closure.
- **COMPLIANCE LAPSE, recorded (not laundered):** the class was
  triggered by batch 6's own authored wrapper and went UNPARKED at the
  time — the batch-6 log claimed "11/11 R1 PASS — zero frontend
  refusals" while a wrong-answer class ran green by purity underneath.
  The checkpoint review caught it, not the batch discipline. Root
  cause of the miss: green R1 rows were read as "no frontend issue";
  the discipline only inspected FAILs. Recorded also in the batch log.
- **NO further decision needed** — the fix is deferred by charter, the
  triage is complete.
- **Fix landed (user check-in ruling, 2026-08-08):** BUG-047 fixed on
  the branch in the response round; pins flipped PASS; entry Status:
  fixed. The lapse record above stands as history.

## P4 (2026-08-08) — BUG-048: value-receiver method via pointer variable wrong-stuck (suspected GoLean bug surfaced by imports)

- **Unit:** `unittest/embedded` (batch 8). The unit's other rows are
  green (incl. two latent-upstream-panic pins); the `live` row stays
  RED as a corpus pin of the bug.
- **The precise question:** none open for this buildout — MUST-PARK
  triage per the charter. Filed as **docs/BUGS.md BUG-048** with the
  full probe matrix; minimized canonical pin
  `methods/value-receiver-via-pointer-var/{addr-of-var,addr-of-literal}`
  (both FAIL/lean-observation: machine stuck "expected struct value,
  got addr" where Go auto-derefs).
- **Evidence:** BUG-048's probe matrix (the buildout worker's own
  probes, 8 shapes); notable localization: promotion-through-embedding
  via a pointer variable WORKS, the direct value-receiver call on the
  pointer variable does not.
- **Options + costs:** maintenance-round fix in receiver adaptation
  (auto-deref for value receivers on pointer bases along the
  non-promoted path); the three pins turn green when fixed and the
  BUGS.md Cases discipline enforces closure.
- **NO further decision needed** — triage complete, fix deferred by
  charter.
