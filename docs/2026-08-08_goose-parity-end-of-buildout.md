# Goose-parity buildout — end-of-buildout report (2026-08-08)

The charter's check-in package (`docs/2026-08-07_goose-parity-charter.md`
§End-of-buildout report). Buildout ran on branch `goose-parity`
(a9ad607 → this commit), goose @ `3be88bbb`, perennial @ `43d4efab`,
NOT merged to main — the branch awaits the user's check-in per the
standing goal. Two mid-flight audit checkpoints ran (phase A after
batch 3; phase B after batch 6), each followed by a fix round; their
confirmed findings and the two compliance corrections are recorded in
`docs/goose-parity-buildout-log.md` (the honest per-batch record).

## Completion state vs the phase-1 inventory

Import-free files at the pinned rev, by enumeration: 81 under
`testdata/examples/` (the scoping's Part-B "87" over all of testdata
includes ~5 import-free files OUTSIDE examples/ — negative-tests/
typeswitch.go, proofsetup-tests/pkg/foo.go, disabled-tests/rfc1813/
types.go, goose-tests/errors/build_tag/{good,bad}.go — all harness/CLI
fixtures or disabled trees that the scoping's own phase-3 assigns out
of the import lane; build_tag/bad.go is importer-rejected by design).
Every examples-tree import-free file is now either LANDED or PARKED:

- **Landed: 78 units / 79 files / 172 corpus rows** —
  semantics 29/29 clean files (batches 1-3, 7), channel 5 of 7
  (batch 4), storage-clean 4 units (5 files; batch 5), generics 3
  (batch 5), unittest 37/37 (batches 6-9).
- **Parked: 2 units + 2 rows** (P2): channel/fibonacci,
  channel/higher-order; muxer's client-old + make-greeting rows —
  confluent certification exceeds sane enumeration cost (measured;
  options incl. POR are in the ledger).
- Import-bearing files (45) remain phase 2/3 by construction (sync 17,
  FFI/disk 17, time 10, other stdlib, harness files).

## Counts per rung

(Figures FINALIZED at the pre-merge audit round, 2026-08-08 — the
first version was a mixed snapshot written before the user-authorized
bug-fix round; the audit flagged it and this section now states the
branch-tip state.)

- **R1 (differential)**: 172 imported rows — **152 PASS / 20 FAIL**.
  Lane split of the 172: 167 strict (147 of them PASS, incl. 4
  expected-panic rows), 4 confluent-certified (all PASS), 1
  membership-certified (PASS, members=6, tier=slow cached checking).
  All 20 FAILs are `frontend-export` reds in RECORDED fail-closed
  quarantine classes (call-in-short-circuit-operand ×16;
  builtin-copy-in-statement-position ×2; map-element-target ×1;
  implicit-interface-conversion-in-multi-value-assignment ×1 — no NEW
  refusal reason in the whole buildout). ZERO deliberate reds remain:
  the buildout-time BUG-048 pin (unittest/embedded/live) flipped green
  when the user-authorized fix landed. Zero drift on every
  pre-existing id at every one of the branch's 11 baseline re-pins
  (1205 → 1381 ids); the only pre-existing-id movements anywhere are
  the 2 BUG-047 and 5 BUG-048 deliberate fix flips.
- **R2 (kernel pins)**: 12 oracles across 6 units (block 1, defer 2,
  nil 6, mapliteral 1, const 1, rune 1) — 24 kernel theorems
  (∀-streams `Terminates` via `allStreamsOk decide +kernel` +
  canonical-stream readout each; 0.4-1.6 s / ≤1 GiB RSS). Claim
  strength vs the designated TotalReadout shape is caveated in matrix
  §6 (checkpoint finding). R2 was held down during the buildout
  pending the then-parked P1 decision; P1 is now RESOLVED — all six
  pins are staleness-guarded by `scripts/check-imported-pins` (ci step
  1c5) — and the const pin's buildout-time BUG-047 true-of-term caveat
  is HISTORY: the bug is fixed and the term regenerated (the guard
  caught the drift).
- **R3 (GoSpec instances)**: 0 — skipped every batch with the recorded
  reason: no existing automation discharges a GoSpec instance for an
  arbitrary imported program; per-oracle WP walks are new per-program
  proof effort, and the charter forbids new proof infrastructure for
  R3. The honest R3 story remains the T3/T4/T7 successor arc.

## The parking ledger (docs/goose-parity-parked.md)

- **P1** — R2 staleness-guard wiring for generated Program terms
  (3 options with costs; pins ship under the documented-caveat option).
- **P2** — enumeration-infeasible confluent certification (fibonacci /
  higher-order / 2 muxer rows; measurements; 4 options incl.
  charter-forbidden POR).
- **P3** — BUG-047 triage + the batch-6 compliance lapse (recorded,
  not laundered).
- **P4** — BUG-048 triage.

## Bug list (filed + pinned during the buildout per MUST-PARK; both
FIXED post-buildout in the user-authorized check-in response round —
heading updated at the pre-merge audit)

- **BUG-047** (pre-existing, FIXED 2026-08-08): frontend double-emitted
  a conversion-of-call as the whole RHS of assign/define
  (emit.go:2112). Pinned red-first by
  `assign-order/conversion-call-eval-once/{define,assign}` (202 vs
  101); both pins now green. The two green-by-luck corpus instances
  (semantics/copy idempotent; unittest/const pure) were annotated
  during the buildout and the annotations removed with the fix.
- **BUG-048** (pre-existing, FIXED 2026-08-08 — frontend-side
  auto-deref): machine wrong-stuck calling a
  VALUE-receiver method through a pointer VARIABLE (`p := &x;
  p.get()`); promoted-through-embedding via pointer var works, the
  direct call does not. Pinned by
  `methods/value-receiver-via-pointer-var/{addr-of-var,addr-of-literal}`
  + `imported-goose/unittest/embedded/live`. (The buildout-time
  "unexercised cell" claim was corrected at the fix: the cell WAS
  pinned by two long-standing tracked-untriaged backlog reds,
  methods/value-auto-deref and pointers/nil-value-receiver-call-panic,
  which the fix also flips.)
- Observations (not bugs filed): a case binary orphaned past the
  harness's go-run timeout keeps running (batch-8 log); the confluent
  enumerator's runner detail is empty when timeout-killed (P2).

## Comparison-matrix delta (docs/goose-perennial-comparison.md §6)

The imported-corpus section §6 now carries per-batch rows and totals.
Corrected parity claims (phase-B checkpoint): the goose-REJECTS-cycles
and Google-unverified deltas were FALSE and are struck/restated. The
surviving true deltas: 152 of their example rows run differentially
GREEN (final count at the pre-merge audit round) on an executable semantics they no longer have; both upstream
`failing_test*` evaluation-order oracles (their known-wrong
translations) pass here; three latent upstream PANICS their
translation-only tests never execute are pinned as panic rows
(generic_conversion's nil-slice index; embedded.go's two nil-*embedB
promotions); Go 1.26 `new(expr)` is covered end-to-end; for Google the
delta is METHOD (their Qed permutation triple vs our certified
6-member reachability + differential). Their 37 proved `test_fun_ok`
lemmas vs our 12 R2 pins: theirs are termination-free Iris partial
correctness, ours are ∀-streams termination + canonical readout —
neither subsumes the other; the R2 count is P1-limited, not
capability-limited.

## What I would do differently (retrospective)

1. **Inspect green rows, not only red ones.** Both real bugs this
   buildout surfaced (BUG-047, BUG-048) ran GREEN or nearly so in
   their first appearance (purity/idempotence luck); the batch-6 lapse
   happened because the discipline only audited FAILs. A cheap
   wire-level double-emission scan (or any lowering-shape diff against
   source counts) per batch would have caught BUG-047 at batch 2.
2. **Never import while a full gate is in flight** (the batch-8
   PARTIAL; the manifest is a filesystem walk).
3. **Probe upstream entry points for termination/panic BEFORE
   wrapping** (the loops.go divergent demos cost a wedged harness; the
   embedded.go panics cost a re-run) — a 10-second `go run` probe per
   entry point is the right default.
4. **The sites/work bound loop is the slow part of concurrent
   imports.** An enumerator "measure mode" (report the consumed sites/
   steps of one canonical run before certification) would collapse the
   red-first tuning loop from 3-4 gate runs to 1 — a maintenance-round
   tooling wish, not attempted here (scripts/machine).
5. The corrected parity-claim discipline: verify every "they
   can't/don't" claim against their tree the way the checkpoint
   verifiers did (TestExamples run, grep for Qed) BEFORE writing it
   into the matrix. Two of my three claimed deltas were wrong; the
   checkable-cite convention exists precisely for this.
