# Channel-logic arc — successor charter (2026-08-10)

Status: DRAFT — SCOPING ONLY (user direction 2026-08-10: scope now, not
necessarily scheduled next). Successor to the spec-parity arc; assumes
its merged final state. Objective: close the *instrument-level* gaps to
Goose/Perennial equivalence that the spec-parity closure record names —
the places where our concurrency results are exhaustive-checking
certificates rather than a compositional program logic.

## The objective, stated as the property it buys

At this arc's end, a proved channel-program row means the same KIND of
thing on both sides: a heap-general, frame-quantified, fuel-independent
triple built compositionally from channel laws — with our standing
extras (executability, differential grounding, termination/deadlock
classes) on top. The parity table's against-us directions for the
channel class (compositionality, heap/frame generality, schedule
granularity's unproven bridge) close or become permanent recorded
asymmetries by explicit decision, never by silence.

## Work plan (slices)

1. **The channel WP law family.** `wpD` laws for the channel primitives
   (send/recv both directions, select incl. default, close, len/cap)
   over the LangD one-thread-step seam built in spec-parity slice 4
   (`goTripleC_of_wpD` is the consumer; P-S4-2 is the debt). Non-vacuity
   discipline as always: every law ships its discharge witness
   same-commit. Exemplar-first: hand-prove ONE channel program
   end-to-end through the laws before writing the rest of the family.
2. **The protocol layer.** The invariant/ghost layer for channel
   protocols (D2 NATIVE decision stands: native internally, comparison
   at the exported level; the Actris-lite port remains a recorded
   future option, not taken). Target: the dsp and muxer rows re-proved
   as compositional triples; park/deposit/wake full-strength for
   fork/join (P-S4-1's ∀-heap `ProgressExecC` closes here).
3. **Per-row frame-quantified triples.** Replace the certificate
   bundles' role for the six spec-parity channel rows (certificates
   stay as validation; the triple becomes the headline). Each row:
   triple + first-order readout (D1 BOTH), upstream status column
   maintained, deltas both directions.
4. **The NPDRF reduction proof.** The schedule-granularity bridge:
   DRF programs behave identically under communication-point
   scheduling. The current draft is marked REFUTABLE-AS-WRITTEN — this
   slice either proves the corrected statement or records precisely
   what fragment it holds for and captions every ∀-schedule theorem
   accordingly. This is the arc's hardest slice; budget for it, and
   an early design note on the corrected statement is binding before
   proof work.
5. **Race-axis decision + closure record.** Either (a) a
   detector-completeness theorem on the modeled fragment (no
   registry-point schedule of a modeled program exhibits a conflict the
   segment-HB detector misses — makes our race-freedom theorems
   sound-by-construction over modeled schedules, closing the proof-side
   asymmetry at that granularity), or (b) the asymmetry is recorded as
   permanent with the O4/T12 axis split as its statement. USER CALL,
   informed by slice 4's outcome (completeness likely composes with the
   NPDRF fragment).

## Decision items for the user (at arc start)

- **D1 — sequencing**: slices as ordered above, or NPDRF (slice 4)
  first since slices 3/5's statements caption against it? Recommended:
  as ordered — the law family unblocks the most, and captions can be
  updated once.
- **D2 — designation policy**: which of the new triples join the
  designated set (CURATED discipline inherited; the dsp pair is the
  natural flagship).
- **D3 — breadth target**: after slice 3, how far to scale across the
  remaining upstream channel population (34 not-imported / 15
  imported-unattempted at spec-parity close, honest 73-item tree) —
  a coverage target is a user call, not a drift default.

## Validation discipline (inherited, with one addition)

Everything from the spec-parity arc binds unchanged (guardrails first,
lockstep, envelope statements from spec text, fail closed, zero drift,
statement TCB + deletion test, non-vacuity witnesses, honest records
with figure-emitting commands, sub-branch audit cycle, arc-end
user-asked audit + Comparator). Addition: every new law's soundness is
also exercised through the CONFLUENT lane where a deterministic
concurrent program exists for its shape — the executable differential
remains the arc's distinguishing check, and a law that cannot be
exercised by any runnable program is a red flag on its own.

## Exit criterion

The six channel rows stand as compositional frame-quantified triples
(or per-row honest deferrals); the NPDRF obligation is proved or
precisely scoped; the race axis is decided and recorded; the parity
table's channel section re-states every delta both directions at the
new state; all inherited gates green; designated growth per D2 with
Comparator landmark. Deferring any goal with an honest log entry is
success; trading soundness for coverage is not.
