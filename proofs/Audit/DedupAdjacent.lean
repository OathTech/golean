import Lean
import GoLeanProofs.Examples.DedupAdjacent

/-!
# In-build axiom gate — the DedupAdjacent example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane A, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`dedup_ok` — the S3 RELATIONAL headline over
`dedup_harness_r(n, seed)`** (`Examples/DedupAdjacent.lean` over the
pinned `dedupLowered`): for every `n ≤ 8` and `seed < 2⁶⁴`, past the
fuel bound `263·n + 361`, at EVERY nondeterminism-choice stream, the
harness run over `runFunctionWithContextM` returns exactly three
values — a length-`n` list `vals` (zero-padded to the fixed cap 8),
`dedupAdj vals` (zero-padded the same way), and
`(dedupAdj vals).length`.

**The postcondition is the ADJACENT-only dedup, as mathematics.**
`dedupAdj` keeps an element iff it is FIRST or differs from the last
KEPT one — a recursion over `List Int`, never a restatement of the
two-pointer loop. Only runs of equal NEIGHBOURS collapse: `1,2,1,2`
maps to itself. That is the classic misreading of this subject, pinned
differentially by the corpus row `four-alternating`, and the machine
bridge is the in-place invariant (kept prefix = the answer so far,
tail untouched, the stale middle never read) proved in `sj_loopD`.

**`∃ vals` is family-determined.** The witness is `ddFamily n seed`
(`vals[i] = seed + i/2` wrapped at uint64 — adjacent pairs repeat, so
both subject branches run at every `n ≥ 3`); the statement merely
avoids saying so. The wrap is part of the family BY DESIGN.

**The bound is a BOUND, never presented as a measurement.**
`N = 263·n + 361` charges every element the widest subject branch. The
MEASURED step count is `361` at `n = 0` and `177·n + 86·K + 343` for
`n ≥ 1` with `K` the survivor count (probe-verified at `n = 0, 1, 5,
8`: 361, 606, 1486, 2103; the family gives `K = ⌈n/2⌉`).

**`∀ ch` is vacuous here and stated anyway** — the subject consumes no
choice; the quantifier records that rather than hiding a `Choices`
argument.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`dedupHarnessRFunc` (`rfl`-linked to the lowering by
`dedupHarnessRFunc_pin`) + `dedupAdj`/`ddArr8` + `Nat`/`Int`/`List`
vocabulary — no heap vocabulary, no Iris, no Frame names, and no
machine-loop function.

Deletion test RUN (`lean_minimal_hypotheses`, lane owner, 2026-08-15 —
re-run rather than inherited from the proof author, who had checked it
by hand): all THREE explicit binders — `n seed`, `hcap`, `hseed` — are
LOAD-BEARING; dropping any one breaks the proof. `hcap` bounds every
loop and the fixed-cap array stores; `hseed` discharges the entry
normalization of the `seed` argument. Neither is decorative.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator
Challenge's trusted closure (gallery-campaign charter §HARD
BOUNDARIES — designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The dedup example (Gallery Campaign G1, lane A) -/

-- Statement vocabulary
example := @GoLean.Examples.DedupAdjacent.dedupAdj
example := @GoLean.Examples.DedupAdjacent.dedupAdjTail
example := @GoLean.Examples.DedupAdjacent.ddArr8
example := @GoLean.Examples.DedupAdjacent.dedupAdjacentFunc
example := @GoLean.Examples.DedupAdjacent.dedupHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.DedupAdjacent.dedupAdjacent_pin
example := @GoLean.Examples.DedupAdjacent.dedupHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.DedupAdjacent.ddFamily
example := @GoLean.Examples.DedupAdjacent.dedupAdj_snoc
example := @GoLean.Examples.DedupAdjacent.dedupAdj_getLast?
example := @GoLean.Examples.DedupAdjacent.sj_loopD
example := @GoLean.Examples.DedupAdjacent.applyStrictOp_div_u64
example := @GoLean.Examples.DedupAdjacent.applyStrictOp_sliceExpr_slice
-- The headlines
example := @GoLean.Examples.DedupAdjacent.dedup_ok
example := @GoLean.Examples.DedupAdjacent.dedup_readout

/-- info: 'GoLean.Examples.DedupAdjacent.dedup_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.dedup_ok
/-- info: 'GoLean.Examples.DedupAdjacent.dedup_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.dedup_readout
/-- info: 'GoLean.Examples.DedupAdjacent.dedupAdj_snoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.dedupAdj_snoc
/-- info: 'GoLean.Examples.DedupAdjacent.dedupAdj_getLast?' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.dedupAdj_getLast?
/-- info: 'GoLean.Examples.DedupAdjacent.sj_loopD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.sj_loopD
/-- info: 'GoLean.Examples.DedupAdjacent.applyStrictOp_div_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.applyStrictOp_div_u64
/-- info: 'GoLean.Examples.DedupAdjacent.applyStrictOp_sliceExpr_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.applyStrictOp_sliceExpr_slice
/-- info: 'GoLean.Examples.DedupAdjacent.dedupAdjacent_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.dedupAdjacent_pin
/-- info: 'GoLean.Examples.DedupAdjacent.dedupHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.DedupAdjacent.dedupHarnessRFunc_pin

end GoLean.Iris.Audit
