import Lean
import GoLeanProofs.Examples.RunLength

/-!
# In-build axiom gate — the RunLength example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane B, 2026-08-15), in the shape the phase-2 and flagship shards use.
The shard imports ONLY this example's root — which reaches every `rle`
module and, like the flagship, also reaches the HEADLINE (the headline
is stated in the root, so the C-H4/C-H5 "the aggregator cannot see the
designated theorem" shape never arises here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`rle_ok` — the S3 RELATIONAL headline over
`rle_harness_r(n, seed)`** (`Examples/RunLength.lean` over the pinned
`rleLowered`): for every `n ≤ 3` and `seed < 2^64`, past fuel
`253·n + 527`, at EVERY nondeterminism-choice stream, the harness run
over `runFunctionWithContextM` returns FOUR values — the encoded input
`pre` as the fixed-cap `[8]uint64` the Go returns, `runVals` and
`runCounts` as the value/count projections of `rleSpec pre`
(zero-padded to cap), and the run count `k = (rleSpec pre).length`.
The postcondition is a relation over RETURNED DATA; the setup family
`seed + i/3` does not appear in it.

**Where the claim's strength actually comes from.** `rleSpec` is the
structural run-length encoding — grouped maximal runs — and
`rleSpec_decode` proves, generally, that expanding the encoding
reproduces the input; `rle_decode` is the first-order readout
corollary (the statement-TCB doctrine's requirement): the returned
`(vals, counts)` lists have equal length `k` and expanding each pair
back into a run reproduces the returned `pre`, with no mention of
`rleSpec` in the statement.

**The `append` spill is the shape worth noting.** The subject builds
its output slices with `append`; the machine's `appendSlice` SPILL
draws the fresh backing's capacity from the choice stream (envelope
`[newLen, max 32 (2·growth)] = [1, 32]` at this example's two spill
sites). `applyStmtOp_append_spill1` surfaces that choice as an
EXISTENTIAL capacity with only the envelope bounds, both capacities are
carried symbolically through every downstream heap front, and the
headline's `∀ ch` therefore ranges over the whole admitted envelope —
nothing returned depends on the draw.

**The `n ≤ 3` cap is a RECORDED HONEST GAP, not the harness's bound.**
The harness itself caps at `n ≤ 8`; `n ∈ [4, 8]` is unproven because
at the second new-run event the spill-or-in-place branch depends on the
FIRST spill's choice-drawn capacity, so every later allocation address
is choice-dependent — beyond literal-address raw segments without new
kit machinery (`HarnessR` module docstring + the campaign log's kit-gap
entry). The theorem does not speak about `n > 3`; nothing fails open.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`rleHarnessRFunc` (`rfl`-linked to the lowering by
`rleHarnessRFunc_pin`) + `rleArr8`/`rleSpec` + `List` operations +
`Nat`/`Int` arithmetic — no heap vocabulary, no Iris, no Frame names.
Deletion test RUN (2026-08-15, by re-elaborating the headline with each
binder removed): both explicit hypotheses are load-bearing — dropping
`hcap` breaks the `n`-case split (1 error), dropping `hseed` breaks the
seed-argument normalization in every case (4 errors). No decorative
hypothesis.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The run-length example (Gallery Campaign G1, lane B) -/

-- Statement vocabulary
example := @GoLean.Examples.RunLength.rleSpec
example := @GoLean.Examples.RunLength.rleArr8
example := @GoLean.Examples.RunLength.rleFunc
example := @GoLean.Examples.RunLength.rleHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.RunLength.rle_pin
example := @GoLean.Examples.RunLength.rleHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.RunLength.rleSpec_decode
example := @GoLean.Examples.RunLength.rleSpec_const_form
example := @GoLean.Examples.RunLength.rleFamily
example := @GoLean.Examples.RunLength.applyStrictOp_div_u64
example := @GoLean.Examples.RunLength.buildAppendBackingValue_one
example := @GoLean.Examples.RunLength.applyStmtOp_append_spill1
example := @GoLean.Examples.RunLength.r_iter0C
example := @GoLean.Examples.RunLength.r_extC37
example := @GoLean.Examples.RunLength.r_extC39
example := @GoLean.Examples.RunLength.q_frontC
example := @GoLean.Examples.RunLength.q_runs0
example := @GoLean.Examples.RunLength.q_runs1
example := @GoLean.Examples.RunLength.q_runs2
example := @GoLean.Examples.RunLength.q_runs3
-- The headlines
example := @GoLean.Examples.RunLength.rle_ok
example := @GoLean.Examples.RunLength.rle_readout
example := @GoLean.Examples.RunLength.rle_decode

/-- info: 'GoLean.Examples.RunLength.rle_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.rle_ok
/-- info: 'GoLean.Examples.RunLength.rle_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.rle_readout
/-- info: 'GoLean.Examples.RunLength.rle_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.rle_decode
/-- info: 'GoLean.Examples.RunLength.rleSpec_decode' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.rleSpec_decode
/-- info: 'GoLean.Examples.RunLength.applyStmtOp_append_spill1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.applyStmtOp_append_spill1
/-- info: 'GoLean.Examples.RunLength.q_runs0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.q_runs0
/-- info: 'GoLean.Examples.RunLength.q_runs1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.q_runs1
/-- info: 'GoLean.Examples.RunLength.q_runs2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.q_runs2
/-- info: 'GoLean.Examples.RunLength.q_runs3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.q_runs3
/-- info: 'GoLean.Examples.RunLength.rle_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.rle_pin
/-- info: 'GoLean.Examples.RunLength.rleHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.RunLength.rleHarnessRFunc_pin

end GoLean.Iris.Audit

