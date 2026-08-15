import Lean
import GoLeanProofs.Examples.Kadane

/-!
# In-build axiom gate — the Kadane example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane A, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`kadane_ok` — the S3 RELATIONAL headline over
`kadane_harness_r(n, seed)`, the wave's only SIGNED (int64) example**
(`Examples/Kadane.lean` over the pinned `kadaneLowered`): for every
`n ≤ 8` and every `seed` in the no-wrap window `-2⁵⁹ ≤ seed ≤ 2⁵⁹`,
past the fuel bound `227·n + 220`, at EVERY nondeterminism-choice
stream, the harness run over `runFunctionWithContextM` returns TWO
values — a length-`n` list `vals` as the fixed-cap `[8]int64` array
the Go returns, and `.int (maxSubarraySum vals) .int64`.

**The postcondition is MATHEMATICS, not a restatement of the scan.**
`maxSubarraySum` enumerates every non-empty contiguous segment
(`segments`, via `nePrefixes`) and takes the greatest sum
(`List.max?`), with `0` for the empty list — the Go source's own
documented empty-slice definition. The scan-shaped functions
`kadCur`/`kadBest` are proof-side only, bridged to the mathematics by
`kadCur_eq_maxEnd`/`kadBest_eq_maxSub`; they do not appear in the
headline's statement closure.

**The domain window is a no-wrap bound** (machine-integer honesty,
FD-E3): family values are `±(seed + i)` with `i < 8`, and the scan's
`cur`/`best` are sums of at most 8 of them (`kad_bounds`), so no int64
operation wraps on the stated domain; outside it the answer is NOT the
mathematical maximum, and the corpus pins that region differentially.

**The fuel bound `227·n + 220` is a BOUND, never a measurement**: it
is the branch-uniform worst case (odd setup iterations 86 vs even 66;
scan iterations up to 88). The MEASURED step counts at `seed = 5` are
`213, 427, 642, 845, 1060, 1263, 1478, 1681, 1896` for `n = 0 … 8` —
input-dependent through the branch structure, so no affine law is
quoted.

**`∀ ch` is vacuous here and stated anyway** — the subject consumes no
choice; the quantifier records that rather than hiding a `Choices`
argument. **`∃ vals` is family-determined** (witness
`kadFamily n seed`); the statement merely avoids saying so.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`kadaneHarnessRFunc` (`rfl`-linked to the lowering by
`kadaneHarnessRFunc_pin`; the subject by `kadane_pin`) +
`maxSubarraySum`/`segments`/`nePrefixes` + `kadArr8` +
`Nat`/`Int`/`List` vocabulary — no heap vocabulary, no Iris, no kit
names, and no `kadCur`/`kadBest`.

Deletion test RUN (`lean_minimal_hypotheses`, lane owner, 2026-08-15 —
re-run rather than inherited from the proof author, who had checked it
by hand): ALL FIVE explicit binders — `n`, `seed`, `hcap : n ≤ 8`, and
`hs1`/`hs2` (the seed window) — are LOAD-BEARING; dropping any one
breaks the proof. `hcap` feeds the padded-prefix lengths and the
`kad_bounds` instantiation; the window feeds every int64
normalization-collapse step.

**What the seed window costs, stated plainly.** `-2⁵⁹ ≤ seed ≤ 2⁵⁹` is
NOT Go's int64 domain — it is a no-wrap window, and it is narrower than
the corpus. Of the six relational-harness rows, FOUR
(`harness-r-empty`, `-one`, `-mid`, `-eight`) lie inside the theorem's
domain and TWO (`harness-r-maxseed` at `2⁶³−1`, `harness-r-minseed` at
`−2⁶³`) lie OUTSIDE it: those two runs are pinned differentially and
are not claimed here. Attribution: the program's own arithmetic — the
family values are `±(seed+i)` and the running sums can reach `m·|seed|`,
so the window is what keeps every int64 `normalize` an identity.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator
Challenge's trusted closure (gallery-campaign charter §HARD
BOUNDARIES — designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The kadane example (Gallery Campaign G1, lane A) -/

-- Statement vocabulary
example := @GoLean.Examples.Kadane.maxSubarraySum
example := @GoLean.Examples.Kadane.segments
example := @GoLean.Examples.Kadane.nePrefixes
example := @GoLean.Examples.Kadane.kadArr8
example := @GoLean.Examples.Kadane.kadaneFunc
example := @GoLean.Examples.Kadane.kadaneHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.Kadane.kadane_pin
example := @GoLean.Examples.Kadane.kadaneHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.Kadane.kadCur
example := @GoLean.Examples.Kadane.kadBest
example := @GoLean.Examples.Kadane.kadCur_eq_maxEnd
example := @GoLean.Examples.Kadane.kadBest_eq_maxSub
example := @GoLean.Examples.Kadane.kadBest_spec
example := @GoLean.Examples.Kadane.kad_bounds
example := @GoLean.Examples.Kadane.kadFamily
-- The int64 gap-witness family (kit gap `i64-ops`)
example := @GoLean.Examples.Kadane.inorm64_of_range
example := @GoLean.Examples.Kadane.storeTarget_slice_i64
example := @GoLean.Examples.Kadane.storeTarget_arrayLocal_i64
example := @GoLean.Examples.Kadane.normalizeValueForTy_arr_i64
example := @GoLean.Examples.Kadane.stepFn_makeSlice_i64_step
-- The headlines
example := @GoLean.Examples.Kadane.kadane_ok
example := @GoLean.Examples.Kadane.kadane_readout

/-- info: 'GoLean.Examples.Kadane.kadane_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadane_ok
/-- info: 'GoLean.Examples.Kadane.kadane_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadane_readout
/-- info: 'GoLean.Examples.Kadane.kadBest_eq_maxSub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadBest_eq_maxSub
/-- info: 'GoLean.Examples.Kadane.kadCur_eq_maxEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadCur_eq_maxEnd
/-- info: 'GoLean.Examples.Kadane.kadBest_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadBest_spec
/-- info: 'GoLean.Examples.Kadane.kad_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kad_bounds
/-- info: 'GoLean.Examples.Kadane.inorm64_of_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.inorm64_of_range
/-- info: 'GoLean.Examples.Kadane.storeTarget_slice_i64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.storeTarget_slice_i64
/-- info: 'GoLean.Examples.Kadane.storeTarget_arrayLocal_i64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.storeTarget_arrayLocal_i64
/-- info: 'GoLean.Examples.Kadane.normalizeValueForTy_arr_i64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.normalizeValueForTy_arr_i64
/-- info: 'GoLean.Examples.Kadane.stepFn_makeSlice_i64_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.stepFn_makeSlice_i64_step
/-- info: 'GoLean.Examples.Kadane.kadane_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadane_pin
/-- info: 'GoLean.Examples.Kadane.kadaneHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.Kadane.kadaneHarnessRFunc_pin

end GoLean.Iris.Audit
