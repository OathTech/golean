import Lean
import GoLeanProofs.Examples.TwoSum

/-!
# In-build axiom gate — the TwoSum example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane B, 2026-08-15), in the shape the phase-2 and flagship shards use.
The shard imports ONLY this example's root — which reaches every
`twosum` module and, like the flagship, also reaches the HEADLINE (the
headline is stated in the root, so the C-H4/C-H5 "the aggregator cannot
see the designated theorem" shape never arises here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`twosum_ok` — the S3 RELATIONAL headline over
`twosum_harness_r(n, seed, target)`** (`Examples/TwoSum.lean` over the
pinned `twosumLowered`): for every `n ≤ 8`, `seed < 2^64` and
`target < 2^64`, past fuel `57·n² + 212·n + 303`, at EVERY
nondeterminism-choice stream, the harness run over
`runFunctionWithContextM` returns THREE values — the searched array as
the fixed-cap `[8]uint64` the Go returns, and the index pair
`twoSumSpec vals target`: the FIRST pair `(i, j)` in scan order with
`i < j < n` and `(vals[i] + vals[j]) % 2^64 = target`, or the sentinel
`(n, n)` when no pair hits. The postcondition is a relation over
RETURNED DATA; the setup family `tsFamily` does not appear in it.

**Where the claim's strength actually comes from.** `twoSumSpec` is a
first-search recursion (`findFrom` inner scan, `findPair` outer), so
by itself it is program-shaped; the mathematical content is
`twoSumSpec_char` — the full first-order characterisation: the named
pair hits and NO scan-earlier pair hits, or the sentinel is returned
and NO pair hits at all. `twosum_first_pair` is the first-order
readout corollary (the statement-TCB doctrine's requirement): it
states that disjunction over the returned values without mentioning
`twoSumSpec` at all.

**The nested loop is the shape worth noting.** Each outer iteration of
`twoSum` allocates a FRESH inner counter and loop flag, so the inner
loop's live cells sit at symbolic addresses past a growing dead
region. The subject-phase proofs thread an abstract dead-region
parameter with `StepKit.DeadFrom` freshness (`ts_alloc`, `ts_inIter`,
`ts_inHit`); the early `return` out of the INNER loop runs to the
DRIVER TERMINAL through both loop continuations (`ts_rowHit`), and the
outer strong induction `ts_outerP` carries the answer function `tsAnsF`
instead of threading an invariant. The fuel bound is QUADRATIC —
`57·n² + 212·n + 303` — the honest cost of the O(n²) subject.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`twosumHarnessRFunc` (`rfl`-linked to the lowering by
`twosumHarnessRFunc_pin`) + `tsArr8`/`twoSumSpec` + `List.getD` +
`Int.emod` + `Nat`/`Int` arithmetic — no heap vocabulary, no Iris, no
frame names. Deletion test RUN (2026-08-15, by re-elaborating the
headline with each explicit binder removed): all three hypotheses are
load-bearing — dropping `hcap` breaks two sites (the run lemma and the
entry-normalization `omega`), dropping `hseed` breaks two, dropping
`htgt` breaks two. No decorative hypothesis.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The two-sum example (Gallery Campaign G1, lane B) -/

-- Statement vocabulary
example := @GoLean.Examples.TwoSum.twoSumSpec
example := @GoLean.Examples.TwoSum.tsArr8
example := @GoLean.Examples.TwoSum.twoSumFunc
example := @GoLean.Examples.TwoSum.twosumHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.TwoSum.twoSum_pin
example := @GoLean.Examples.TwoSum.twosumHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.TwoSum.findFrom
example := @GoLean.Examples.TwoSum.findPair
example := @GoLean.Examples.TwoSum.twoSumSpec_char
example := @GoLean.Examples.TwoSum.tsFamily
example := @GoLean.Examples.TwoSum.tsAnsF
example := @GoLean.Examples.TwoSum.ts_alloc
example := @GoLean.Examples.TwoSum.ts_inIter
example := @GoLean.Examples.TwoSum.ts_inHit
example := @GoLean.Examples.TwoSum.ts_rowMiss
example := @GoLean.Examples.TwoSum.ts_rowHit
example := @GoLean.Examples.TwoSum.ts_outerP
example := @GoLean.Examples.TwoSum.su_loopT
example := @GoLean.Examples.TwoSum.cp_loopT
example := @GoLean.Examples.TwoSum.ts_runT
-- The headlines
example := @GoLean.Examples.TwoSum.twosum_ok
example := @GoLean.Examples.TwoSum.twosum_readout
example := @GoLean.Examples.TwoSum.twosum_first_pair

/-- info: 'GoLean.Examples.TwoSum.twosum_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.twosum_ok
/-- info: 'GoLean.Examples.TwoSum.twosum_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.twosum_readout
/-- info: 'GoLean.Examples.TwoSum.twosum_first_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.twosum_first_pair
/-- info: 'GoLean.Examples.TwoSum.ts_runT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.ts_runT
/-- info: 'GoLean.Examples.TwoSum.ts_outerP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.ts_outerP
/-- info: 'GoLean.Examples.TwoSum.ts_rowHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.ts_rowHit
/-- info: 'GoLean.Examples.TwoSum.ts_rowMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.ts_rowMiss
/-- info: 'GoLean.Examples.TwoSum.ts_inHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.ts_inHit
/-- info: 'GoLean.Examples.TwoSum.ts_inIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.ts_inIter
/-- info: 'GoLean.Examples.TwoSum.su_loopT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.su_loopT
/-- info: 'GoLean.Examples.TwoSum.cp_loopT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.cp_loopT
/-- info: 'GoLean.Examples.TwoSum.twoSumSpec_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.twoSumSpec_char
/-- info: 'GoLean.Examples.TwoSum.findPair_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.findPair_some
/-- info: 'GoLean.Examples.TwoSum.findPair_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.findPair_none
/-- info: 'GoLean.Examples.TwoSum.twoSum_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.twoSum_pin
/-- info: 'GoLean.Examples.TwoSum.twosumHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.TwoSum.twosumHarnessRFunc_pin

end GoLean.Iris.Audit
