import Lean
import GoLeanProofs.Examples.Histogram

/-!
# In-build axiom gate — the Histogram example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, the
flagship example, 2026-08-15), in the shape the phase-2 shards use. The
shard imports ONLY this example's root — which reaches every histogram
module and, unlike the older examples, also reaches the HEADLINE
(the headline is stated in the root, not in a leaf shard, so the
C-H4/C-H5 "the aggregator cannot see the designated theorem" shape
never arises here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`histogram_ok` — the S3 RELATIONAL headline over
`histogram_harness_r(n, seed, q)`** (`Examples/Histogram.lean` over the
pinned `histogramLowered`): for every `n ≤ 8`, `seed < 2^64` and
`q < 2^64`, past fuel `210·n + 344`, at EVERY nondeterminism-choice
stream, the harness run over `runFunctionWithContextM` returns THREE
values — the counted values as the fixed-cap `[8]uint64` the Go
returns, `occurrences q vals`, and `distinctCount vals`. The
postcondition is a relation over RETURNED DATA; neither the setup
family `histFamily` nor any closed form appears in it.

**The ∀-choices quantifier is doing real work AND is load-bearing for
READING the claim.** `for range counts {}` consumes one pick per
iteration, so the theorem covers every map-iteration order Go could
exhibit; it holds at all of them because `distinctCount` is a function
of the returned values alone. A spec naming "the first key visited"
would be unprovable here — that unprovability is the envelope working.
The variable-free range form is also why the range loop is
state-stable: `bindIterVars` with neither binder allocates nothing, so
the machine's only per-iteration effect is "one fewer entry".

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`histHarnessRFunc` (`rfl`-linked to the lowering by
`histogramHarnessR_pin`) + `histArr8`/`occurrences`/`distinctCount` +
`Nat`/`Int` arithmetic — no heap vocabulary, no Iris, no Frame names.
Deletion test RUN (`lean_minimal_hypotheses`, 2026-08-15): all four
explicit binders are load-bearing — `n seed q`, `hcap`, `hseed` and
`hq` each break the proof when dropped, so no hypothesis is decorative.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The histogram example (Gallery Campaign G1 unit 1) -/

-- Statement vocabulary
example := @GoLean.Examples.Histogram.occurrences
example := @GoLean.Examples.Histogram.distinctCount
example := @GoLean.Examples.Histogram.histArr8
example := @GoLean.Examples.Histogram.histogramFunc
example := @GoLean.Examples.Histogram.histHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.Histogram.histogram_pin
example := @GoLean.Examples.Histogram.histogramHarnessR_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.Histogram.histFamily
example := @GoLean.Examples.Histogram.countsList
example := @GoLean.Examples.Histogram.countsList_length
example := @GoLean.Examples.Histogram.cnt_countsList'
example := @GoLean.Examples.Histogram.stepFn_pick_novars
example := @GoLean.Examples.Histogram.hg_count_loop
example := @GoLean.Examples.Histogram.hg_range_loop
example := @GoLean.Examples.Histogram.hg_runs_generic
-- The headlines
example := @GoLean.Examples.Histogram.histogram_ok
example := @GoLean.Examples.Histogram.histogram_readout

/-- info: 'GoLean.Examples.Histogram.histogram_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.histogram_ok
/-- info: 'GoLean.Examples.Histogram.histogram_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.histogram_readout
/-- info: 'GoLean.Examples.Histogram.hg_runs_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.hg_runs_generic
/-- info: 'GoLean.Examples.Histogram.hg_count_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.hg_count_loop
/-- info: 'GoLean.Examples.Histogram.hg_range_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.hg_range_loop
/-- info: 'GoLean.Examples.Histogram.stepFn_pick_novars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.stepFn_pick_novars
/-- info: 'GoLean.Examples.Histogram.countsList_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.countsList_length
/-- info: 'GoLean.Examples.Histogram.cnt_countsList'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.cnt_countsList'
/-- info: 'GoLean.Examples.Histogram.countsList_val_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.countsList_val_le
/-- info: 'GoLean.Examples.Histogram.distinctCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.distinctCount_le
/-- info: 'GoLean.Examples.Histogram.histFamily_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.histFamily_set
/-- info: 'GoLean.Examples.Histogram.histogram_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.histogram_pin
/-- info: 'GoLean.Examples.Histogram.histogramHarnessR_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.Histogram.histogramHarnessR_pin

end GoLean.Iris.Audit
