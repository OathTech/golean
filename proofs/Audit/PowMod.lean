import Lean
import GoLeanProofs.Examples.PowMod

/-!
# In-build axiom gate — the PowMod example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane A, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`powmod_ok` — the S2 SCALAR headline over
`powmod_harness(base, exp, mod)`** (`Examples/PowMod.lean` over the
pinned `powmodLowered`): for every `base, exp < 2^64` and every `mod`
below the source's OWN no-wrap threshold `(mod−1)² < 2⁶⁴`, past the
CONSTANT fuel bound `6027`, at EVERY nondeterminism-choice stream, the
harness run over `runFunctionWithContextM` returns exactly
`powModAnswer base exp mod = if mod = 0 then 0 else base ^ exp % mod`.

**The postcondition is MATHEMATICS, not a restatement of the loop.**
`base ^ exp % mod` is natural-number exponentiation, so the theorem is
the correctness of exponentiation by squaring. The loop-shaped function
`powLoop` is proof-side only and is bridged to the mathematics by
`powLoop_eq`; it does not appear in the headline's statement closure.

**The bound is a CONSTANT because the exponent halves.** `exp < 2^64`
needs at most 64 iterations, so one number covers the whole domain. It
is a BOUND, never presented as a measurement: the measured step count
is `139 + 72·bits(exp) + 20·popcount(exp)` (probe-verified; the two
coincide at `exp = 2⁶⁴−1`), and `59` / `68` on the two guards.

**`∀ ch` is vacuous here and stated anyway** — the subject consumes no
choice; the quantifier records that rather than hiding a `Choices`
argument.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`powmodHarnessFunc` (`rfl`-linked to the lowering by
`powmodHarnessFunc_pin`) + `powModAnswer` + `Nat`/`Int` arithmetic — no
heap vocabulary, no Iris, no Frame names, and no `powLoop`.

Deletion test RUN (`lean_minimal_hypotheses`, 2026-08-15): all five
explicit binders — `base exp mod`, `hb`, `he`, `hm`, `hnw` — are
LOAD-BEARING; dropping any one breaks the proof. Recorded honestly:
`hm` is *logically* implied by `hnw` (below the wrap threshold `mod`
cannot exceed `2^32 + 1`), and is kept as an explicit binder so the
statement reads uniformly — all three arguments in the uint64 domain,
plus the no-wrap condition. The proof does consume it.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The powmod example (Gallery Campaign G1, lane A unit 1) -/

-- Statement vocabulary
example := @GoLean.Examples.PowMod.powModAnswer
example := @GoLean.Examples.PowMod.powModFunc
example := @GoLean.Examples.PowMod.powmodHarnessFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.PowMod.powMod_pin
example := @GoLean.Examples.PowMod.powmodHarnessFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.PowMod.powLoop
example := @GoLean.Examples.PowMod.powLoop_eq
example := @GoLean.Examples.PowMod.powLoop_zero
example := @GoLean.Examples.PowMod.powLoop_step
example := @GoLean.Examples.PowMod.applyStrictOp_mul_u64
example := @GoLean.Examples.PowMod.applyStrictOp_div_u64
-- The headlines
example := @GoLean.Examples.PowMod.powmod_ok
example := @GoLean.Examples.PowMod.powmod_readout

/-- info: 'GoLean.Examples.PowMod.powmod_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powmod_ok
/-- info: 'GoLean.Examples.PowMod.powmod_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powmod_readout
/-- info: 'GoLean.Examples.PowMod.powLoop_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powLoop_eq
/-- info: 'GoLean.Examples.PowMod.powLoop_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powLoop_zero
/-- info: 'GoLean.Examples.PowMod.powLoop_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powLoop_step
/-- info: 'GoLean.Examples.PowMod.applyStrictOp_mul_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.applyStrictOp_mul_u64
/-- info: 'GoLean.Examples.PowMod.applyStrictOp_div_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.applyStrictOp_div_u64
/-- info: 'GoLean.Examples.PowMod.powMod_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powMod_pin
/-- info: 'GoLean.Examples.PowMod.powmodHarnessFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.PowMod.powmodHarnessFunc_pin

end GoLean.Iris.Audit
