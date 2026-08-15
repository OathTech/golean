import Lean
import GoLeanProofs.Examples.Sieve

/-!
# In-build axiom gate — the Sieve example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, HARD
LANE, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`sieve_ok` — the S2 SCALAR headline over `sieve_harness(n)`**
(`Examples/Sieve.lean` over the pinned `sieveLowered`): for every
`n < 2^62`, past the fuel bound `(n+1)·(49·(n+1) + 261) + 300`, at
EVERY nondeterminism-choice stream, the harness run over
`runFunctionWithContextM` returns exactly `primeCount n` — the number
of primes `≤ n`, with primality defined by TRIAL DIVISION.

**The specification is mathematics, not a loop restatement.**
`primeCount`/`isPrime` (`Examples/Sieve/Pure.lean`) enumerate divisors;
the theorem therefore carries the sieve of Eratosthenes' own
correctness — that marking multiples of the unmarked `i` with
`i·i ≤ n` marks exactly the composites (`sieveTable_spec`, whose core
is the least-prime-factor argument `p·p ≤ k` for composite `k`). The
loop mirrors (`markFrom`/`sieveOuter`/`countFrom`) are proof-side.

**`n < 2^62` is the program's own arithmetic**: the outer guard
computes `i·i` and near `2^64` that multiply WRAPS, making the program
compute something else; below `2^62` every machine integer in the run
stays under the threshold. The theorem deliberately withholds the wrap
region.

**The subject is the campaign's dynamic-allocation example**:
`make([]bool, n+1)` at a SYMBOLIC length, a nested loop whose inner
trip count depends on the outer index, and per-pass scratch cells at
symbolic addresses — the machine half (`Examples/Sieve/Machine.lean`)
carries them in the footprint style the FibMemo unit introduced.

**The bound is a BOUND, not a measurement**: a deliberately generous
quadratic over-charge. Measured totals: 55 / 279 / 340 / 1174 / 3296
at `n = 0, 2, 3, 10, 30`; the bound evaluates to 610 / 1524 / 2128 /
9100 / 55480 there.

**`∀ ch` is vacuous here and stated anyway** — the run consumes no
choice.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`sieveHarnessFunc` (`rfl`-linked to the lowering by
`sieveHarnessFunc_pin`) + `primeCount` + `Nat`/`Int` arithmetic — no
heap vocabulary, no Iris, no loop-mirror names.

Deletion test RUN (`lean_minimal_hypotheses`, 2026-08-15): both
explicit binders — `n` and `hn : n < 2^62` — are LOAD-BEARING;
dropping either breaks the proof.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The sieve example (Gallery Campaign G1, hard lane) -/

-- Statement vocabulary
example := @GoLean.Examples.Sieve.isPrime
example := @GoLean.Examples.Sieve.primeCount
example := @GoLean.Examples.Sieve.sieveHarnessFunc
-- The lowering pins
example := @GoLean.Examples.Sieve.sieveHarnessFunc_pin
example := @GoLean.Examples.Sieve.countPrimes_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.Sieve.markFrom
example := @GoLean.Examples.Sieve.sieveOuter
example := @GoLean.Examples.Sieve.countFrom
example := @GoLean.Examples.Sieve.sieveTable_spec
example := @GoLean.Examples.Sieve.sieveAnswer_eq
example := @GoLean.Examples.Sieve.sv_runs
-- The headlines
example := @GoLean.Examples.Sieve.sieve_ok
example := @GoLean.Examples.Sieve.sieve_readout

/-- info: 'GoLean.Examples.Sieve.sieve_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sieve_ok
/-- info: 'GoLean.Examples.Sieve.sieve_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sieve_readout
/-- info: 'GoLean.Examples.Sieve.sieveTable_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sieveTable_spec
/-- info: 'GoLean.Examples.Sieve.sieveAnswer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sieveAnswer_eq
/-- info: 'GoLean.Examples.Sieve.sv_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sv_runs
/-- info: 'GoLean.Examples.Sieve.sv_mark_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sv_mark_loop
/-- info: 'GoLean.Examples.Sieve.sv_outer_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sv_outer_loop
/-- info: 'GoLean.Examples.Sieve.sv_count_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sv_count_loop
/-- info: 'GoLean.Examples.Sieve.storeTarget_slice_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.storeTarget_slice_bool
/-- info: 'GoLean.Examples.Sieve.sieveHarnessFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.sieveHarnessFunc_pin
/-- info: 'GoLean.Examples.Sieve.countPrimes_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.Sieve.countPrimes_pin

end GoLean.Iris.Audit
