import Lean
import GoLeanProofs.Examples.Stein

/-!
# In-build axiom gate — the Stein example

Per-example shard of `proofs/Audit.lean` (the sharded-audit shape,
2026-08-14). The shard imports ONLY this example's module, so a change
to another example does not re-elaborate it; it is built because the
root `Audit.lean` imports it, and `scripts/ci`'s proofs-file
audit-coverage step fails if any `proofs/**/*.lean` leaves the audited
import closure.
-/

namespace GoLean.Iris.Audit

/-! ## The stein example (gallery campaign unit G2.E3/stein, 2026-08-15)

`✓` **`stein_ok` — TOTAL harness headline, full uint64 × uint64 domain,
EXACT value** (`Examples/Stein.lean` over the pinned `steinLowered`):
for every `(a, b)`, running `stein_harness(a, b)` through the machine's
native function entry completes normally past one fuel bound at every
choice stream and returns exactly `Nat.gcd a b`. The example is
extension E3's COMPLETE consumer — its `for isEven(a) && isEven(b)`
guard rides the short-circuit normalization, pinned in the golden repr.
The MATHEMATICAL content is `steinSpec_eq_gcd` (`Examples/Stein/Pure`):
Stein's three phases as pure functions, proven equal to `Nat.gcd` from
core Lean. `stein_readout` is the D1 run-conditioned twin via the
shared bridge. -/
example := @GoLean.Examples.Stein.stein_ok
example := @GoLean.Examples.Stein.stein_readout
example := @GoLean.Examples.Stein.steinSpec_eq_gcd
example := @GoLean.Examples.Stein.stein_runs
/-- info: 'GoLean.Examples.Stein.stein_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Stein.stein_ok
/-- info: 'GoLean.Examples.Stein.steinSpec_eq_gcd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Stein.steinSpec_eq_gcd

end GoLean.Iris.Audit
