import Lean
import GoLeanProofs.Examples.Gcd

/-!
# In-build axiom gate — the Gcd example

Per-example shard of `proofs/Audit.lean` (examples phase-2 slice 0,
lever 3, 2026-08-14; the per-file dependency shape of `deps/brick-wp`'s
2026-08-14 sharded audit). The `example :=` witness references and the
`#guard_msgs #print axioms` pins below are VERBATIM from the
pre-shard `Audit.lean`.

The shard imports ONLY this example's module, so a change to another
example does not re-elaborate it. It is built because the root
`Audit.lean` imports it — and `scripts/ci`'s proofs-file audit-coverage
step FAILS if any `proofs/**/*.lean` leaves the audited import closure,
so dropping that import cannot silently retire these pins.
-/

namespace GoLean.Iris.Audit

/-! ## The gcd example (scale-out slice 2c, 2026-08-13)

`✓` **`gcd_ok` — framed TOTAL, full uint64 × uint64 domain, EXACT
value** (`Examples/Gcd.lean` over the pinned `gcdLowered`): for every
`(a, b)`, beside ANY disjoint frame, execution completes normally past
one fuel bound at every choice stream, the result cell holds exactly
`Nat.gcd a b`, and every frame cell is preserved verbatim. The fib
bounded/wrapped pair COLLAPSES here — `a % b` and `Nat.gcd` cannot
wrap — recorded in the module docstring (FD-E3: no wrap exists to
state). Route (recorded): direct machine-step segments, one strong
induction on the `b`-value (the §5c non-unit ≤-decrease realized
directly; the `%` divide-by-zero branch discharged by the private
executable fact `applyStrictOp_mod_u64`). `gcd_readout` is the D1
run-conditioned twin, derived via `normal_readout_of_total` — the new
shared bridge (this commit; gcd_readout is its same-commit discharge
witness): a total headline already determines every normal completion
(`execStmt` is a function; success is fuel-monotone with the same
result). Scope honesty: usability evidence per the charter's
two-questions separation. -/
example := @GoLean.Surface.normal_readout_of_total
-- HARNESS RESTATEMENT (form note §11, 2026-08-13): `gcd_ok` is now the
-- harness headline over `runFunctionWithContextM` (three-phase
-- gcd_harness; full uint64² domain, exact Nat.gcd, returned data);
-- the memory-quantified forms are KEPT proof-side as `gcd_framed` /
-- `gcd_framed_readout` (renamed, ruling (a)).
example := @GoLean.Examples.Gcd.gcd_ok
example := @GoLean.Examples.Gcd.gcd_readout
example := @GoLean.Examples.Gcd.gcd_framed
example := @GoLean.Examples.Gcd.gcd_framed_readout
/-- info: 'GoLean.Examples.Gcd.gcd_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Gcd.gcd_ok
/-- info: 'GoLean.Examples.Gcd.gcd_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Gcd.gcd_framed

end GoLean.Iris.Audit
