import Lean
import GoLeanProofs.Examples.Reverse

/-!
# In-build axiom gate — the Reverse example

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

/-! ## The reverse exemplar (slice 2b, 2026-08-13)

`✓` **`reverse_ok` — the §9e memory-input headline, completion split
CLOSED** (`Examples/Reverse.lean` over the pinned `reverseLowered`;
design note §9e + the executable frame theorem). For any `[]uint64`
input list, at ANY placement (`base`), beside ANY disjoint frame:
execution completes normally past one fuel bound at every choice
stream, the backing cell holds the reversal, and every frame cell is
preserved verbatim. Statement deltas vs the §9e draft, recorded in the
module: `hlen : xs.length < 2^63` added (with completion IN the
statement the draft is false past Go's `int` domain — the driver's
bounds check panics); the ∀-placement is realized by the
input-RELOCATING renaming `relocShift` through the frame theorem's
generalized `ShiftSpec` (build-handoff §3 finding 1's payoff,
consumed). Proof route (recorded): direct machine-step segments +
strong induction on the two-pointer measure — one induction delivers
value AND completion; the Iris WP slice laws are witnessed separately
(block above) and deliberately not consumed here. Scope honesty:
usability evidence per the charter's two-questions separation. -/
-- HARNESS RESTATEMENT (form note §11): `reverse_ok` is now the harness
-- headline (reverse_harness: setup family s[i] = seed + i wrapping;
-- Go-side element-wise reversal check → verdict 1; input-family
-- honesty recorded). The memory-quantified ∀xs form above is KEPT
-- proof-side as `reverse_framed` (renamed; genuinely stronger on the
-- input quantifier — which is why it stays).
example := @GoLean.Examples.Reverse.reverse_ok
example := @GoLean.Examples.Reverse.reverse_framed
example := @GoLean.Examples.Reverse.revFamily
example := @GoLean.Examples.Reverse.reverseHarnessFunc
example := @GoLean.Examples.Reverse.reverse_readout
/-- info: 'GoLean.Examples.Reverse.reverse_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Reverse.reverse_ok
/-- info: 'GoLean.Examples.Reverse.reverse_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Reverse.reverse_framed

end GoLean.Iris.Audit
