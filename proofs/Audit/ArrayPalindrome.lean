import Lean
import GoLeanProofs.Examples.ArrayPalindrome

/-!
# In-build axiom gate — the ArrayPalindrome example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane B, 2026-08-15), in the shape the phase-2 and flagship shards use.
The shard imports ONLY this example's root — which reaches every
`palin` module and, like the flagship, also reaches the HEADLINE (the
headline is stated in the root, so the C-H4/C-H5 "the aggregator cannot
see the designated theorem" shape never arises here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`palin_ok` — the S3 RELATIONAL headline over
`palin_harness_r(n, seed)`** (`Examples/ArrayPalindrome.lean` over the
pinned `palinLowered`): for every `n ≤ 8` and `seed < 2^64`, past fuel
`144·n + 298`, at EVERY nondeterminism-choice stream, the harness run
over `runFunctionWithContextM` returns TWO values — the checked array
as the fixed-cap `[8]uint64` the Go returns, and `palinSpec pre`, which
is `1` exactly when `pre.reverse = pre`. The postcondition is a
relation over RETURNED DATA; the setup family `familyMod 2` does not
appear in it.

**Where the claim's strength actually comes from.** `palinSpec` is
`if xs.reverse = xs then 1 else 0` — nothing but list reversal. The Go
program does NOT compute a reversal: it scans pairs `(t, len−1−t)` for
`t < len/2` and bails at the first disagreement. `palin_iff_half` is
the bridge between the two, and it is the only place index arithmetic
appears. `palin_verdict_iff` is the first-order readout corollary (the
statement-TCB doctrine's requirement): it states `v = 1 ↔
pre.reverse = pre` without mentioning `palinSpec` at all.

**The early return is the shape worth noting.** The subject leaves its
loop from two different places — the exit test, and a `return` inside
the body — so `ph_loopP` runs to the DRIVER TERMINAL rather than to a
loop head, and its content is that both exits deliver the same
observable. The final `i`/`j` are existentially quantified there:
they differ between the exits and nothing returned depends on them.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`palinHarnessRFunc` (`rfl`-linked to the lowering by
`palinHarnessRFunc_pin`) + `palArr8`/`palinSpec` + `List.reverse` +
`Nat`/`Int` arithmetic — no heap vocabulary, no Iris, no Frame names.
Deletion test RUN (2026-08-15, by re-elaborating the headline with each
binder removed): both explicit hypotheses are load-bearing — dropping
`hcap` breaks two goals, dropping `hseed` breaks one. No decorative
hypothesis.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The array-palindrome example (Gallery Campaign G1, lane B) -/

-- Statement vocabulary
example := @GoLean.Examples.ArrayPalindrome.palinSpec
example := @GoLean.Examples.ArrayPalindrome.palArr8
example := @GoLean.Examples.ArrayPalindrome.isPalindromeFunc
example := @GoLean.Examples.ArrayPalindrome.palinHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.ArrayPalindrome.palin_pin
example := @GoLean.Examples.ArrayPalindrome.palinHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.ArrayPalindrome.PalinUpTo
example := @GoLean.Examples.ArrayPalindrome.palin_iff_half
example := @GoLean.Examples.ArrayPalindrome.palinSpec_of_full
example := @GoLean.Examples.ArrayPalindrome.palinSpec_of_mismatch
example := @GoLean.Examples.ArrayPalindrome.su_loopP
example := @GoLean.Examples.ArrayPalindrome.cp_loopP
example := @GoLean.Examples.ArrayPalindrome.ph_loopP
example := @GoLean.Examples.ArrayPalindrome.ph_bailP
example := @GoLean.Examples.ArrayPalindrome.ph_outP
example := @GoLean.Examples.ArrayPalindrome.p_runs_generic
-- The headlines
example := @GoLean.Examples.ArrayPalindrome.palin_ok
example := @GoLean.Examples.ArrayPalindrome.palin_readout
example := @GoLean.Examples.ArrayPalindrome.palin_verdict_iff

/-- info: 'GoLean.Examples.ArrayPalindrome.palin_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palin_ok
/-- info: 'GoLean.Examples.ArrayPalindrome.palin_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palin_readout
/-- info: 'GoLean.Examples.ArrayPalindrome.palin_verdict_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palin_verdict_iff
/-- info: 'GoLean.Examples.ArrayPalindrome.p_runs_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.p_runs_generic
/-- info: 'GoLean.Examples.ArrayPalindrome.ph_loopP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.ph_loopP
/-- info: 'GoLean.Examples.ArrayPalindrome.su_loopP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.su_loopP
/-- info: 'GoLean.Examples.ArrayPalindrome.cp_loopP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.cp_loopP
/-- info: 'GoLean.Examples.ArrayPalindrome.ph_bailP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.ph_bailP
/-- info: 'GoLean.Examples.ArrayPalindrome.ph_outP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.ph_outP
/-- info: 'GoLean.Examples.ArrayPalindrome.palin_iff_half' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palin_iff_half
/-- info: 'GoLean.Examples.ArrayPalindrome.palinSpec_of_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palinSpec_of_full
/-- info: 'GoLean.Examples.ArrayPalindrome.palinSpec_of_mismatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palinSpec_of_mismatch
/-- info: 'GoLean.Examples.ArrayPalindrome.palin_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palin_pin
/-- info: 'GoLean.Examples.ArrayPalindrome.palinHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.ArrayPalindrome.palinHarnessRFunc_pin

end GoLean.Iris.Audit
