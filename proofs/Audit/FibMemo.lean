import Lean
import GoLeanProofs.Examples.FibMemo

/-!
# In-build axiom gate — the FibMemo example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, HARD
LANE, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`fibmemo_ok` — the S2 SCALAR headline over
`fibmemo_harness(n)`** (`Examples/FibMemo.lean` over the pinned
`fibmemoLowered`): for every `n < 2^64`, past the fuel bound
`170·n + 107`, at EVERY nondeterminism-choice stream, the harness run
over `runFunctionWithContextM` returns exactly `fibSpec n % 2^64` —
the gallery's FIRST RECURSIVE subject, computed through a live
`map[uint64]uint64` memo consulted with the comma-ok form.

**The specification is `fibSpec`** — the designated statement
vocabulary of the existing `fib` example, imported rather than
redefined, so the gallery's "Fibonacci" means one definition. The
memoized recursion, the table model `mtbl` and the wrapped `fibW` are
proof-side and never appear in the headline's statement.

**`% 2^64` is machine-integer honesty** (the `fib` example's
`fib_total` stance): the claim covers the FULL uint64 domain, where
the additions wrap; for `n ≤ 93` the mod is the identity.

**The bound is LINEAR because the memo is load-bearing** — an
unmemoized recursion would be exponential. The proof's strong
induction (`fmCall_build`, `Examples/FibMemo/Rec.lean`) is the
campaign's NEW SHAPE: continuation-stack-parametric — the call-span
lemmas quantify over the return continuation, so each recursive
instantiation supplies the frame continuation the machine pushed one
level up, and the heap rides as an abstract sandwich (live cells /
dead frames) under a small-footprint invariant. It is a BOUND, not a
measurement: measured totals are `107` (`n ≤ 1`), `249` (`n = 2`) and
`170·n − 119` (`n ≥ 3`, probe-verified at `n = 3, 4, 5, 10`).

**`∀ ch` is vacuous here and stated anyway** — the harness consumes no
choice (the memo is only indexed, never ranged over).

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`fibmemoHarnessFunc` (`rfl`-linked to the lowering by
`fibmemoHarnessFunc_pin`) + `fibSpec` + `Nat`/`Int` arithmetic — no
heap vocabulary, no Iris, no continuation names, no `mtbl`/`fibW`.

Deletion test RUN (`lean_minimal_hypotheses`, 2026-08-15): both
explicit binders — `n` and `hn : n < 2^64` — are LOAD-BEARING;
dropping either breaks the proof.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The fibmemo example (Gallery Campaign G1, hard lane) -/

-- Statement vocabulary (fibSpec is the fib example's, by import)
example := @GoLean.Examples.Fib.fibSpec
example := @GoLean.Examples.FibMemo.fibmemoHarnessFunc
-- The lowering pins
example := @GoLean.Examples.FibMemo.fibmemoHarnessFunc_pin
example := @GoLean.Examples.FibMemo.fibMemoFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.FibMemo.fibW
example := @GoLean.Examples.FibMemo.mtbl
example := @GoLean.Examples.FibMemo.fmCall_build
example := @GoLean.Examples.FibMemo.fmCall_base
example := @GoLean.Examples.FibMemo.fmCall_hit
example := @GoLean.Examples.FibMemo.fibW_rec
example := @GoLean.Examples.FibMemo.setk_mtbl
-- The headlines
example := @GoLean.Examples.FibMemo.fibmemo_ok
example := @GoLean.Examples.FibMemo.fibmemo_readout

/-- info: 'GoLean.Examples.FibMemo.fibmemo_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fibmemo_ok
/-- info: 'GoLean.Examples.FibMemo.fibmemo_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fibmemo_readout
/-- info: 'GoLean.Examples.FibMemo.fmCall_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fmCall_build
/-- info: 'GoLean.Examples.FibMemo.fmCall_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fmCall_base
/-- info: 'GoLean.Examples.FibMemo.fmCall_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fmCall_hit
/-- info: 'GoLean.Examples.FibMemo.fibW_rec' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fibW_rec
/-- info: 'GoLean.Examples.FibMemo.setk_mtbl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.setk_mtbl
/-- info: 'GoLean.Examples.FibMemo.idxOf?_mtbl_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.idxOf?_mtbl_none
/-- info: 'GoLean.Examples.FibMemo.idxOf?_mtbl_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.idxOf?_mtbl_some
/-- info: 'GoLean.Examples.FibMemo.fibmemoHarnessFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fibmemoHarnessFunc_pin
/-- info: 'GoLean.Examples.FibMemo.fibMemoFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.FibMemo.fibMemoFunc_pin

end GoLean.Iris.Audit
