import Lean
import GoLeanProofs.Examples.SliceStack

/-!
# In-build axiom gate — the SliceStack example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane A2, 2026-08-15), in the shape the phase-2 shards use. The shard
imports ONLY this example's root — which reaches the HEADLINE, because
the headline is stated in the root rather than in a leaf shard (the
C-H4/C-H5 shape, adopted from birth).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`stack_ok` — the S3 RELATIONAL headline over
`stack_harness_r(n, seed, k)`** (`Examples/SliceStack.lean` over the
pinned `stackLowered`): for every `n ≤ 8`, EVERY `seed < 2^64`, and
EVERY `k < 2^64`, past the fuel bound `257·n + 254`, at EVERY
nondeterminism-choice stream, the harness run over
`runFunctionWithContextM` returns three values — the `n` pushed values
as a zero-padded `[8]uint64` array, `pushed.reverse.take k` (LIFO
order, truncated at what the stack holds), and the REMAINING stack
size `n − k` (Nat subtraction, truncating at zero). The postcondition
is a relation over the RETURNED data.

**`∀ ch` DOES REAL WORK — the headline honesty clause.** This is the
gallery's first non-map example (alongside `queue`) whose subject
consumes nondeterminism choices: each `append` that outgrows its
backing array draws one choice to fix the fresh capacity inside the
machine's growth envelope (`appendSpillWidth`/`appendGrowthCap`). The
proof is CAPACITY- AND ADDRESS-GENERIC — the push-loop invariant
(`PuInv`) carries an existential backing address and capacity and
never names the choice-dependent layout — so the theorem holds at
every stream and survives a re-envelope of the append growth rule that
keeps the choice arity. The step COUNT is choice-invariant
(probe-checked at three streams); the heap layout is not, and only the
count reaches the statement. The two append gap witnesses
(`st_append_inplace`, `st_append_spill`) are the machine-facing record
of the dichotomy: in-place iff the length is strictly under the
capacity, spill (one choice consumed, fresh backing) iff they are
equal.

**`∃ pushed` is family-determined**: the witness is
`stFam n seed = [seed, seed+1, …]` reduced mod 2^64; the statement
avoids saying so, exactly as Histogram's and DotProduct's headlines do.
Making the input genuine ∀-data needs the ghost rung-1 annotation,
which is designed and not built.

**The arithmetic wraps, and the claim covers the wrap region — but the
corpus's differential ceiling is BELOW the theorem's.** The theorem's
domain is the full `seed < 2^64`; the corpus's largest pinned seed is
`2^63 − 1` (row `harness-maxseed`, args `8,9223372036854775807,4`), so
`[2^63, 2^64)` is theorem-claimed but oracle-unpinned — probe-run
against the machine (`n = 1, 3, 8` at `seed = 2^64 − 1`, `n = k = 8`
at `2^64 − 2`, all matching) but not pinned against `go run`.

**The cap `n ≤ 8` is the pass-by-value observation bound** — the
program's own `stackCapN = 8` arrays. `seed`/`k` bounds are Go's
uint64 domain, not ours. **`n − k` is Nat subtraction**, truncating at
zero: the Go pops `min(k, n)` values and returns `size(s)`, so an
over-large `k` drains the stack rather than driving the count below
zero. The Go never pops an empty stack — its loop runs `min(k, n)`
times, not `k`.

**The fuel bound `257·n + 254` is a BOUND, not the exact count.** The
measured count is `242 + 130·n + 127·min(k,n) + 12·[n < k]`
(probe-confirmed at `n = 0…8` across `k` under, at, and over `n`, and
proved as `st_run`'s exact count); the shipped `N` equals it exactly
when `k > n` and is loose by `127·(n − k) + 12` when `k ≤ n`. Bound
and measurement are labelled separately; neither is presented as the
other.

Deletion test — **RUN by the LANE OWNER** (`lean_minimal_hypotheses`
on `stack_ok`), not asserted by inspection: **all FOUR explicit binder
groups are LOAD-BEARING** — the value binders `(n seed k : Nat)`,
`hcap`, `hseed` and `hk`. Dropping `hcap` leaves an `omega` unable to
discharge the fuel arithmetic; dropping `hseed` or `hk` leaves the
entry equation's uint64 normal form unproved, and `hk` additionally
feeds the `min(k, n)` comparison in the pop-count phase. Recorded
honestly: inside the internal `st_run` the seed bound is NOT consumed
(the machine wraps every stored value regardless) — it bites only at
the entry normalization, which is why it is load-bearing for the
headline and not for the run lemma.

**The three NAMED hypotheses (`hcap`, `hseed`, `hk`) are load-bearing
in three DIFFERENT senses**, separated by a machine probe RE-RUN by the
lane owner (each argument point executed against
`runFunctionWithContextM` and compared to the postcondition), because
"the proof needs it" and "the claim is false without it" are not the
same statement:

* `hcap` is a **totality** boundary — at `n = 9` the subject does not
  return at all: `panic "runtime error: index out of range [8] with
  length 8"`, so the `= .ok …` conjunct fails outright.
* `hk` is a **truth** boundary — probe counterexample at
  `n = 3, seed = 5, k = 2^64`: the machine normalizes `k` to `0`, pops
  nothing and returns remaining size `3`, while the postcondition read
  at the Nat `k = 2^64` demands the full reversed prefix and `0`.
* `hseed` is a **proof-structure** boundary only — at
  `n = 3, seed = 2^64, k = 2` the machine still MATCHES the
  postcondition (both the entry normalization and `stFam` reduce mod
  2^64, so they move together). The hypothesis is genuinely needed by
  the proof as structured (`unorm_nat_of_lt`); it is not a frontier of
  the claim. Stated because the earlier one-word verdict
  ("load-bearing") invited the stronger reading.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`stackHarnessRFunc` (`rfl`-linked to the lowering by
`stackHarnessRFunc_pin`) + `stArr8` + `List`/`Int` arithmetic — no
heap vocabulary, no Iris, no frame names, no family function.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator Challenge's
trusted closure (gallery-campaign charter §HARD BOUNDARIES —
designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The stack example (Gallery Campaign G1, proof lane A2) -/

-- Statement vocabulary
example := @GoLean.Examples.SliceStack.stArr8
example := @GoLean.Examples.SliceStack.stackHarnessRFunc
example := @GoLean.Examples.SliceStack.pushFunc
example := @GoLean.Examples.SliceStack.popFunc
example := @GoLean.Examples.SliceStack.sizeFunc
-- The lowering pins (the third link of the golden chain)
example := @GoLean.Examples.SliceStack.stackHarnessRFunc_pin
example := @GoLean.Examples.SliceStack.push_pin
example := @GoLean.Examples.SliceStack.pop_pin
example := @GoLean.Examples.SliceStack.size_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.SliceStack.stFam
example := @GoLean.Examples.SliceStack.stPopL
example := @GoLean.Examples.SliceStack.stPopL_reverse_take
example := @GoLean.Examples.SliceStack.PuInv
example := @GoLean.Examples.SliceStack.st_append_inplace
example := @GoLean.Examples.SliceStack.st_append_spill
example := @GoLean.Examples.SliceStack.st_sliceExpr_slice
example := @GoLean.Examples.SliceStack.stepFn_return_frame
example := @GoLean.Examples.SliceStack.st_run
-- The headlines
example := @GoLean.Examples.SliceStack.stack_ok
example := @GoLean.Examples.SliceStack.stack_readout

/-- info: 'GoLean.Examples.SliceStack.stack_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.stack_ok
/-- info: 'GoLean.Examples.SliceStack.stack_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.stack_readout
/-- info: 'GoLean.Examples.SliceStack.stPopL_reverse_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.stPopL_reverse_take
/-- info: 'GoLean.Examples.SliceStack.st_append_inplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.st_append_inplace
/-- info: 'GoLean.Examples.SliceStack.st_append_spill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.st_append_spill
/-- info: 'GoLean.Examples.SliceStack.st_sliceExpr_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.st_sliceExpr_slice
/-- info: 'GoLean.Examples.SliceStack.stepFn_return_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.stepFn_return_frame
/-- info: 'GoLean.Examples.SliceStack.stackHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.stackHarnessRFunc_pin
/-- info: 'GoLean.Examples.SliceStack.push_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.push_pin
/-- info: 'GoLean.Examples.SliceStack.pop_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.pop_pin
/-- info: 'GoLean.Examples.SliceStack.size_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SliceStack.size_pin

end GoLean.Iris.Audit
