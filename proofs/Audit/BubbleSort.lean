import Lean
import GoLeanProofs.Examples.BubbleSort

/-!
# In-build axiom gate — the BubbleSort example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane B, 2026-08-15), in the shape the phase-2 and flagship shards use.
The shard imports ONLY this example's root — which reaches every
`bubble` module and, like the flagship, also reaches the HEADLINE (the
headline is stated in the root, so the C-H4/C-H5 "the aggregator
cannot see the designated theorem" shape never arises here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`bubble_ok` — the S3 RELATIONAL headline over
`bubble_harness_r(n, seed)`** (`Examples/BubbleSort.lean` over the
pinned `bubbleLowered`): for every `n ≤ 8` and `seed < 2^64`, past
fuel `(105·n + 116)·n + 174·n + 318` (QUADRATIC — bubble sort), at
EVERY nondeterminism-choice stream, the harness run over
`runFunctionWithContextM` returns TWO values — the pre-sort copy `pre`
as the fixed-cap `[8]uint64` the Go returns, and **`sortSpec pre`, THE
sorted permutation of `pre`**, as the second. The postcondition is a
relation over RETURNED DATA; the LCG setup family does not appear in
it. This is the strongest honest form the S3 harness style has
produced: the gallery's other sort (InsertionSort) returns a
Go-computed verdict `1`; `bubble` returns the DATA and relates it.

**Where the claim's strength actually comes from.** `sortSpec` is the
gallery's one definition of "the sorted permutation"
(`Examples.InsertionSort.Pure`, an insertion fold), and
`SortShared.sorted_perm_unique` — a sorted list is determined by its
element counts — makes the functional form `post = sortSpec pre` and
the first-order form "`post` is sorted ∧ counts preserved" the same
claim. `bubble_sorted_perm` is the first-order readout corollary (the
statement-TCB doctrine's requirement): `Sorted post ∧ ∀ v,
post.count v = pre.count v`, with `Sorted` the shared
`GoLean.SliceMem.Sorted`.

**The two shapes worth noting.**

* **Per-pass re-allocation**: the subject allocates a fresh
  `swapped`/`i`/`$forFirst` triple each outer pass, so the outer loop
  is carried by the executable frame theorem — each pass proven once
  at the tight placement (`bPass_swapped`/`bPass_early`), transferred
  (`transfer_seg16`), the retired triple rebased into the frame
  (`rebaseSim16`). The garbage cells are semantically inert; the
  frame theorem is precisely the tool that says so.
* **The early return**: `if !swapped { return }` gives the subject two
  ways out. `bOuter_loop` runs BOTH to the same post-call anchor; the
  pure invariant `BubbleInv` discharges sortedness at each exit — the
  counter exit from the invariant alone (`bubbleInv_finalExit`), the
  early exit from "a swap-free pass certifies a sorted prefix"
  (`bubbleInv_earlyExit` via `passB_false_adj`).

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`bubbleHarnessRFunc` (`rfl`-linked to the lowering by
`bubbleHarnessRFunc_pin`) + `bArr8V`/`sortSpec`/`Sorted`/`List.count`
+ `Nat`/`Int` arithmetic — no heap vocabulary, no Iris, no Frame names
(the frame layer is proof method below the statement line).

Deletion test RUN (2026-08-15, by re-elaborating the headline with
each binder removed): both explicit hypotheses are load-bearing —
dropping `hcap` breaks the run lemma's cap-dependent goals, dropping
`hseed` breaks the entry normalization. Recorded per binder in the
lane report.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator
Challenge's trusted closure (gallery-campaign charter §HARD
BOUNDARIES — designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The bubble-sort example (Gallery Campaign G1, lane B) -/

-- Statement vocabulary
example := @GoLean.Examples.BubbleSort.bArr8V
example := @GoLean.Examples.BubbleSort.sortSpec
example := @GoLean.Examples.BubbleSort.bubbleSortFunc
example := @GoLean.Examples.BubbleSort.bubbleHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.BubbleSort.bubble_pin
example := @GoLean.Examples.BubbleSort.bubbleHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.BubbleSort.passL
example := @GoLean.Examples.BubbleSort.passB
example := @GoLean.Examples.BubbleSort.BubbleInv
example := @GoLean.Examples.BubbleSort.bubbleInv_pass
example := @GoLean.Examples.BubbleSort.bubbleInv_earlyExit
example := @GoLean.Examples.BubbleSort.bubbleInv_finalExit
example := @GoLean.Examples.BubbleSort.bInner_loop
example := @GoLean.Examples.BubbleSort.bPass_swapped
example := @GoLean.Examples.BubbleSort.bPass_early
example := @GoLean.Examples.BubbleSort.rebaseSim16
example := @GoLean.Examples.BubbleSort.transfer_seg16
example := @GoLean.Examples.BubbleSort.bOuter_loop
example := @GoLean.Examples.BubbleSort.su_loopB
example := @GoLean.Examples.BubbleSort.cp_loopB
example := @GoLean.Examples.BubbleSort.ep_loopB
example := @GoLean.Examples.BubbleSort.bH_runs
-- The headlines
example := @GoLean.Examples.BubbleSort.bubble_ok
example := @GoLean.Examples.BubbleSort.bubble_readout
example := @GoLean.Examples.BubbleSort.bubble_sorted_perm

/-- info: 'GoLean.Examples.BubbleSort.bubble_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubble_ok
/-- info: 'GoLean.Examples.BubbleSort.bubble_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubble_readout
/-- info: 'GoLean.Examples.BubbleSort.bubble_sorted_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubble_sorted_perm
/-- info: 'GoLean.Examples.BubbleSort.bH_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bH_runs
/-- info: 'GoLean.Examples.BubbleSort.bOuter_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bOuter_loop
/-- info: 'GoLean.Examples.BubbleSort.bInner_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bInner_loop
/-- info: 'GoLean.Examples.BubbleSort.bPass_swapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bPass_swapped
/-- info: 'GoLean.Examples.BubbleSort.bPass_early' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bPass_early
/-- info: 'GoLean.Examples.BubbleSort.su_loopB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.su_loopB
/-- info: 'GoLean.Examples.BubbleSort.cp_loopB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.cp_loopB
/-- info: 'GoLean.Examples.BubbleSort.ep_loopB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.ep_loopB
/-- info: 'GoLean.Examples.BubbleSort.rebaseSim16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.rebaseSim16
/-- info: 'GoLean.Examples.BubbleSort.bubbleInv_pass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubbleInv_pass
/-- info: 'GoLean.Examples.BubbleSort.bubbleInv_earlyExit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubbleInv_earlyExit
/-- info: 'GoLean.Examples.BubbleSort.bubble_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubble_pin
/-- info: 'GoLean.Examples.BubbleSort.bubbleHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.BubbleSort.bubbleHarnessRFunc_pin

end GoLean.Iris.Audit
