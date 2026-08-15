import Lean
import GoLeanProofs.Examples.SelectionSort

/-!
# In-build axiom gate — the SelectionSort example

Per-example shard of `proofs/Audit.lean` (Gallery Campaign G1, proof
lane B, 2026-08-15), in the shape the phase-2 and flagship shards use.
The shard imports ONLY this example's root — which reaches every
`selsort` module and the HEADLINE (stated in the root, so the
C-H4/C-H5 "the aggregator cannot see the designated theorem" shape
never arises here).

It is built because the root `Audit.lean` imports it — and
`scripts/ci`'s proofs-file audit-coverage step FAILS if any
`proofs/**/*.lean` leaves the audited import closure, so dropping that
import cannot silently retire these pins.

`✓` **`selsort_ok` — the S3 RELATIONAL headline over
`selsort_harness_r(n, seed)`** (`Examples/SelectionSort.lean` over the
pinned `selsortLowered`): for every `n ≤ 8` and `seed < 2^64`, past
fuel `(67·n + 145)·n + 174·n + 318`, at EVERY nondeterminism-choice
stream, the harness run over `runFunctionWithContextM` returns TWO
values — the input `pre` and `post = sortSpec pre`, THE sorted
permutation of `pre`, both as the fixed-cap `[8]uint64` arrays the Go
returns. This is the sorted-permutation claim over RETURNED DATA: the
gallery's other sort (InsertionSort) returns a Go-computed verdict
`1`; this harness returns the data itself and the theorem relates it.

**Where the claim's strength actually comes from.** `sortSpec` is the
insertion fold from `Examples.InsertionSort.Pure` — the gallery's ONE
definition of "the sorted permutation" (`SortShared`'s recorded
cross-example import). The Go program does NOT compute an insertion
fold: it selects successive minima and swaps in place. The bridge is
`SortShared.sorted_perm_unique` (a sorted list is determined by its
counts): the machine induction reaches `Sorted lf ∧ counts preserved`
(the selection invariant `PrefixSorted`/`PrefixLE`, advanced per pass
by `swap_advance` at the inner scan's `minIdx` exit), and
`eq_sortSpec_of_sorted_count` converts to the functional form.
`selsort_sorted_count` is the first-order readout corollary (the
statement-TCB doctrine's requirement): `Sorted post ∧ ∀ v,
post.count v = pre.count v`, no `sortSpec` anywhere.

**The nested reallocation is the shape worth noting.** Every outer
pass allocates a FRESH `m`/`j`/`$forFirst` triple (probe-verified;
`nextAddr` grows by 3 per pass, dead cells persist), so the pass is
proven once at the tight canonical placement and moved to the true
placement by the executable frame theorem, the triple REBASED into the
frame between passes (`rebaseSim3`, threshold 16, retire 3 — the
InsertionSort `rebaseSim11` pattern at this example's deeper prefix).
The post phase is proven canonically and transferred in ONE
`transfer_seg16` application; the result cells (2/3) are read back
through the final frame simulation.

Statement closure: interpreter/native-entry vocabulary
(`runFunctionWithContextM`, `Choices`, `Result`) + the pinned
`selsortHarnessRFunc` (`rfl`-linked to the lowering by
`selsortHarnessRFunc_pin`) + `selArr8`/`sortSpec`/`SliceMem.Sorted` +
`List.count` + `Nat`/`Int` arithmetic — no heap vocabulary, no Iris,
no Frame names in any statement.
Deletion test RUN (2026-08-15, by re-elaborating the headline with
each binder removed, `.tmp/del_hcap.lean`/`.tmp/del_hseed.lean`): both
explicit hypotheses are load-bearing — dropping `hcap` breaks TWO
goals (the run theorem's cap discharge and the `n`-argument
normalization rewrite), dropping `hseed` breaks TWO goals (the run
theorem's seed discharge and the `seed`-argument normalization
rewrite). No decorative hypothesis.

NOT DESIGNATED: this example is deliberately absent from
`Examples/Targets.lean`, from `scripts/ci`'s Targets allowlist, from
`Audit.lean`'s designated-name list and from the Comparator
Challenge's trusted closure (gallery-campaign charter §HARD
BOUNDARIES — designation is arc-end work under user sign-off).
-/

namespace GoLean.Iris.Audit

/-! ## The selection-sort example (Gallery Campaign G1, lane B) -/

-- Statement vocabulary
example := @GoLean.Examples.SelectionSort.selArr8
example := @GoLean.Examples.SelectionSort.selFam
example := @GoLean.Examples.SelectionSort.selectionSortFunc
example := @GoLean.Examples.SelectionSort.selsortHarnessRFunc
-- The two lowering pins (the third link of the golden chain)
example := @GoLean.Examples.SelectionSort.selectionSort_pin
example := @GoLean.Examples.SelectionSort.selsortHarnessRFunc_pin
-- Proof vocabulary the honesty clauses name
example := @GoLean.Examples.SelectionSort.minIdx
example := @GoLean.Examples.SelectionSort.swapList
example := @GoLean.Examples.SelectionSort.PrefixSorted
example := @GoLean.Examples.SelectionSort.PrefixLE
example := @GoLean.Examples.SelectionSort.swap_advance
example := @GoLean.Examples.SelectionSort.count_swapList
example := @GoLean.Examples.SelectionSort.sorted_of_prefixSorted
example := @GoLean.Examples.SelectionSort.inner_loop
example := @GoLean.Examples.SelectionSort.pass_seg
example := @GoLean.Examples.SelectionSort.rebaseSim3
example := @GoLean.Examples.SelectionSort.outer_loop
example := @GoLean.Examples.SelectionSort.sA_runs
example := @GoLean.Examples.SelectionSort.post_runs
example := @GoLean.Examples.SelectionSort.selsortH_runs
-- The shared sort vocabulary (SortShared, proven once for both sorts)
example := @GoLean.Examples.SortShared.sorted_perm_unique
example := @GoLean.Examples.SortShared.eq_sortSpec_of_sorted_count
example := @GoLean.Examples.SortShared.sorted_count_of_eq_sortSpec
example := @GoLean.Examples.SortShared.lcgFamily
-- The headlines
example := @GoLean.Examples.SelectionSort.selsort_ok
example := @GoLean.Examples.SelectionSort.selsort_readout
example := @GoLean.Examples.SelectionSort.selsort_sorted_count

/-- info: 'GoLean.Examples.SelectionSort.selsort_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.selsort_ok
/-- info: 'GoLean.Examples.SelectionSort.selsort_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.selsort_readout
/-- info: 'GoLean.Examples.SelectionSort.selsort_sorted_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.selsort_sorted_count
/-- info: 'GoLean.Examples.SelectionSort.selsortH_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.selsortH_runs
/-- info: 'GoLean.Examples.SelectionSort.outer_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.outer_loop
/-- info: 'GoLean.Examples.SelectionSort.inner_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.inner_loop
/-- info: 'GoLean.Examples.SelectionSort.pass_seg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.pass_seg
/-- info: 'GoLean.Examples.SelectionSort.rebaseSim3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.rebaseSim3
/-- info: 'GoLean.Examples.SelectionSort.post_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.post_runs
/-- info: 'GoLean.Examples.SelectionSort.sA_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.sA_runs
/-- info: 'GoLean.Examples.SelectionSort.swap_advance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.swap_advance
/-- info: 'GoLean.Examples.SelectionSort.count_swapList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.count_swapList
/-- info: 'GoLean.Examples.SelectionSort.sorted_of_prefixSorted' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.sorted_of_prefixSorted
/-- info: 'GoLean.Examples.SelectionSort.minIdx_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.minIdx_min
/-- info: 'GoLean.Examples.SelectionSort.selectionSort_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.selectionSort_pin
/-- info: 'GoLean.Examples.SelectionSort.selsortHarnessRFunc_pin' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Examples.SelectionSort.selsortHarnessRFunc_pin

end GoLean.Iris.Audit
