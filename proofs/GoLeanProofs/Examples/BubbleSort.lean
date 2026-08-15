import GoLeanProofs.Examples.BubbleSort.Run

/-!
# BubbleSort — the `bubble` example (Gallery Campaign G1, proof lane B)

Go source: `Corpus/coverage/exec/examples/bubble/main.go`
(differentially green against `go run`, 14 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/bubble-lowered.repr`
and carried in `GoLeanProofs.Examples.BubbleSortProgram`.

The subject `bubbleSort` is the classic early-exit bubble sort: the
outer `for end := len(s); end > 1; end--` shrinks the unsorted prefix,
the inner `for i := 1; i < end; i++` bubbles a maximum to `end-1` by
adjacent swaps, and a swap-free pass RETURNS EARLY through the unary
`!` test `if !swapped { return }`. The harness is the S3 RELATIONAL
style: `bubble_harness_r(n, seed)` builds a genuinely-unsorted input by
iterating a wrapping LCG from `seed`, copies it into `pre`, sorts IN
PLACE, copies the result into `post`, and returns BOTH fixed-cap
`[8]uint64` arrays — so the postcondition is a relation over the
RETURNED DATA: `post = sortSpec pre`, the unique sorted permutation.

**What the shape costs the proof.** Two things make this the lane's
hardest subject:

* **Per-pass re-allocation.** Each outer pass allocates a fresh
  `swapped`/`i`/`$forFirst` triple, so `rfl` segments cannot describe
  the outer loop at one placement. Each pass is proven ONCE at the
  tight canonical placement and transferred to the true garbage-laden
  placement by the executable frame theorem, with the retired triple
  REBASED into the frame between passes (`BubbleSort.Frame`, the
  InsertionSort `ρ11`/`rebaseSim11` pattern at threshold 16, retire 3).
* **The early return.** The subject leaves from two places — the
  counter exit `end ≤ 1` and the `return` inside the body — so the
  outer induction runs both exits to the SAME post-call anchor, and
  the pure invariant (`BubbleInv`: suffix sorted, prefix bounded by
  suffix, counts preserved) discharges sortedness at EACH exit — the
  early one via "a swap-free pass certifies a sorted prefix"
  (`bubbleInv_earlyExit`).

The per-phase shards:

* `BubbleSort.Pure` — one pass as a compare-and-swap fold (`passL`/
  `passB`), the pass invariants, and `BubbleInv` with its three exits.
* `BubbleSort.Machine` — the two pinned `Func`s, the address layout,
  the statement pieces, environments, continuations, heap fronts, and
  the derived entry equation.
* `BubbleSort.Harness` — entry, the LCG setup loop, the `pre` copy.
* `BubbleSort.Subject` — the nested loops at the tight placement: the
  inner induction and both pass exits.
* `BubbleSort.Frame` — the threshold-16/retire-3 frame-rebase layer.
* `BubbleSort.Outer` — the outer induction over the true placement.
* `BubbleSort.Run` — the epilogue (the `post` copy, the result
  stores) and the end-to-end run `bH_runs`.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.BubbleSort` reaches it by name (the
C-H4/C-H5 shape, adopted from birth).
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- `sortSpec`, re-exported into the example's namespace for the
statement: the gallery's ONE definition of "the sorted permutation"
(an insertion fold, `Examples.InsertionSort.Pure`). -/
abbrev sortSpec : List Int → List Int :=
  GoLean.Examples.InsertionSort.sortSpec

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8` and every `seed < 2^64`, running the Go harness
`bubble_harness_r(n, seed)` through the machine's native function
entry — empty-heap state, both arguments at the call boundary —
completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns TWO values: a length-`n`
list `pre` as the fixed-cap array the Go returns, and
**`sortSpec pre` — THE sorted permutation of `pre`** — as the second.
The postcondition is a relation over the RETURNED DATA; no family
function and no index arithmetic appears in it.

Honesty clauses, all recorded rather than hidden:

* **The claim is the FUNCTIONAL form of the sort postcondition.**
  `sortSpec` (an insertion fold) is the unique sorted permutation:
  `sorted_perm_unique` (`SortShared`) makes "`post` is sorted and has
  `pre`'s element counts" and "`post = sortSpec pre`" the SAME claim;
  `bubble_sorted_perm` below ships the first-order reading.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[bubbleCapN]uint64` with `bubbleCapN = 8` (visible in the corpus
  Go) and the two copy loops plus zero-padding exist ONLY so the data
  can cross the observation boundary.
* **`∃ pre` is still family-determined.** The witness is the wrapping
  LCG family `x ← x·2862933555777941757 + 3037000493 (mod 2^64)`
  seeded at `seed` — genuinely unsorted at the corpus rows, which
  exercise passes WITH swaps, the swap-free early exit, and the
  counter exit. The statement merely avoids SAYING so; making the
  input genuine ∀-data needs the ghost rung-1 annotation, which is
  designed and not built.
* **`n = 0` and `n = 1` are included**: `end = len(s) ≤ 1`, the outer
  test fails at once, and the empty/singleton list IS sorted (the
  corpus rows `harness-r-empty`/`harness-r-one` pin both against
  `go run`).
* **Domain bounds attributed**: `seed < 2^64` is Go's own uint64
  domain (the argument arrives pre-wrapped); the in-list bounds are
  the program's own arithmetic (every element is an LCG iterate mod
  2^64); `n ≤ 8` is the harness's visible cap; sortedness/permutation
  are mathematics over `List Int`.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = (105·n + 116)·n + 174·n + 318` — QUADRATIC, and a
branch-uniform WORST CASE: `105` per inner comparison (charged at the
swap arm), at most `n−1` passes of at most `n−1` comparisons, `68` per
setup iteration, `53` per copy iteration (twice), plus the fixed
entry/prologue/epilogue segments. The MEASURED counts, recorded
separately and NOT presented as the bound (seed 7): `318` at `n = 0`,
`492` at `n = 1`, `809/1040/1549` at `n = 2/3/4`, `4443` at `n = 8`.
The measurement depends on the data — how many swaps fire and where
the early exit lands — so it is not a law; the bound is. -/
theorem bubble_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel bubbleLowered.typeDefs.toList
            bubbleLowered.funcs bubbleHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            bubbleLowered.methods ch
          = .ok { values := #[bArr8V pre, bArr8V (sortSpec pre)] } := by
  have hfam_len : (bubFam n seed).length = n :=
    SortShared.lcgFamily_length bubA bubB n seed
  refine ⟨bubFam n seed, hfam_len,
    (105 * n + 116) * n + 174 * n + 318, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, σf, hk, hrun, hl2, hl3⟩ := bH_runs n seed hcap hseed ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  have hst : bHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = σB (bHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4 := rfl
  rw [bH_entry_eq,
    unorm_of_range (v := (n : Int)) (by omega)
      (by exact_mod_cast (by omega : n < 2 ^ 64)),
    unorm_of_range (v := (seed : Int)) (by omega)
      (by exact_mod_cast hseed),
    hst, hfold, runConfig_next_stop]
  have hload : loadMany σf [.base ⟨2⟩, .base ⟨3⟩]
      = .ok [.array ⟨(bubPre n seed).map (fun v => .int v .uint64)⟩,
             .array ⟨(bPost (bubSorted n seed) n).map
               (fun v => .int v .uint64)⟩] := by
    simp [loadMany, loadLoc, hl2, hl3, pure, Except.pure, Bind.bind,
      Except.bind]
  have harr0 : bArr8V (bubFam n seed)
      = .array ⟨(bubPre n seed).map (fun v => .int v .uint64)⟩ := by
    rw [bArr8V, hfam_len]
  have hslen : (sortSpec (bubFam n seed)).length = n := by
    rw [show sortSpec (bubFam n seed)
        = GoLean.Examples.InsertionSort.sortSpec (bubFam n seed) from rfl,
      GoLean.Examples.InsertionSort.sortSpec_length, hfam_len]
  have harr1 : bArr8V (sortSpec (bubFam n seed))
      = .array ⟨(bPost (bubSorted n seed) n).map
          (fun v => .int v .uint64)⟩ := by
    rw [bArr8V, bPost,
      List.take_of_length_le (Nat.le_of_eq (bubSorted_length n seed)),
      hslen]
  rw [harr0, harr1]
  simp [hload, Bind.bind, Except.bind, pure, Except.pure]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those two values. -/
theorem bubble_readout (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel bubbleLowered.typeDefs.toList
            bubbleLowered.funcs bubbleHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            bubbleLowered.methods ch
          = .ok r →
        r = { values := #[bArr8V pre, bArr8V (sortSpec pre)] } := by
  obtain ⟨pre, hlen, htot⟩ := bubble_ok n seed hcap hseed
  exact ⟨pre, hlen, harness_readout_of_total htot⟩

/-- **The first-order readout** (statement-TCB doctrine: a corollary a
reader can check against the Go without unfolding `sortSpec`): the
second returned array is SORTED and has exactly the first's element
counts — the two-conjunct spelling of "the sorted permutation",
derived through `SortShared.sorted_count_of_eq_sortSpec`. -/
theorem bubble_sorted_perm (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ post : List Int,
          runFunctionWithContextM fuel bubbleLowered.typeDefs.toList
              bubbleLowered.funcs bubbleHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              bubbleLowered.methods ch
            = .ok { values := #[bArr8V pre, bArr8V post] }
          ∧ Sorted post ∧ (∀ v : Int, post.count v = pre.count v) := by
  obtain ⟨pre, hlen, N, htot⟩ := bubble_ok n seed hcap hseed
  refine ⟨pre, hlen, N, fun fuel hfuel ch => ⟨sortSpec pre,
    htot fuel hfuel ch, ?_, ?_⟩⟩
  · exact (SortShared.sorted_count_of_eq_sortSpec rfl).1
  · exact (SortShared.sorted_count_of_eq_sortSpec rfl).2

end GoLean.Examples.BubbleSort
