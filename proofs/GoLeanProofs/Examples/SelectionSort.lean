import GoLeanProofs.Examples.SelectionSort.Run

/-!
# SelectionSort — the `selsort` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/selsort/main.go`
(differentially green against `go run`, 14 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/selsort-lowered.repr`
and carried in `GoLeanProofs.Examples.SelectionSortProgram`.

The subject `selectionSort` is the classic nested loop: pass `i` scans
`j = i+1 … len(s)-1` for the first minimum of the suffix and swaps it
into place UNCONDITIONALLY (`s[i], s[m] = s[m], s[i]` fires even when
`m == i`). The harness is the S3 RELATIONAL style: setup iterates a
wrapping LCG from `seed`, a copy loop lifts the input into `pre`, the
subject sorts IN PLACE, a second copy loop lifts the result into
`post`, and BOTH fixed-cap `[8]uint64` arrays are returned — so the
postcondition relates the RETURNED DATA directly:
`post = sortSpec pre`, the unique sorted permutation.

**What the nested reallocation costs the proof, and why it is worth
saying.** The machine allocates a FRESH `m`/`j`/`$forFirst` triple on
every outer pass (the pass-local declarations re-enter their blocks;
`nextAddr` grows by 3 per pass and the dead cells stay in the heap —
probe-verified). Fixed-address segments therefore cannot describe the
outer loop head at a single placement; each pass is proven ONCE at a
tight canonical placement (`m`/`j`/flag at 16/17/18) and transferred
to the true garbage-laden placement by the executable frame theorem,
with the retired triple REBASED into the frame between passes
(`rebaseSim3` — the InsertionSort `rebaseSim11` pattern at threshold
16, retire 3). The post-subject phase is proven as one canonical run
and transferred in a single `transfer_seg16` application.

The per-phase shards:

* `SelectionSort/Pure.lean` — `minIdx`, `swapList`, and the selection
  invariant (`PrefixSorted`/`PrefixLE`/count preservation).
* `SelectionSort/Machine.lean` — the two pinned `Func`s, the address
  layout, environments, continuations, heap fronts, the entry
  equation.
* `SelectionSort/HarnessR.lean` — phase A (entry, LCG setup, pre-copy,
  the call boundary), exact in `121·n + 195` steps.
* `SelectionSort/Subject.lean` — the canonical pass: the inner scan
  (`m = minIdx` invariant) and the swap.
* `SelectionSort/Frame.lean` — the ρ16 rebase layer and the outer
  induction over the true run.
* `SelectionSort/Post.lean` — the post-copy loop and the epilogue,
  exact in `53·n + 88` steps.
* `SelectionSort/Run.lean` — the end-to-end composition.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.SelectionSort` reaches it by name (the
C-H4/C-H5 shape, adopted from birth).
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Examples.SortShared
open GoLean.Examples.InsertionSort (sortSpec)

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8` and every `seed < 2^64`, running the Go harness
`selsort_harness_r(n, seed)` through the machine's native function
entry — empty-heap state, both arguments at the call boundary —
completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns TWO values: a length-`n`
list `pre` and the list `post = sortSpec pre` — THE sorted permutation
of `pre` — both as the fixed-cap `[8]uint64` arrays the Go returns.
The postcondition is a relation over the RETURNED DATA: the sorted
output is returned and equated to the mathematical sort of the
returned input; no family function appears in it.

Honesty clauses, all recorded rather than hidden:

* **`sortSpec` is the whole mathematical content**: the insertion fold
  from `Examples.InsertionSort.Pure` — the gallery's ONE definition of
  "the sorted permutation" (`SortShared`'s deliberate cross-example
  import). `selsort_sorted_count` below restates the claim
  first-order — `Sorted post ∧ ∀ v, count v post = count v pre` —
  with no `sortSpec` at all; the two forms are interderivable by
  `SortShared.sorted_perm_unique`.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[selsortCapN]uint64` with `selsortCapN = 8` (visible in the corpus
  Go); the copy loops and zero-padding exist ONLY so the data can
  cross the observation boundary.
* **`∃ pre` is still family-determined.** The witness is the wrapping
  LCG family `x = x·6364136223846793005 + 1442695040888963407 (mod
  2^64)` iterated from `seed` — genuinely unsorted inputs
  (probe-verified in the guardrails wave) — and the statement merely
  avoids SAYING so. Genuine ∀-data input needs the ghost rung-1
  annotation, which is designed and not built.
* **`n = 0` and `n = 1` are included**: the loops degenerate and the
  empty/singleton list is its own sort (`harness-r-empty`/
  `harness-r-one` pin this against `go run`).
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = (67·n + 145)·n + 174·n + 318` — QUADRATIC, as
selection sort is: the branch-uniform worst case charges every inner
iteration at its `m`-update ceiling (67 steps) and every pass at a
full-suffix scan. The MEASURED counts, recorded separately and NOT
presented as the bound: at seed 7, `318` at `n = 0` (exact — it is
the constant term), then `637 / 1011 / 1452 / 1960 / 2535 / 3165 /
3838 / 4566` at `n = 1…8`; at `n = 8` across seeds
`0 / 1 / 123456789 / 2^64−1` the counts are `4506 / 4530 / 4554 /
4542` (the bound there is `7158`). The measurement depends on the
data — how often the running minimum updates; the bound does not. -/
theorem selsort_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre post : List Int, pre.length = n ∧ post = sortSpec pre ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel selsortLowered.typeDefs.toList
            selsortLowered.funcs selsortHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            selsortLowered.methods ch
          = .ok { values := #[selArr8 pre, selArr8 post] } := by
  refine ⟨selFam n seed, sortSpec (selFam n seed),
    lcgFamily_length lcgA lcgB n seed, rfl,
    (67 * n + 145) * n + 174 * n + 318, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, σf, lf, hk, hrun, hlfl, hsort, hcnt, hlook2, hlook3⟩ :=
    selsortH_runs n seed hcap hseed ch
  have hlf : lf = sortSpec (selFam n seed) :=
    eq_sortSpec_of_sorted_count hsort hcnt
  rw [hlf] at hlook3
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [selsH_entry_eq,
    unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    σSeed_eq, hfold, runConfig_next_stop]
  have hload : loadMany σf [.base ⟨2⟩, .base ⟨3⟩]
      = .ok [.array ⟨(selPad8 (selFam n seed)).map
              (fun v => .int v .uint64)⟩,
             .array ⟨(selPad8 (sortSpec (selFam n seed))).map
              (fun v => .int v .uint64)⟩] := by
    simp [loadMany, loadLoc, hlook2, hlook3, pure, Except.pure,
      Bind.bind, Except.bind]
  simp [hload, selArr8, Bind.bind, Except.bind, pure, Except.pure]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those two values. -/
theorem selsort_readout (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre post : List Int, pre.length = n ∧ post = sortSpec pre ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel selsortLowered.typeDefs.toList
            selsortLowered.funcs selsortHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            selsortLowered.methods ch
          = .ok r →
        r = { values := #[selArr8 pre, selArr8 post] } := by
  obtain ⟨pre, post, hlen, hpost, N, htot⟩ := selsort_ok n seed hcap hseed
  exact ⟨pre, post, hlen, hpost, harness_readout_of_total ⟨N, htot⟩⟩

/-- **The first-order readout** (statement-TCB doctrine: a headline
ships a corollary a reader can check against the Go without unfolding
`sortSpec`): the second returned array is SORTED and holds exactly the
first returned array's elements, multiplicity and all. -/
theorem selsort_sorted_count (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre post : List Int, pre.length = n ∧
      Sorted post ∧ (∀ v : Int, post.count v = pre.count v) ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel selsortLowered.typeDefs.toList
            selsortLowered.funcs selsortHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            selsortLowered.methods ch
          = .ok { values := #[selArr8 pre, selArr8 post] } := by
  obtain ⟨pre, post, hlen, hpost, N, htot⟩ := selsort_ok n seed hcap hseed
  obtain ⟨hsorted, hcount⟩ := sorted_count_of_eq_sortSpec hpost
  exact ⟨pre, post, hlen, hsorted, hcount, N, htot⟩

end GoLean.Examples.SelectionSort
