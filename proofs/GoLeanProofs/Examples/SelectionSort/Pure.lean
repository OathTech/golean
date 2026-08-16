import GoLeanProofs.SliceMem
import GoLeanProofs.Examples.SortShared

/-!
# SelectionSort — Pure

The example's mathematical content: the first-minimum index function
`minIdx` (what the inner loop computes), the two-set `swapList` (what
the unconditional swap does), and the selection-sort invariant — after
`i` outer passes the first `i` entries are sorted and dominate the
rest, with every value's multiplicity preserved.

The statement layer above (the root) uses only `SliceMem.Sorted`,
`List.count` and `SortShared.eq_sortSpec_of_sorted_count`; everything
here is proof method for the machine inductions in
`SelectionSort/Subject.lean` and `SelectionSort/Frame.lean`.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## `getD`/`set` pointwise algebra + the swap — LIFTED (WP arc s1
lift 3): `getD_set_self`/`getD_set_ne`/`count_set_add`, `swapList` and
its five facts moved VERBATIM to `SliceMem` (exactly as this file's
GAP-WITNESS note asked). The two names below survive as zero-proof
delegations because the audit shard roll-calls/pins them; everything
else resolves through the module's `open GoLean.SliceMem`. -/

/-- Delegation to `SliceMem.swapList` (shard roll-call name). -/
abbrev swapList (l : List Int) (i m : Nat) : List Int :=
  SliceMem.swapList l i m

/-- Delegation to `SliceMem.count_swapList` (shard-pinned name). -/
theorem count_swapList (v : Int) {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length) :
    (swapList l i m).count v = l.count v :=
  SliceMem.count_swapList v hi hm

/-! ## The first-minimum index -/

/-- `minIdx l i k` — the index of the FIRST minimum among positions
`i, i+1, …, i+k` (Go's strict `<` keeps the earliest minimum). This is
exactly the inner loop's `m`: at inner counter `j`, `m = minIdx l i
(j-i-1)`. -/
def minIdx (l : List Int) (i : Nat) : Nat → Nat
  | 0 => i
  | k + 1 =>
      if l.getD (i + k + 1) 0 < l.getD (minIdx l i k) 0
      then i + k + 1 else minIdx l i k

theorem le_minIdx (l : List Int) (i : Nat) : ∀ k, i ≤ minIdx l i k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl i
  | succ k ih =>
      rw [minIdx]
      split
      · omega
      · exact ih

theorem minIdx_le (l : List Int) (i : Nat) : ∀ k, minIdx l i k ≤ i + k := by
  intro k
  induction k with
  | zero => simp [minIdx]
  | succ k ih =>
      rw [minIdx]
      split
      · omega
      · omega

/-- The min property: `l[minIdx l i k]` is ≤ every inspected entry. -/
theorem minIdx_min (l : List Int) (i : Nat) :
    ∀ k t, i ≤ t → t ≤ i + k → l.getD (minIdx l i k) 0 ≤ l.getD t 0 := by
  intro k
  induction k with
  | zero =>
      intro t h1 h2
      have : t = i := by omega
      subst this
      exact Int.le_refl _
  | succ k ih =>
      intro t h1 h2
      rw [minIdx]
      split
      · rename_i hlt
        rcases Nat.lt_or_ge t (i + k + 1) with h | h
        · exact Int.le_trans (Int.le_of_lt hlt) (ih t h1 (by omega))
        · have : t = i + k + 1 := by omega
          subst this
          exact Int.le_refl _
      · rename_i hge
        rcases Nat.lt_or_ge t (i + k + 1) with h | h
        · exact ih t h1 (by omega)
        · have : t = i + k + 1 := by omega
          subst this
          exact Int.not_lt.mp hge

/-- The recursion step in the loop's spelling: at inner counter `j`
(`i < j`), the new `m` after comparing `s[j] < s[m]`. -/
theorem minIdx_step (l : List Int) {i j : Nat} (hij : i < j) :
    minIdx l i (j - i)
      = if l.getD j 0 < l.getD (minIdx l i (j - i - 1)) 0
        then j else minIdx l i (j - i - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
  have h1 : i + k + 1 - i = k + 1 := by omega
  have h2 : i + k + 1 - i - 1 = k := by omega
  rw [h2, h1, minIdx]

/-! ## The outer invariant -/

/-- The first `i` entries are pairwise sorted. At `i = l.length` this
IS `SliceMem.Sorted`. -/
def PrefixSorted (l : List Int) (i : Nat) : Prop :=
  ∀ a b : Nat, a < b → b < i → l.getD a 0 ≤ l.getD b 0

/-- Every prefix entry is ≤ every suffix entry (the "the prefix holds
the `i` smallest" half). -/
def PrefixLE (l : List Int) (i : Nat) : Prop :=
  ∀ a b : Nat, a < i → i ≤ b → b < l.length → l.getD a 0 ≤ l.getD b 0

theorem prefixSorted_zero (l : List Int) : PrefixSorted l 0 := by
  intro a b _ hb; omega

theorem prefixLE_zero (l : List Int) : PrefixLE l 0 := by
  intro a b ha _ _; omega

theorem sorted_of_prefixSorted {l : List Int}
    (h : PrefixSorted l l.length) : Sorted l :=
  fun a b hab hb => h a b hab hb

/-- **One pass advances the invariant, `m` abstract**: any position of
a suffix minimum works — the machine induction instantiates `m` with
the inner loop's exit value. -/
theorem swap_advance_gen {l : List Int} {n i m : Nat}
    (hlen : l.length = n) (hi : i < n) (him : i ≤ m) (hmn : m < n)
    (hmin : ∀ t, i ≤ t → t < n → l.getD m 0 ≤ l.getD t 0)
    (hps : PrefixSorted l i) (hple : PrefixLE l i) :
    PrefixSorted (swapList l i m) (i + 1)
      ∧ PrefixLE (swapList l i m) (i + 1) := by
  have hlen' : (swapList l i m).length = n := by
    rw [swapList_length, hlen]
  constructor
  · -- PrefixSorted at i + 1
    intro a b hab hb
    rcases Nat.lt_or_ge b i with hbi | hbi
    · -- both strictly inside the old prefix: untouched
      rw [getD_swapList_other (by omega) (by omega),
        getD_swapList_other (by omega) (by omega)]
      exact hps a b hab hbi
    · -- b = i: the new entry is the suffix minimum, ≥ the old prefix
      have hbe : b = i := by omega
      subst hbe
      rw [getD_swapList_fst (by omega) (by omega),
        getD_swapList_other (by omega) (by omega)]
      exact hple a m (by omega) him (by omega)
  · -- PrefixLE at i + 1
    intro a b ha hb hbl
    rw [hlen'] at hbl
    rcases Nat.lt_or_ge a i with hai | hai
    · -- a in the old prefix
      have hga : (swapList l i m).getD a 0 = l.getD a 0 :=
        getD_swapList_other (by omega) (by omega)
      rw [hga]
      by_cases hbm : b = m
      · subst hbm
        rw [getD_swapList_snd (by omega)]
        exact hple a i hai (Nat.le_refl i) (by omega)
      · rw [getD_swapList_other (by omega) hbm]
        exact hple a b hai (by omega) (by omega)
    · -- a = i: the fresh minimum dominates the new suffix
      have hae : a = i := by omega
      rw [hae, getD_swapList_fst (by omega) (by omega)]
      by_cases hbm : b = m
      · subst hbm
        rw [getD_swapList_snd (by omega)]
        exact hmin i (Nat.le_refl i) hi
      · rw [getD_swapList_other (by omega) hbm]
        exact hmin b (by omega) (by omega)

/-- The instantiation at the inner loop's actual exit value
`m = minIdx l i (n - 1 - i)`. -/
theorem swap_advance {l : List Int} {n i : Nat}
    (hlen : l.length = n) (hi : i < n)
    (hps : PrefixSorted l i) (hple : PrefixLE l i) :
    PrefixSorted (swapList l i (minIdx l i (n - 1 - i))) (i + 1)
      ∧ PrefixLE (swapList l i (minIdx l i (n - 1 - i))) (i + 1) := by
  refine swap_advance_gen hlen hi (le_minIdx l i _) ?_ ?_ hps hple
  · have := minIdx_le l i (n - 1 - i)
    omega
  · intro t h1 h2
    exact minIdx_min l i (n - 1 - i) t h1 (by omega)

end GoLean.Examples.SelectionSort
