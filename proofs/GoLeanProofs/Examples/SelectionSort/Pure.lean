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

/-! ## `getD`/`set` pointwise algebra (list surgery for the swap) -/

theorem getD_set_self {l : List Int} {k : Nat} {w : Int}
    (hk : k < l.length) : (l.set k w).getD k 0 = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl,
    if_pos hk]
  rfl

theorem getD_set_ne {l : List Int} {k j : Nat} {w : Int}
    (h : k ≠ j) : (l.set k w).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_neg h,
    List.getD_eq_getElem?_getD]

/-- The additive counting law of one `set` (no `Nat` subtraction). -/
theorem count_set_add (v w : Int) :
    ∀ (l : List Int) (k : Nat), k < l.length →
    (l.set k w).count v + (if l.getD k 0 = v then 1 else 0)
      = l.count v + (if w = v then 1 else 0) := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons x rest ih =>
      intro k hk
      cases k with
      | zero =>
          simp only [List.set_cons_zero, List.count_cons, List.getD_cons_zero,
            beq_iff_eq]
          omega
      | succ kk =>
          have hkk : kk < rest.length := by simpa using hk
          have ih' := ih kk hkk
          simp only [List.set_cons_succ, List.count_cons,
            List.getD_cons_succ, beq_iff_eq]
          omega

/-! ## The swap -/

/-- The machine's two stores, in the machine's order: `s[i] := old
s[m]`, then `s[m] := old s[i]` (both right-hand sides were read before
either store). At `m = i` this is a no-op on the list. -/
def swapList (l : List Int) (i m : Nat) : List Int :=
  (l.set i (l.getD m 0)).set m (l.getD i 0)

theorem swapList_length (l : List Int) (i m : Nat) :
    (swapList l i m).length = l.length := by
  simp [swapList]

theorem getD_swapList_fst {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length) :
    (swapList l i m).getD i 0 = l.getD m 0 := by
  by_cases him : m = i
  · subst him
    rw [swapList, getD_set_self (by simpa using hi)]
  · rw [swapList, getD_set_ne him, getD_set_self hi]

theorem getD_swapList_snd {l : List Int} {i m : Nat}
    (hm : m < l.length) :
    (swapList l i m).getD m 0 = l.getD i 0 :=
  getD_set_self (by simpa using hm)

theorem getD_swapList_other {l : List Int} {i m k : Nat}
    (hki : k ≠ i) (hkm : k ≠ m) :
    (swapList l i m).getD k 0 = l.getD k 0 := by
  rw [swapList, getD_set_ne (fun h => hkm h.symm),
    getD_set_ne (fun h => hki h.symm)]

/-- **Swapping preserves every count** — the permutation half of the
invariant, first-order. -/
theorem count_swapList (v : Int) {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length) :
    (swapList l i m).count v = l.count v := by
  have h1 := count_set_add v (l.getD i 0) (l.set i (l.getD m 0)) m
    (by simpa using hm)
  have h2 := count_set_add v (l.getD m 0) l i hi
  have hgm : (l.set i (l.getD m 0)).getD m 0 = l.getD m 0 := by
    by_cases him : i = m
    · subst him; exact getD_set_self hi
    · exact getD_set_ne him
  rw [hgm] at h1
  rw [show ((l.set i (l.getD m 0)).set m (l.getD i 0)) = swapList l i m
    from rfl] at h1
  by_cases ha : l.getD m 0 = v <;> by_cases hb : l.getD i 0 = v <;>
    simp [ha, hb] at h1 h2 ⊢ <;> omega

/-- The range invariant survives a swap (values only move). -/
theorem range_swapList {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length)
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ x ∈ swapList l i m, 0 ≤ x ∧ x < 2 ^ 64 := by
  intro x hx
  rw [swapList] at hx
  rcases mem_set_of_mem hx with rfl | hx
  · exact hr _ (getD_mem hi)
  · rcases mem_set_of_mem hx with rfl | hx
    · exact hr _ (getD_mem hm)
    · exact hr x hx

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
