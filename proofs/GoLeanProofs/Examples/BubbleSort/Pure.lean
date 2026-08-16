import GoLeanProofs.Examples.SortShared

/-!
# BubbleSort — Pure

The example's mathematical content: one bubble PASS as a fold of
compare-and-swap steps, the pass invariants (multiset preservation,
the running max, the untouched tail), the `swapped` flag's meaning
(a swap-free pass certifies a sorted prefix), and the OUTER invariant
`BubbleInv` that carries the sorted suffix and the prefix/suffix
boundary across passes.

Statement vocabulary is NOT here: the headline speaks `sortSpec` /
`Sorted` / `List.count` (via `SortShared`); everything in this module
is proof method — the shape of the Go loop, mirrored on `List Int`.

The machine loop at inner counter `i = m+1` has list `passL l m` and
flag `passB l m`: `passL l m` is the input after the compare-and-swap
steps at indices `1..m`, `passB l m` records whether any fired.
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.SliceMem

set_option maxRecDepth 1000000

/-! ## One pass, as a fold of compare-and-swap steps -/

/-- One compare-and-swap step at index `i` (Go:
`if s[i-1] > s[i] { s[i-1], s[i] = s[i], s[i-1] }`). At `i = 0` the
comparison is `v < v` and the step is the identity. -/
def bstepL (l : List Int) (i : Nat) : List Int :=
  if l.getD i 0 < l.getD (i - 1) 0
  then (l.set (i - 1) (l.getD i 0)).set i (l.getD (i - 1) 0)
  else l

/-- Whether the step at index `i` fires. -/
def bstepB (l : List Int) (i : Nat) : Bool :=
  decide (l.getD i 0 < l.getD (i - 1) 0)

/-- The list after the compare-and-swap steps at indices `1..m`. -/
def passL (l : List Int) : Nat → List Int
  | 0 => l
  | m + 1 => bstepL (passL l m) (m + 1)

/-- Whether ANY step at indices `1..m` fired — the Go `swapped` flag. -/
def passB (l : List Int) : Nat → Bool
  | 0 => false
  | m + 1 => passB l m || bstepB (passL l m) (m + 1)

/-! ## getD/set helpers -/

theorem getD_of_lt {l : List Int} {k : Nat} (h : k < l.length) :
    l.getD k 0 = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

-- `getD_set_self`/`getD_set_ne` — LIFTED (WP arc s1 lift 3): the
-- local copies are deleted; uses resolve to `SliceMem`'s. The
-- adjacent-pair decomposition lemmas (`adj_decomp`/`adj_swap_decomp`)
-- are deleted with them: `bstepL`'s swap arm IS
-- `SliceMem.swapList l (i-1) i`, so the count fact is one delegation.

/-- One step preserves every element count. -/
theorem bstepL_count {l : List Int} {i : Nat} (h2 : i < l.length)
    (v : Int) : (bstepL l i).count v = l.count v := by
  rw [bstepL]
  split
  · rename_i hlt
    rcases Nat.eq_zero_or_pos i with rfl | h1
    · rw [show (0 : Nat) - 1 = 0 from rfl] at hlt
      exact absurd hlt (Int.lt_irrefl _)
    · exact count_swapList v (by omega) h2
  · rfl

/-- One step preserves length. -/
theorem bstepL_length (l : List Int) (i : Nat) :
    (bstepL l i).length = l.length := by
  rw [bstepL]
  split <;> simp

theorem passL_length (l : List Int) (m : Nat) :
    (passL l m).length = l.length := by
  induction m with
  | zero => rfl
  | succ m ih => rw [passL, bstepL_length, ih]

/-- The pass preserves every element count (each step is an adjacent
swap or the identity). -/
theorem passL_count {l : List Int} {m : Nat} (hm : m < l.length)
    (v : Int) : (passL l m).count v = l.count v := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [passL, bstepL_count (by rw [passL_length]; omega) v,
        ih (by omega)]

/-- Membership transport (for the uint64-range hypotheses). -/
theorem passL_mem {l : List Int} {m : Nat} (hm : m < l.length)
    {x : Int} (hx : x ∈ passL l m) : x ∈ l := by
  have h1 : 0 < (passL l m).count x := List.count_pos_iff.mpr hx
  rw [passL_count hm] at h1
  exact List.count_pos_iff.mp h1

/-- Positions past the pass counter are untouched. -/
theorem passL_getD_gt {l : List Int} {m k : Nat} (h : m < k) :
    (passL l m).getD k 0 = l.getD k 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [passL, bstepL]
      split
      · rw [getD_set_ne (by omega), getD_set_ne (by omega), ih (by omega)]
      · exact ih (by omega)

/-- **The running max**: after the steps at `1..m`, position `m` holds
a maximum of the prefix `0..m`. -/
theorem passL_max {l : List Int} {m : Nat} (hm : m < l.length) :
    ∀ t, t ≤ m → (passL l m).getD t 0 ≤ (passL l m).getD m 0 := by
  induction m with
  | zero =>
      intro t ht
      have : t = 0 := by omega
      subst this
      exact Int.le_refl _
  | succ m ih =>
      intro t ht
      have hlen : (passL l m).length = l.length := passL_length l m
      simp only [passL, bstepL, Nat.succ_sub_one]
      split
      · rename_i hlt
        -- the swap fires: the old max moves up to m+1
        have htop : (((passL l m).set m ((passL l m).getD (m + 1) 0)).set
              (m + 1) ((passL l m).getD m 0)).getD (m + 1) 0
            = (passL l m).getD m 0 :=
          getD_set_self (by simp only [List.length_set]; omega)
        rw [htop]
        rcases Nat.lt_or_ge t m with hlt2 | hge
        · rw [getD_set_ne (by omega), getD_set_ne (by omega)]
          exact ih (by omega) t (by omega)
        · rcases Nat.eq_or_lt_of_le hge with heq | h2
          · subst heq
            rw [getD_set_ne (by omega : m + 1 ≠ m),
              getD_set_self (by rw [passL_length]; omega)]
            exact Int.le_of_lt hlt
          · have htm : t = m + 1 := by omega
            subst htm
            rw [htop]
            exact Int.le_refl _
      · rename_i hnlt
        have hle : (passL l m).getD m 0 ≤ (passL l m).getD (m + 1) 0 :=
          Int.not_lt.mp hnlt
        rcases Nat.eq_or_lt_of_le ht with rfl | h2
        · exact Int.le_refl _
        · exact Int.le_trans (ih (by omega) t (by omega)) hle

/-- **Provenance**: every prefix position of the passed list holds a
value from a prefix position of the input. -/
theorem passL_from {l : List Int} (m : Nat) :
    ∀ t, t ≤ m → ∃ u, u ≤ m
      ∧ (passL l m).getD t 0 = l.getD u 0 := by
  induction m with
  | zero => intro t ht; exact ⟨t, ht, rfl⟩
  | succ m ih =>
      intro t ht
      have huntouched : (passL l m).getD (m + 1) 0 = l.getD (m + 1) 0 :=
        passL_getD_gt (by omega)
      simp only [passL, bstepL, Nat.succ_sub_one]
      split
      · rcases Nat.lt_or_ge t m with hlt2 | hge2
        · rw [getD_set_ne (by omega : m + 1 ≠ t),
            getD_set_ne (by omega : m ≠ t)]
          obtain ⟨u, hu, he⟩ := ih t (by omega)
          exact ⟨u, by omega, he⟩
        · rcases Nat.eq_or_lt_of_le hge2 with heq | h3
          · -- t = m: receives the value bubbled down from m+1
            subst heq
            rw [getD_set_ne (by omega : m + 1 ≠ m)]
            by_cases hml : m < l.length
            · rw [getD_set_self (by rw [passL_length]; omega),
                huntouched]
              exact ⟨m + 1, by omega, rfl⟩
            · rw [List.set_eq_of_length_le
                  (by rw [passL_length]; omega)]
              obtain ⟨u, hu, he⟩ := ih m (by omega)
              exact ⟨u, by omega, he⟩
          · -- t = m + 1: receives the displaced old max
            have htm : t = m + 1 := by omega
            subst htm
            by_cases hml : m + 1 < l.length
            · rw [getD_set_self
                  (by simp only [List.length_set]; rw [passL_length]; omega)]
              obtain ⟨u, hu, he⟩ := ih m (by omega)
              exact ⟨u, by omega, he⟩
            · rw [List.set_eq_of_length_le
                  (by simp only [List.length_set]; rw [passL_length]; omega),
                getD_set_ne (by omega : m ≠ m + 1), huntouched]
              exact ⟨m + 1, by omega, rfl⟩
      · rcases Nat.lt_or_ge t (m + 1) with hlt2 | hge2
        · obtain ⟨u, hu, he⟩ := ih t (by omega)
          exact ⟨u, by omega, he⟩
        · have htm : t = m + 1 := by omega
          subst htm
          rw [huntouched]
          exact ⟨m + 1, by omega, rfl⟩

/-- A swap-free pass changed nothing. -/
theorem passB_false_id {l : List Int} {m : Nat}
    (h : passB l m = false) : passL l m = l := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [passB, Bool.or_eq_false_iff] at h
      obtain ⟨h1, h2⟩ := h
      rw [passL, ih h1, bstepL]
      rw [ih h1] at h2
      rw [bstepB, decide_eq_false_iff_not] at h2
      rw [if_neg h2]

/-- A swap-free pass certifies every adjacent pair it inspected. -/
theorem passB_false_adj {l : List Int} {m : Nat}
    (h : passB l m = false) :
    ∀ i, 1 ≤ i → i ≤ m → l.getD (i - 1) 0 ≤ l.getD i 0 := by
  induction m with
  | zero => intro i h1 h2; omega
  | succ m ih =>
      intro i h1 h2
      rw [passB, Bool.or_eq_false_iff] at h
      obtain ⟨hp, hs⟩ := h
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact ih hp i h1 (by omega)
      · have him : i = m + 1 := by omega
        subst him
        rw [passB_false_id hp, bstepB, decide_eq_false_iff_not] at hs
        exact Int.not_lt.mp hs

/-- Adjacent order on a prefix extends to full order on the prefix. -/
theorem adj_prefix_sorted {l : List Int} {e : Nat}
    (hadj : ∀ i, 1 ≤ i → i < e → l.getD (i - 1) 0 ≤ l.getD i 0) :
    ∀ i j, i ≤ j → j < e → l.getD i 0 ≤ l.getD j 0 := by
  intro i j hij hj
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst this
      exact Int.le_refl _
  | succ j ihj =>
      rcases Nat.eq_or_lt_of_le hij with rfl | h2
      · exact Int.le_refl _
      · have hstep : l.getD j 0 ≤ l.getD (j + 1) 0 := by
          have := hadj (j + 1) (by omega) hj
          simpa using this
        exact Int.le_trans (ihj (by omega) (by omega)) hstep

/-! ## The outer invariant -/

/-- **The bubble-sort outer invariant** at outer counter `end = e`:
the length and the element counts match the input, the region from `e`
on is sorted (`suf`), and every prefix element is bounded by every
suffix element (`bnd`). -/
structure BubbleInv (l0 l : List Int) (e : Nat) : Prop where
  len : l.length = l0.length
  count : ∀ v : Int, l.count v = l0.count v
  bnd : ∀ i j, i < e → e ≤ j → j < l.length → l.getD i 0 ≤ l.getD j 0
  suf : ∀ i j, e ≤ i → i ≤ j → j < l.length → l.getD i 0 ≤ l.getD j 0

/-- The invariant holds at entry (`e = length`, `l = l0`). -/
theorem bubbleInv_init (l0 : List Int) : BubbleInv l0 l0 l0.length where
  len := rfl
  count := fun _ => rfl
  bnd := fun i j _ hj hjl => by omega
  suf := fun i j hi hij hjl => by omega

/-- **One pass advances the invariant**: at `end = e ≥ 2` the pass
(steps `1..e-1`) bubbles a prefix maximum to `e-1`, so the invariant
holds at `e-1`. -/
theorem bubbleInv_pass {l0 l : List Int} {e : Nat}
    (hI : BubbleInv l0 l e) (h2 : 2 ≤ e) (he : e ≤ l.length) :
    BubbleInv l0 (passL l (e - 1)) (e - 1) := by
  have hlt : e - 1 < l.length := by omega
  have hlen : (passL l (e - 1)).length = l.length := passL_length l (e - 1)
  refine ⟨by rw [hlen, hI.len], fun v => by rw [passL_count hlt, hI.count],
    ?_, ?_⟩
  · intro i j hi hj hjl
    rcases Nat.lt_or_ge j e with hje | hje
    · -- j = e-1: the fresh maximum
      have hj1 : j = e - 1 := by omega
      subst hj1
      exact passL_max hlt i (by omega)
    · -- j ≥ e: untouched suffix; the prefix value has provenance
      rw [passL_getD_gt (show e - 1 < j by omega)]
      obtain ⟨u, hu, he'⟩ := passL_from (e - 1) i (by omega)
      rw [he']
      exact hI.bnd u j (by omega) hje (by rwa [hlen] at hjl)
  · intro i j hi hij hjl
    rcases Nat.lt_or_ge i e with hie | hie
    · -- i = e-1
      have hieq : i = e - 1 := by omega
      subst hieq
      rcases Nat.eq_or_lt_of_le hij with rfl | hj2
      · exact Int.le_refl _
      · have hje : e ≤ j := by omega
        rw [passL_getD_gt (show e - 1 < j by omega)]
        obtain ⟨u, hu, he'⟩ := passL_from (e - 1) (e - 1) (by omega)
        rw [he']
        exact hI.bnd u j (by omega) hje (by rwa [hlen] at hjl)
    · rw [passL_getD_gt (show e - 1 < i by omega),
        passL_getD_gt (show e - 1 < j by omega)]
      exact hI.suf i j hie hij (by rwa [hlen] at hjl)

/-- **The early exit is honest**: a swap-free pass at `end = e` means
the whole list is sorted. -/
theorem bubbleInv_earlyExit {l0 l : List Int} {e : Nat}
    (hI : BubbleInv l0 l e) (h2 : 2 ≤ e) (he : e ≤ l.length)
    (hsw : passB l (e - 1) = false) : Sorted l := by
  have hadj := passB_false_adj hsw
  have hpre : ∀ i j, i ≤ j → j < e → l.getD i 0 ≤ l.getD j 0 :=
    adj_prefix_sorted (fun i hi hie => hadj i hi (by omega))
  intro i j hij hjl
  rcases Nat.lt_or_ge j e with hje | hje
  · exact hpre i j (by omega) hje
  · rcases Nat.lt_or_ge i e with hie | hie
    · exact hI.bnd i j hie hje hjl
    · exact hI.suf i j hie (by omega) hjl

/-- **The counter exit is honest**: at `end ≤ 1` the invariant alone
gives sortedness. -/
theorem bubbleInv_finalExit {l0 l : List Int} {e : Nat}
    (hI : BubbleInv l0 l e) (h1 : e ≤ 1) : Sorted l := by
  intro i j hij hjl
  rcases Nat.lt_or_ge i e with hie | hie
  · exact hI.bnd i j hie (by omega) hjl
  · exact hI.suf i j hie (by omega) hjl

/-- The two conclusions of any exit, packaged: the current list is the
unique sorted permutation of the input. -/
theorem bubbleInv_conclude {l0 l : List Int} {e : Nat}
    (hI : BubbleInv l0 l e) (hs : Sorted l) :
    l = GoLean.Examples.InsertionSort.sortSpec l0 :=
  SortShared.eq_sortSpec_of_sorted_count hs hI.count

end GoLean.Examples.BubbleSort
