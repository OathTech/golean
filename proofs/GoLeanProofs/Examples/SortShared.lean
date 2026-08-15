import GoLeanProofs.Examples.InsertionSort.Pure

/-!
# SortShared — the vocabulary the two comparison sorts share

Gallery Campaign G1, proof lane B (2026-08-15). `bubble` and `selsort`
are the campaign's SORT PAIR: two different algorithms, the same Go
harness shape (`([8]uint64, [8]uint64)` — the pre-state and the
post-state, both returned), and therefore the same postcondition. This
module holds exactly what they share, proven once:

1. **The LCG setup family.** Both harnesses build a genuinely-unsorted
   input by iterating a wrapping linear congruential generator from
   `seed` — they differ only in the two constants. `lcgFamily a b n
   seed` is that family with the constants as parameters, with the same
   six facts `SliceMem.familyMod` carries.
2. **The sorted-permutation bridge.** A sorted list is DETERMINED by
   its multiset (`sorted_perm_unique`), so "the returned `post` is
   sorted and has the same element counts as the returned `pre`" and
   "`post = sortSpec pre`" are the same claim. Each sort proves whichever
   its own loop invariant reaches naturally, and gets the other for
   free. `sortSpec` (insertion sort, defined as a fold) is imported
   from `Examples.InsertionSort.Pure` rather than re-derived — a
   cross-example import, taken deliberately and logged, because the
   alternative is a second definition of "the sorted permutation of a
   list" in a gallery whose whole point is that one word means one
   thing.

## Why this module is not in the kit

Both halves are CONSUMER-DRIVEN candidates for a later lift, not lifts
themselves: `lcgFamily` wants to be `SliceMem.familyF` (a family
parameterized by its index function — see the lane's kit-gap list), and
`sorted_perm_unique` wants to sit beside `SliceMem.Sorted`. The
campaign charter forbids this lane from editing the kit (gaps are
RECORDED, never fixed in-lane), so both live here, marked, with their
shapes written down for the operator.

`-- KIT-GAP WITNESS` markers below flag the code a kit lift would
delete.
-/

namespace GoLean.Examples.SortShared

open GoLean GoLean.SliceMem

set_option maxRecDepth 1000000

/-! ## The wrapping LCG setup family

-- KIT-GAP WITNESS (see the lane's kit-gap list): the kit's
`SliceMem.familyMod k n seed` is hard-wired to `seed + i % k`. Neither
sort's family is additive at all, so all six facts are re-derived here.
Shape wanted: `SliceMem.familyOf (step : Nat → Nat) (n seed : Nat)`,
the general "iterate a wrapping step function" family, with
`length`/`range`/`Z_range`/`succ`/`set`/`getD` proven once;
`familyMod` and `lcgFamily` both become instances. -/

/-- `lcgStep a b k seed` — the LCG iterated `k` times from `seed`, each
step wrapped at uint64 exactly as Go's `x = x*a + b` does. -/
def lcgStep (a b : Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => (lcgStep a b k x * a + b) % 2 ^ 64

theorem lcgStep_lt {a b k x : Nat} (hk : 0 < k) : lcgStep a b k x < 2 ^ 64 := by
  cases k with
  | zero => omega
  | succ k => exact Nat.mod_lt _ (by omega)

/-- The setup family: `s[i]` is the LCG's `(i+1)`-th iterate. -/
def lcgFamily (a b n seed : Nat) : List Int :=
  (List.range n).map (fun i => ((lcgStep a b (i + 1) seed : Nat) : Int))

theorem lcgFamily_length (a b n seed : Nat) :
    (lcgFamily a b n seed).length = n := by
  simp [lcgFamily]

theorem lcgFamily_range (a b n seed : Nat) :
    ∀ v ∈ lcgFamily a b n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [lcgFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  have : lcgStep a b (i + 1) seed < 2 ^ 64 := lcgStep_lt (by omega)
  omega

/-- The family prefix with a zero tail stays in uint64 range. -/
theorem lcgFamilyZ_range {a b n seed i : Nat} :
    ∀ v ∈ lcgFamily a b i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact lcgFamily_range a b i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem lcgFamily_succ (a b i seed : Nat) :
    lcgFamily a b (i + 1) seed
      = lcgFamily a b i seed ++ [((lcgStep a b (i + 1) seed : Nat) : Int)] := by
  simp [lcgFamily, List.range_succ]

/-- One setup store advances the family prefix. -/
theorem lcgFamily_set {a b n seed i : Nat} (hi : i < n) :
    (lcgFamily a b i seed ++ List.replicate (n - i) 0).set i
        ((lcgStep a b (i + 1) seed : Nat) : Int)
      = lcgFamily a b (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (lcgFamily a b i seed).length = i := lcgFamily_length a b i seed
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, lcgFamily_succ]
  simp

/-- The family's element at an in-range index. -/
theorem lcgFamily_getD {a b n seed m : Nat} (hm : m < n) :
    (lcgFamily a b n seed).getD m 0
      = ((lcgStep a b (m + 1) seed : Nat) : Int) := by
  rw [lcgFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-! ## The sorted-permutation bridge

-- KIT-GAP WITNESS: `sorted_perm_unique` is a fact about
`SliceMem.Sorted` and `List.count` with no example in it; it belongs
beside `Sorted` in the kit. Consumers: bubble, selsort (both landed
here), and any future sort. -/

/-- The head of a sorted list is a lower bound for the rest. -/
theorem sorted_head_le {x : Int} {xs : List Int} (h : Sorted (x :: xs))
    {v : Int} (hv : v ∈ xs) : x ≤ v := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hv
  have hlt : k + 1 < (x :: xs).length := by simpa using hk
  have hle := h 0 (k + 1) (by omega) hlt
  have h0 : (x :: xs).getD 0 0 = x := by
    rw [List.getD_eq_getElem?_getD]; simp
  have h1 : (x :: xs).getD (k + 1) 0 = v := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, ← hget]
    simp
  rw [h0, h1] at hle
  exact hle

/-- The tail of a sorted list is sorted. -/
theorem sorted_tail {x : Int} {xs : List Int} (h : Sorted (x :: xs)) :
    Sorted xs := by
  intro i j hij hj
  have hle := h (i + 1) (j + 1) (by omega) (by simpa using hj)
  have hshift : ∀ k : Nat, (x :: xs).getD (k + 1) 0 = xs.getD k 0 := by
    intro k; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]; simp
  rw [hshift i, hshift j] at hle
  exact hle

private theorem count_cons_self (x : Int) (xs : List Int) :
    (x :: xs).count x = xs.count x + 1 := by
  simp [List.count_cons]

/-- **A sorted list is determined by its element counts.** This is the
bridge that makes "sorted and a permutation of the input" and "equal to
THE sorted permutation of the input" the same claim, so each sort can
prove whichever its loop invariant reaches and report both. -/
theorem sorted_perm_unique : ∀ {l₁ l₂ : List Int}, Sorted l₁ → Sorted l₂ →
    (∀ v : Int, l₁.count v = l₂.count v) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ _ hc
      cases l₂ with
      | nil => rfl
      | cons y ys =>
          exact absurd (hc y) (by simp [count_cons_self])
  | cons x xs ih =>
      intro l₂ hax hbs hc
      cases l₂ with
      | nil => exact absurd (hc x) (by simp [count_cons_self])
      | cons y ys =>
          have hxb : x ∈ y :: ys := by
            have : 0 < (y :: ys).count x := by
              rw [← hc x, count_cons_self]; omega
            exact List.count_pos_iff.mp this
          have hya : y ∈ x :: xs := by
            have : 0 < (x :: xs).count y := by
              rw [hc y, count_cons_self]; omega
            exact List.count_pos_iff.mp this
          have hxy : x = y := by
            rcases List.mem_cons.mp hxb with h | h
            · exact h
            · rcases List.mem_cons.mp hya with h' | h'
              · exact h'.symm
              · exact Int.le_antisymm (sorted_head_le hax h')
                  (sorted_head_le hbs h)
          subst hxy
          have hct : ∀ v : Int, xs.count v = ys.count v := by
            intro v
            have := hc v
            rw [List.count_cons, List.count_cons] at this
            omega
          rw [ih (sorted_tail hax) (sorted_tail hbs) hct]

/-- **The two readings of a sort's postcondition are the same.** Given
that `post` is sorted and has `pre`'s element counts, `post` IS
`sortSpec pre` — the unique sorted permutation, defined in
`Examples.InsertionSort.Pure` as an insertion fold. -/
theorem eq_sortSpec_of_sorted_count {pre post : List Int}
    (hs : Sorted post) (hc : ∀ v : Int, post.count v = pre.count v) :
    post = GoLean.Examples.InsertionSort.sortSpec pre :=
  sorted_perm_unique hs (GoLean.Examples.InsertionSort.sortSpec_sorted pre)
    (fun v => by
      rw [hc v, GoLean.Examples.InsertionSort.sortSpec_count])

/-- The converse direction, for a sort whose invariant lands on the
functional form instead. -/
theorem sorted_count_of_eq_sortSpec {pre post : List Int}
    (h : post = GoLean.Examples.InsertionSort.sortSpec pre) :
    Sorted post ∧ ∀ v : Int, post.count v = pre.count v := by
  subst h
  exact ⟨GoLean.Examples.InsertionSort.sortSpec_sorted pre,
    fun v => GoLean.Examples.InsertionSort.sortSpec_count pre v⟩

end GoLean.Examples.SortShared
