import GoLeanProofs.Examples.HistogramProgram
import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit

/-!
# Histogram — Pure

The specification layer of the `histogram` example (Gallery Campaign
G1, the flagship kit-integration exercise; charter
`docs/2026-08-15_gallery-campaign.md` §G0 item 4 / §G1).

Two layers live here, and the split matters:

* **STATEMENT vocabulary** — `occurrences` and `distinctCount`, the two
  spec functions the headline mentions. Both are first-order list
  functions a reader can check by eye, and both are ORDER-INVARIANT
  functions OF THE RETURNED DATA (the S3 relational style): they never
  mention the map, the machine, or the setup family.
* **PROOF vocabulary** — `bump`/`countsList` (the abstract content of
  the map data cell) and `histFamily` (the setup family), plus the
  bridges from those to the statement functions.

## Kit gaps witnessed here (campaign log `g1.md`, KIT-GAP list)

* **GAP-P1 `bump`/`countsList`.** The counting-fold layer is a verbatim
  re-derivation of `Examples/WordCount/Pure.lean`'s. G0 item 3b
  deliberately left it in wordcount ("wordcount spec vocabulary, not map
  machinery"); as the chartered consumer this example shows that call
  was wrong — the fold, `setk_cnt_succ`, `countsList_append_word`,
  `cnt_countsList'`, `countsList_val_le` and the nodup-keys chain are
  map-histogram machinery, not wordcount's. Shape wanted: these lemmas
  in `MapMem` over `bump`, leaving each example only its own statement
  functions and their bridges.
* **GAP-P2 the setup family.** `histFamily` and its four facts are an
  address-free re-derivation of `wcFamily`. The P5 lift covered the
  setup INDUCTION but explicitly not the family (G0 log, unit 3a JC).
  Shape wanted: a `familyMod k` generic over the modulus with
  `length`/`range`/`set`/`getD` proven once.

The `(countsList l).length = distinctCount l` bridge below is NOT a gap
— it is this example's own spec content.
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-! ## The statement vocabulary (order-invariant, §10b) -/

/-- How many times `v` occurs in `l`. -/
def occurrences (v : Int) (l : List Int) : Nat :=
  (l.filter (· = v)).length

/-- How many DISTINCT values `l` holds — each value counted exactly
once, at its LAST occurrence. Order-invariant in the sense the
∀-choices quantifier needs: it is a function of `l` alone, so no
map-iteration order can be read off it. -/
def distinctCount : List Int → Nat
  | [] => 0
  | v :: rest => (if v ∈ rest then 0 else 1) + distinctCount rest

/-! ## The proof vocabulary: the counting fold

GAP-P1 (see the module docstring): re-derived from
`Examples/WordCount/Pure.lean`. -/

/-- One value lands in the counts list: increment the first occurrence
of the key, or append `(v, 1)` — first-occurrence insertion order,
matching the machine's `mapAssign`. -/
def bump : List (Int × Nat) → Int → List (Int × Nat)
  | [], v => [(v, 1)]
  | (k, c) :: rest, v =>
      if k = v then (k, c + 1) :: rest else (k, c) :: bump rest v

/-- The counts list after processing `l`, in first-occurrence insertion
order — the abstract content of the map data cell. -/
def countsList (l : List Int) : List (Int × Nat) :=
  l.foldl bump []

/-- What the machine's write computes is `bump`: the value written is
`counts[v] + 1` at the first occurrence (or `0 + 1` fresh). -/
theorem setk_cnt_succ :
    ∀ (kvs : List (Int × Nat)) (v : Int),
    setk kvs v (cnt kvs v + 1) = bump kvs v := by
  intro kvs
  induction kvs with
  | nil => intro v; rfl
  | cons kv rest ih =>
      intro v
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = v
      · simp [setk, cnt, bump, hk]
      · simp [setk, cnt, bump, hk, ih v]

theorem countsList_append_value (p : List Int) (v : Int) :
    countsList (p ++ [v]) = bump (countsList p) v := by
  simp [countsList, List.foldl_append]

theorem countsList_nil : countsList [] = [] := rfl

/-! ### `occurrences` against the fold -/

private theorem occurrences_nil (v : Int) : occurrences v [] = 0 := rfl

private theorem occurrences_cons (v w : Int) (l : List Int) :
    occurrences v (w :: l)
      = (if w = v then 1 else 0) + occurrences v l := by
  simp only [occurrences, List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

private theorem cnt_bump (kvs : List (Int × Nat)) (w x : Int) :
    cnt (bump kvs w) x
      = if x = w then cnt kvs w + 1 else cnt kvs x := by
  induction kvs with
  | nil =>
      by_cases hx : x = w
      · simp [bump, cnt, hx]
      · simp [bump, cnt, hx, Ne.symm hx]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · subst hk
        by_cases hx : x = k
        · simp [bump, cnt, hx]
        · simp [bump, cnt, Ne.symm hx, hx]
      · by_cases hxk : k = x
        · subst hxk
          simp [bump, cnt, hk]
        · simp [bump, cnt, hk, hxk, ih]

private theorem cnt_countsList (l : List Int) :
    ∀ (kvs : List (Int × Nat)) (x : Int),
    cnt (List.foldl bump kvs l) x = cnt kvs x + occurrences x l := by
  induction l with
  | nil => intro kvs x; simp [occurrences_nil]
  | cons w rest ih =>
      intro kvs x
      simp only [List.foldl_cons, ih, cnt_bump, occurrences_cons]
      by_cases hx : x = w
      · subst hx
        have h1 : (if x = x then cnt kvs x + 1 else cnt kvs x)
            = cnt kvs x + 1 := if_pos rfl
        have h2 : (if x = x then 1 else 0) = 1 := if_pos rfl
        omega
      · have h1 : (if x = w then cnt kvs w + 1 else cnt kvs x)
            = cnt kvs x := if_neg hx
        have h2 : (if w = x then 1 else 0) = 0 := if_neg (Ne.symm hx)
        omega

/-- **The queried-key bridge**: the map's count at any key is that
key's number of occurrences (0 on both sides for an absent key — Go's
zero-value read is exactly the `occurrences = 0` case). -/
theorem cnt_countsList' (l : List Int) (x : Int) :
    cnt (countsList l) x = occurrences x l := by
  simpa [countsList, cnt] using cnt_countsList l [] x

/-! ### The key column: membership, nodup, and the value bound -/

private theorem mem_bump {kvs : List (Int × Nat)} {w : Int}
    {p : Int × Nat} (h : p ∈ bump kvs w) :
    p.1 = w ∨ p ∈ kvs := by
  induction kvs with
  | nil =>
      simp only [bump, List.mem_singleton] at h
      exact .inl (by rw [h])
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp only [bump, if_pos hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inl (by rw [h1]; exact hk)
        · exact .inr (List.mem_cons.mpr (.inr h1))
      · simp only [bump, if_neg hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inr (List.mem_cons.mpr (.inl h1))
        · rcases ih h1 with h2 | h2
          · exact .inl h2
          · exact .inr (List.mem_cons.mpr (.inr h2))

theorem countsList_key_mem (l : List Int) :
    ∀ (kvs : List (Int × Nat)) (p : Int × Nat),
    p ∈ List.foldl bump kvs l → p.1 ∈ l ∨ p ∈ kvs := by
  induction l with
  | nil => intro kvs p h; exact .inr h
  | cons w rest ih =>
      intro kvs p h
      simp only [List.foldl_cons] at h
      rcases ih (bump kvs w) p h with h | h
      · exact .inl (by simp [h])
      · rcases mem_bump h with h | h
        · exact .inl (by simp [h])
        · exact .inr h

private theorem nodup_keys_bump {kvs : List (Int × Nat)} {w : Int}
    (h : (kvs.map Prod.fst).Nodup) :
    ((bump kvs w).map Prod.fst).Nodup := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at h
      by_cases hk : k = w
      · simpa [bump, hk, List.nodup_cons] using h
      · simp only [bump, if_neg hk, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih h.2⟩
        intro hc
        rcases List.mem_map.mp hc with ⟨p, hp, hpk⟩
        rcases mem_bump hp with h1 | h1
        · exact hk (hpk ▸ h1)
        · exact h.1 (List.mem_map.mpr ⟨p, h1, hpk⟩)

private theorem nodup_keys_countsList (l : List Int) :
    ∀ kvs : List (Int × Nat), (kvs.map Prod.fst).Nodup →
    ((List.foldl bump kvs l).map Prod.fst).Nodup := by
  induction l with
  | nil => intro kvs h; exact h
  | cons w rest ih =>
      intro kvs h
      exact ih (bump kvs w) (nodup_keys_bump h)

private theorem cnt_of_mem_nodup :
    ∀ {kvs : List (Int × Nat)} {k : Int} {c : Nat},
    (kvs.map Prod.fst).Nodup → (k, c) ∈ kvs → cnt kvs k = c := by
  intro kvs
  induction kvs with
  | nil => intro k c _ h; cases h
  | cons kv rest ih =>
      intro k c hnd h
      obtain ⟨k', c'⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with h | h
      · injection h with h1 h2
        subst h1; subst h2
        simp [cnt]
      · have hk : k' ≠ k := by
          intro hc
          subst hc
          exact hnd.1 (List.mem_map.mpr ⟨(k', c), h, rfl⟩)
        simp only [cnt, if_neg hk]
        exact ih hnd.2 h

/-- Value bound: no count exceeds the number of values counted. -/
theorem countsList_val_le (l : List Int) {p : Int × Nat}
    (hp : p ∈ countsList l) : p.2 ≤ l.length := by
  obtain ⟨k, c⟩ := p
  have hnd := nodup_keys_countsList l [] (by simp)
  have hcnt : cnt (countsList l) k = c := cnt_of_mem_nodup hnd hp
  have := cnt_countsList' l k
  rw [hcnt] at this
  simp only [occurrences] at this
  have hle : (l.filter (· = k)).length ≤ l.length :=
    List.length_filter_le _ _
  omega

/-! ## The cardinality bridge: `(countsList l).length = distinctCount l`

This example's own spec content — the fact that makes the `for range`
loop's answer readable. The auxiliary `newCount seen l` counts the
values of `l` that are distinct AND not already accounted for by
`seen`; `newCount []` is `distinctCount`, and the fold's length grows
by exactly `newCount` over its key column. -/

/-- Values of `l` that are neither in `seen` nor repeated later. -/
private def newCount (seen : List Int) : List Int → Nat
  | [] => 0
  | v :: rest => (if v ∈ seen ∨ v ∈ rest then 0 else 1) + newCount seen rest

private theorem newCount_nil_seen (l : List Int) :
    newCount [] l = distinctCount l := by
  induction l with
  | nil => rfl
  | cons v rest ih => simp [newCount, distinctCount, ih]

/-- `newCount` sees `seen` only through membership. -/
private theorem newCount_congr {s₁ s₂ : List Int}
    (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : ∀ l, newCount s₁ l = newCount s₂ l := by
  intro l
  induction l with
  | nil => rfl
  | cons v rest ih =>
      simp only [newCount, ih]
      by_cases hv : v ∈ s₁
      · simp [hv, (h v).mp hv]
      · have hv2 : v ∉ s₂ := fun hc => hv ((h v).mpr hc)
        simp [hv, hv2]

/-- Adding a FRESH key to `seen` removes exactly the one it accounts
for. -/
private theorem newCount_cons_seen {v : Int} {seen : List Int}
    (hv : v ∉ seen) :
    ∀ l, newCount seen l = newCount (v :: seen) l + (if v ∈ l then 1 else 0) := by
  intro l
  induction l with
  | nil => simp [newCount]
  | cons w rest ih =>
      simp only [newCount, ih, List.mem_cons]
      by_cases hwv : w = v
      · subst hwv
        by_cases hwr : w ∈ rest <;> simp [hv, hwr] <;> omega
      · by_cases hws : w ∈ seen <;> by_cases hwr : w ∈ rest <;>
          by_cases hvr : v ∈ rest <;>
            simp [hwv, hws, hwr, hvr, Ne.symm hwv] <;> omega

private theorem bump_length (kvs : List (Int × Nat)) (v : Int) :
    (bump kvs v).length
      = kvs.length + (if v ∈ kvs.map Prod.fst then 0 else 1) := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = v
      · simp [bump, hk]
      · have hvk : ¬ (v = k) := fun hc => hk hc.symm
        simp only [bump, if_neg hk, List.length_cons, ih, List.map_cons,
          List.mem_cons]
        by_cases hm : v ∈ rest.map Prod.fst <;> simp [hm, hvk] <;> omega

private theorem bump_keys_mem (kvs : List (Int × Nat)) (v x : Int) :
    x ∈ (bump kvs v).map Prod.fst ↔ (x = v ∨ x ∈ kvs.map Prod.fst) := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = v
      · simp only [bump, if_pos hk, List.map_cons, List.mem_cons]
        constructor
        · intro h; rcases h with h | h
          · exact .inl (h.trans hk)
          · exact .inr (.inr h)
        · intro h; rcases h with h | h | h
          · exact .inl (h.trans hk.symm)
          · exact .inl h
          · exact .inr h
      · simp only [bump, if_neg hk, List.map_cons, List.mem_cons, ih]
        constructor
        · intro h; rcases h with h | h | h
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)
        · intro h; rcases h with h | h | h
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

private theorem foldl_bump_length (l : List Int) :
    ∀ kvs : List (Int × Nat),
    (List.foldl bump kvs l).length
      = kvs.length + newCount (kvs.map Prod.fst) l := by
  induction l with
  | nil => intro kvs; simp [newCount]
  | cons v rest ih =>
      intro kvs
      simp only [List.foldl_cons, ih, bump_length, newCount]
      by_cases hv : v ∈ kvs.map Prod.fst
      · have hcongr : ∀ x, x ∈ (bump kvs v).map Prod.fst
            ↔ x ∈ kvs.map Prod.fst := by
          intro x
          rw [bump_keys_mem]
          constructor
          · intro h; rcases h with h | h
            · exact h ▸ hv
            · exact h
          · intro h; exact .inr h
        rw [newCount_congr hcongr rest]
        simp [hv]
      · have hcongr : ∀ x, x ∈ (bump kvs v).map Prod.fst
            ↔ x ∈ v :: kvs.map Prod.fst := by
          intro x
          rw [bump_keys_mem]
          simp [List.mem_cons]
        rw [newCount_congr hcongr rest,
          newCount_cons_seen hv rest]
        by_cases hvr : v ∈ rest <;> simp [hv, hvr] <;> omega

/-- **The cardinality bridge**: the histogram has exactly as many
entries as `l` has distinct values. This is what makes the `for range
counts` answer readable — the loop runs once per entry at EVERY
iteration order, and the entry count is a function of the data. -/
theorem countsList_length (l : List Int) :
    (countsList l).length = distinctCount l := by
  rw [countsList, foldl_bump_length l []]
  simp [newCount_nil_seen]

theorem distinctCount_le (l : List Int) : distinctCount l ≤ l.length := by
  induction l with
  | nil => simp [distinctCount]
  | cons v rest ih =>
      simp only [distinctCount, List.length_cons]
      by_cases hv : v ∈ rest <;> simp [hv] <;> omega

theorem countsList_length_le (l : List Int) :
    (countsList l).length ≤ l.length := by
  rw [countsList_length]; exact distinctCount_le l

/-! ## The setup family

GAP-P2 (see the module docstring): an address-free re-derivation of
`Examples/WordCount/Family.lean`'s `wcFamily`. -/

/-- The setup loop's family: `v[i] = seed + i%3`, wrapped at uint64 —
three distinct values once `n ≥ 3`, with controllable multiplicities. -/
def histFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i % 3) % 2 ^ 64 : Nat) : Int))

theorem histFamily_length (n seed : Nat) :
    (histFamily n seed).length = n := by
  simp [histFamily]

theorem histFamily_range (n seed : Nat) :
    ∀ v ∈ histFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [histFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  have : (seed + i % 3) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

theorem histFamilyZ_range {n seed i : Nat} :
    ∀ v ∈ histFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact histFamily_range i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

private theorem histFamily_succ (i seed : Nat) :
    histFamily (i + 1) seed
      = histFamily i seed ++ [(((seed + i % 3) % 2 ^ 64 : Nat) : Int)] := by
  simp [histFamily, List.range_succ]

theorem histFamily_set {n seed i : Nat} (hi : i < n) :
    (histFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      = histFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (histFamily i seed).length = i := histFamily_length i seed
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, histFamily_succ]
  simp

theorem histFamily_getD {n seed m : Nat} (hm : m < n) :
    (histFamily n seed).getD m 0 = (((seed + m % 3) % 2 ^ 64 : Nat) : Int) := by
  rw [histFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

end GoLean.Examples.Histogram
