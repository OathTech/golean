import GoLeanProofs.SliceMem

/-!
# TwoSum — Pure

The example's entire mathematical content: the first-pair-in-scan-order
search `twoSumSpec`, its defining recursions (`findFrom` for the inner
scan, `findPair` for the outer), the characterisation lemmas that turn
"the recursion returned `some`/`none`" into first-order statements
about wrapped pair sums, and the setup family `tsFamily`
(`s[i] = seed + i`, wrapping).

`twoSumSpec` is STATEMENT vocabulary — the headline says the returned
index pair IS `twoSumSpec` of the returned data, and nothing else in
this module reaches the statement layer. The wrapped pair sum is
spelled `(xs.getD a 0 + xs.getD b 0) % 2 ^ 64` throughout — Go's
uint64 addition on in-range values, written with `Int.emod` so the
statement needs no machine vocabulary.
-/

namespace GoLean.Examples.TwoSum

open GoLean GoLean.SliceMem

set_option maxRecDepth 1000000

/-! ## The setup family `s[i] = seed + i` (wrapping)

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (twosum), [lane B] KIT GAP —
-- familyF): `SliceMem.familyMod k` is the family `seed + i % k`; this
-- example's setup is `seed + i` (the identity index function), which
-- `familyMod` cannot express at any `k`. The shape wanted is a family
-- parameterized by an index function,
-- `SliceMem.familyF (f : Nat → Nat) (n seed : Nat) : List Int`
-- with `length`/`range`/`Z_range`/`succ`/`set`/`getD` proven once —
-- then `familyMod k = familyF (· % k)`, twosum = `familyF id`,
-- rle = `familyF (· / 3)`. Until that lands, the six facts below are
-- local re-derivations (mirroring the `familyMod` proofs verbatim,
-- with `i % k` replaced by `i`). `prefixPad` itself IS
-- family-generic, so the copy-loop invariant needs only the one
-- `set`-step instance `prefixPad_tsFamily_set`. -/

/-- The setup family: `fam[i] = (seed + i) % 2^64`. -/
def tsFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))

theorem tsFamily_length (n seed : Nat) : (tsFamily n seed).length = n := by
  simp [tsFamily]

theorem tsFamily_range (n seed : Nat) :
    ∀ v ∈ tsFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [tsFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  have : (seed + i) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

/-- The family prefix with a zero tail stays in uint64 range. -/
theorem tsFamilyZ_range {seed i m : Nat} :
    ∀ v ∈ tsFamily i seed ++ List.replicate (m - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact tsFamily_range i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem tsFamily_succ (i seed : Nat) :
    tsFamily (i + 1) seed
      = tsFamily i seed ++ [(((seed + i) % 2 ^ 64 : Nat) : Int)] := by
  simp [tsFamily, List.range_succ]

/-- One setup store advances the family prefix. -/
theorem tsFamily_set {n seed i : Nat} (hi : i < n) :
    (tsFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i) % 2 ^ 64 : Nat) : Int)
      = tsFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (tsFamily i seed).length = i := tsFamily_length i seed
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, tsFamily_succ]
  simp

/-- The family's element at an in-range index. -/
theorem tsFamily_getD {n seed m : Nat} (hm : m < n) :
    (tsFamily n seed).getD m 0 = (((seed + m) % 2 ^ 64 : Nat) : Int) := by
  rw [tsFamily, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-! ## The copy-loop invariant (the kit's `prefixPad` at `tsFamily`) -/

/-- The `vals` array after `m` copy steps. -/
abbrev tsPre (m seed : Nat) : List Int := prefixPad tsFamily 8 m seed

theorem tsPre_zero (seed : Nat) : tsPre 0 seed = List.replicate 8 0 :=
  prefixPad_zero rfl

theorem tsPre_length {m seed : Nat} (h : m ≤ 8) :
    (tsPre m seed).length = 8 :=
  prefixPad_length (tsFamily_length m seed) h

theorem tsPre_range {m seed : Nat} :
    ∀ v ∈ tsPre m seed, 0 ≤ v ∧ v < 2 ^ 64 :=
  prefixPad_range (tsFamily_range m seed)

/-- One copy store advances the prefix (the `tsFamily` instance of the
kit's `prefixPad_familyMod_set`; local for the same kit-gap reason as
the family itself). -/
theorem tsPre_set {seed m : Nat} (hm : m < 8) :
    (tsPre m seed).set m (((seed + m) % 2 ^ 64 : Nat) : Int)
      = tsPre (m + 1) seed :=
  tsFamily_set hm

theorem tsPre_full {n seed : Nat} :
    tsPre n seed
      = tsFamily n seed
          ++ List.replicate (8 - (tsFamily n seed).length) 0 :=
  prefixPad_full (tsFamily_length n seed)

/-! ## The specification function

`twoSum`'s contract: the FIRST index pair `(i, j)` in scan order
(outer `i` ascending, inner `j` ascending, always `i < j`) whose
wrapped sum hits the target — or the out-of-range sentinel
`(len, len)` when no pair does. The two recursions below mirror that
scan structurally; the characterisation lemmas afterwards state what
they compute in first-order terms, and the first-order corollary in
the root is stated from those, never from the recursions. -/

/-- The inner scan: the first `u ≥ j` with
`(xs[i] + xs[u]) % 2^64 = tgt`, or `none`. -/
def findFrom (xs : List Int) (tgt : Int) (i j : Nat) : Option Nat :=
  if _h : j < xs.length then
    if (xs.getD i 0 + xs.getD j 0) % 2 ^ 64 = tgt then some j
    else findFrom xs tgt i (j + 1)
  else none
termination_by xs.length - j

/-- The outer scan: the first pair `(a, b)` in scan order with
`a ≥ i`. -/
def findPair (xs : List Int) (tgt : Int) (i : Nat) : Option (Nat × Nat) :=
  if _h : i < xs.length then
    match findFrom xs tgt i (i + 1) with
    | some j => some (i, j)
    | none => findPair xs tgt (i + 1)
  else none
termination_by xs.length - i

/-- **The specification**: the first pair in scan order as machine
integers, or the sentinel `(len, len)`. -/
def twoSumSpec (xs : List Int) (tgt : Int) : Int × Int :=
  match findPair xs tgt 0 with
  | some (i, j) => ((i : Int), (j : Int))
  | none => ((xs.length : Int), (xs.length : Int))

/-! ### Defining equations (the machine induction's step interface) -/

theorem findFrom_hit {xs : List Int} {tgt : Int} {i j : Nat}
    (hj : j < xs.length) (h : (xs.getD i 0 + xs.getD j 0) % 2 ^ 64 = tgt) :
    findFrom xs tgt i j = some j := by
  rw [findFrom, dif_pos hj, if_pos h]

theorem findFrom_miss {xs : List Int} {tgt : Int} {i j : Nat}
    (hj : j < xs.length)
    (h : ¬ (xs.getD i 0 + xs.getD j 0) % 2 ^ 64 = tgt) :
    findFrom xs tgt i j = findFrom xs tgt i (j + 1) := by
  rw [findFrom, dif_pos hj, if_neg h]

theorem findFrom_end {xs : List Int} {tgt : Int} {i j : Nat}
    (hj : xs.length ≤ j) : findFrom xs tgt i j = none := by
  rw [findFrom, dif_neg (by omega)]

theorem findPair_hit {xs : List Int} {tgt : Int} {i j : Nat}
    (hi : i < xs.length) (h : findFrom xs tgt i (i + 1) = some j) :
    findPair xs tgt i = some (i, j) := by
  rw [findPair, dif_pos hi, h]

theorem findPair_step {xs : List Int} {tgt : Int} {i : Nat}
    (hi : i < xs.length) (h : findFrom xs tgt i (i + 1) = none) :
    findPair xs tgt i = findPair xs tgt (i + 1) := by
  rw [findPair, dif_pos hi, h]

theorem findPair_end {xs : List Int} {tgt : Int} {i : Nat}
    (hi : xs.length ≤ i) : findPair xs tgt i = none := by
  rw [findPair, dif_neg (by omega)]

/-! ### Characterisations -/

/-- What `findFrom … = some u` says: `u` is in range, at or past the
start, its pair sum hits, and no earlier candidate in the row does. -/
theorem findFrom_some {xs : List Int} {tgt : Int} {i j u : Nat}
    (h : findFrom xs tgt i j = some u) :
    j ≤ u ∧ u < xs.length
      ∧ (xs.getD i 0 + xs.getD u 0) % 2 ^ 64 = tgt
      ∧ ∀ v, j ≤ v → v < u → ¬ (xs.getD i 0 + xs.getD v 0) % 2 ^ 64 = tgt := by
  by_cases hj : j < xs.length
  · by_cases hhit : (xs.getD i 0 + xs.getD j 0) % 2 ^ 64 = tgt
    · rw [findFrom_hit hj hhit, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hj, hhit, fun v h1 h2 => by omega⟩
    · rw [findFrom_miss hj hhit] at h
      obtain ⟨h1, h2, h3, h4⟩ := findFrom_some h
      refine ⟨by omega, h2, h3, fun v hv1 hv2 => ?_⟩
      rcases Nat.lt_or_ge v (j + 1) with hlt | hge
      · have : v = j := by omega
        subst this; exact hhit
      · exact h4 v hge hv2
  · rw [findFrom_end (by omega)] at h
    cases h
termination_by xs.length - j

/-- What `findFrom … = none` says: no candidate in the row from `j`
hits. -/
theorem findFrom_none {xs : List Int} {tgt : Int} {i j : Nat}
    (h : findFrom xs tgt i j = none) :
    ∀ v, j ≤ v → v < xs.length →
      ¬ (xs.getD i 0 + xs.getD v 0) % 2 ^ 64 = tgt := by
  intro v hv1 hv2
  by_cases hj : j < xs.length
  · by_cases hhit : (xs.getD i 0 + xs.getD j 0) % 2 ^ 64 = tgt
    · rw [findFrom_hit hj hhit] at h; cases h
    · rw [findFrom_miss hj hhit] at h
      rcases Nat.lt_or_ge v (j + 1) with hlt | hge
      · have : v = j := by omega
        subst this; exact hhit
      · exact findFrom_none h v hge hv2
  · omega
termination_by xs.length - j

/-- What `findPair … = some (a, b)` says: a genuine in-range pair at
or past row `i`, whose sum hits, with NO scan-earlier pair (from row
`i` on) hitting. -/
theorem findPair_some {xs : List Int} {tgt : Int} {i : Nat}
    {a b : Nat} (h : findPair xs tgt i = some (a, b)) :
    i ≤ a ∧ a < b ∧ b < xs.length
      ∧ (xs.getD a 0 + xs.getD b 0) % 2 ^ 64 = tgt
      ∧ ∀ a' b', i ≤ a' → a' < b' → b' < xs.length →
          (a' < a ∨ (a' = a ∧ b' < b)) →
          ¬ (xs.getD a' 0 + xs.getD b' 0) % 2 ^ 64 = tgt := by
  by_cases hi : i < xs.length
  · cases hf : findFrom xs tgt i (i + 1) with
    | some u =>
        rw [findPair_hit hi hf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3, h4⟩ := findFrom_some hf
        refine ⟨Nat.le_refl _, by omega, h2, h3, ?_⟩
        intro a' b' ha1 hab hb hlex
        rcases hlex with hlt | ⟨rfl, hb'⟩
        · omega
        · exact h4 b' (by omega) hb'
    | none =>
        rw [findPair_step hi hf] at h
        obtain ⟨h1, h2, h3, h4, h5⟩ := findPair_some h
        refine ⟨by omega, h2, h3, h4, ?_⟩
        intro a' b' ha1 hab hb hlex
        rcases Nat.lt_or_ge a' (i + 1) with hlt | hge
        · have : a' = i := by omega
          subst this
          exact findFrom_none hf b' (by omega) hb
        · exact h5 a' b' hge hab hb hlex
  · rw [findPair_end (by omega)] at h
    cases h
termination_by xs.length - i

/-- What `findPair … = none` says: no pair from row `i` on hits. -/
theorem findPair_none {xs : List Int} {tgt : Int} {i : Nat}
    (h : findPair xs tgt i = none) :
    ∀ a b, i ≤ a → a < b → b < xs.length →
      ¬ (xs.getD a 0 + xs.getD b 0) % 2 ^ 64 = tgt := by
  intro a b ha hab hb
  by_cases hi : i < xs.length
  · cases hf : findFrom xs tgt i (i + 1) with
    | some u => rw [findPair_hit hi hf] at h; cases h
    | none =>
        rw [findPair_step hi hf] at h
        rcases Nat.lt_or_ge a (i + 1) with hlt | hge
        · have : a = i := by omega
          subst this
          exact findFrom_none hf b (by omega) hb
        · exact findPair_none h a b hge hab hb
  · omega
termination_by xs.length - i

/-! ### The first-order reading of `twoSumSpec` (the corollary's
bridge) -/

/-- The full first-order characterisation: either the spec names a
genuine first pair, or it is the sentinel and no pair exists. -/
theorem twoSumSpec_char (xs : List Int) (tgt : Int) :
    (∃ a b : Nat, twoSumSpec xs tgt = ((a : Int), (b : Int))
      ∧ a < b ∧ b < xs.length
      ∧ (xs.getD a 0 + xs.getD b 0) % 2 ^ 64 = tgt
      ∧ ∀ a' b' : Nat, a' < b' → b' < xs.length →
          (a' < a ∨ (a' = a ∧ b' < b)) →
          ¬ (xs.getD a' 0 + xs.getD b' 0) % 2 ^ 64 = tgt)
    ∨ (twoSumSpec xs tgt = ((xs.length : Int), (xs.length : Int))
      ∧ ∀ a b : Nat, a < b → b < xs.length →
          ¬ (xs.getD a 0 + xs.getD b 0) % 2 ^ 64 = tgt) := by
  cases hp : findPair xs tgt 0 with
  | some p =>
      obtain ⟨a, b⟩ := p
      obtain ⟨-, h2, h3, h4, h5⟩ := findPair_some hp
      exact .inl ⟨a, b, by rw [twoSumSpec, hp], h2, h3, h4,
        fun a' b' hab hb hlex => h5 a' b' (Nat.zero_le _) hab hb hlex⟩
  | none =>
      exact .inr ⟨by rw [twoSumSpec, hp],
        fun a b hab hb => findPair_none hp a b (Nat.zero_le _) hab hb⟩

end GoLean.Examples.TwoSum
