import GoLean.GoCore.MachineSound

/-!
# Value-level lemmas: normalized int arrays, positional writes, and
sorted-permutation uniqueness (proof-automation arc phase 3, 2026-08-01)

Plain Lean over `GoValue`/`List`/`Array` — no Iris, no WP. These are the
facts a walk needs when the DATA it manipulates is symbolic rather than a
literal: an array whose contents are known only up to a permutation, a
write at a position given by a length, a sort whose input order is not
determined.

They are stated over arbitrary lists, kinds and elements: nothing here
mentions a program, a lowering, or the quorum target (standing
over-specialization check). The quorum use is one instantiation.

Three groups:

1. **Positional read/write** (`arraySet_middle`, `arrayGet_middle`): the
   machine's `arraySet`/`arrayGet` at index `pre.length` of
   `pre ++ x :: rest`. This is what a right-to-left fill loop needs when
   the number of already-filled slots is a variable.
2. **Normalization of an int array** (`normalizeArrayForTy_int`): an
   array all of whose elements are already-normalized ints of one kind
   normalizes to itself, at ANY fuel and ANY state. Without this a store
   into a symbolic array is unreachable by `simp`, which can only compute
   `normalizeArrayForTy` on a literal.
3. **Sorted-permutation uniqueness** (`eq_of_perm_of_pairwise`) and its
   corollary for the machine's sort (`mergeSort_eq_of_perm`): two sorted
   lists that are permutations of each other are equal, hence
   `List.mergeSort` gives the SAME answer on every permutation of its
   input. This is what lets a proof about a nondeterministically-filled
   array reach the sort without enumerating the fill orders.
   Antisymmetry is required only ON THE ELEMENTS PRESENT, which is what
   makes it usable at `(Int × IntKind)` — a type where the machine's
   comparison `fun a b => a.1 ≤ b.1` is NOT globally antisymmetric.
-/

open GoLean GoLean.GoCore

namespace GoLean.Iris

/-! ## 1. Positional read and write -/

theorem list_map_eraseIdx {α β : Type _} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: t, i + 1 => by
    simp only [List.map_cons, List.eraseIdx_cons_succ, list_map_eraseIdx f t i]

theorem list_getElem?_middle {α : Type _} (pre : List α) (x : α) (rest : List α) :
    (pre ++ x :: rest)[pre.length]? = some x := by
  induction pre with
  | nil => simp
  | cons a t _ => simp

theorem list_set_middle {α : Type _} (pre : List α) (x : α) (rest : List α) (y : α) :
    (pre ++ x :: rest).set pre.length y = pre ++ y :: rest := by
  induction pre with
  | nil => simp
  | cons a t ih => simp [ih]

/-- **The positional write.** The machine's `arraySet` at index
`pre.length` of `pre ++ old :: rest` replaces exactly that slot, with the
element coerced by the machine's own `coerceStoredValue`. Stated with the
coercion as a hypothesis so the lemma is independent of the element
type. -/
theorem arraySet_middle {pre rest : List GoValue} {old new coerced : GoValue}
    (hc : coerceStoredValue old new = .ok coerced) :
    arraySet (pre ++ old :: rest).toArray (pre.length : Int) new
      = .ok (pre ++ coerced :: rest).toArray := by
  have hlt : pre.length < (pre ++ old :: rest).toArray.size := by
    simp only [List.size_toArray, List.length_append, List.length_cons]
    omega
  have hidx : arrayIndexNat (pre ++ old :: rest).toArray (pre.length : Int)
      = .ok pre.length := by
    simp only [arrayIndexNat]
    rw [if_neg (by omega), Int.toNat_natCast, if_pos hlt]
    rfl
  have hget : (pre ++ old :: rest).toArray[pre.length]? = some old := by
    rw [List.getElem?_toArray]
    exact list_getElem?_middle pre old rest
  simp only [arraySet, hidx, hget, hc, Bind.bind, Except.bind, pure, Except.pure]
  simp only [Array.set!, Array.setIfInBounds, dif_pos hlt, List.set_toArray,
    list_set_middle]

/-- The positional write with the index given as a separate `Nat` — the
form a proof reaches when the index is a loop variable known to equal the
prefix length, and the one that avoids rewriting `pre` itself. -/
theorem arraySet_middle' {pre rest : List GoValue} {old new coerced : GoValue}
    {j : Nat} (hj : j = pre.length)
    (hc : coerceStoredValue old new = .ok coerced) :
    arraySet (pre ++ old :: rest).toArray (j : Int) new
      = .ok (pre ++ coerced :: rest).toArray := by
  subst hj; exact arraySet_middle hc

/-- **The positional read.** -/
theorem arrayGet_middle {pre rest : List GoValue} {x : GoValue} :
    arrayGet (pre ++ x :: rest).toArray (pre.length : Int) = .ok x := by
  have hlt : pre.length < (pre ++ x :: rest).toArray.size := by
    simp only [List.size_toArray, List.length_append, List.length_cons]
    omega
  have hidx : arrayIndexNat (pre ++ x :: rest).toArray (pre.length : Int)
      = .ok pre.length := by
    simp only [arrayIndexNat]
    rw [if_neg (by omega), Int.toNat_natCast, if_pos hlt]
    rfl
  have hget : (pre ++ x :: rest).toArray[pre.length]? = some x := by
    rw [List.getElem?_toArray]
    exact list_getElem?_middle pre x rest
  simp only [arrayGet, hidx, hget, Bind.bind, Except.bind, pure, Except.pure]

/-- The positional read with the index given as a separate `Nat`. -/
theorem arrayGet_middle' {pre rest : List GoValue} {x : GoValue} {j : Nat}
    (hj : j = pre.length) :
    arrayGet (pre ++ x :: rest).toArray (j : Int) = .ok x := by
  subst hj; exact arrayGet_middle

/-! ## 2. Normalization of an already-normalized int array -/

/-- An array of already-normalized ints of one kind normalizes to itself,
at any fuel and in any state — so a store into a SYMBOLIC array is
computable where `simp` alone (which needs a literal) is not. -/
theorem normalizeArrayForTy_int (fuel : Nat) (σ : ExecState) (kind : IntKind) :
    ∀ l : List GoValue,
      (∀ x ∈ l, ∃ v : Int, x = .int v kind ∧ kind.normalize v = v) →
      normalizeArrayForTy fuel σ (.int kind) l = .ok l.toArray := by
  intro l
  induction l with
  | nil => intro _; simp only [normalizeArrayForTy]; rfl
  | cons a t ih =>
    intro h
    obtain ⟨v, rfl, hv⟩ := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    rw [List.toArray_cons]
    simp only [normalizeArrayForTy, normalizeValueForTyFuel, ht, hv,
      Bind.bind, Except.bind, pure, Except.pure]

/-- The same fact at the public entry point, packaged for an ARRAY value
at an array type: `normalizeValueForTy` at `[n]kind`. -/
theorem normalizeValueForTy_intArray {σ : ExecState} {kind : IntKind} {n : Nat}
    {l : List GoValue} (hlen : l.length = n)
    (hall : ∀ x ∈ l, ∃ v : Int, x = .int v kind ∧ kind.normalize v = v) :
    normalizeValueForTy σ (.array n (.int kind)) (.array l.toArray)
      = .ok (.array l.toArray) := by
  have hsize : (l.toArray.size != n) = false := by simp [hlen]
  simp only [normalizeValueForTy, normalizeValueForTyFuel, hsize,
    Bool.false_eq_true, if_false, normalizeArrayForTy_int _ σ kind l hall,
    Bind.bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-! ## 2b. `int` normalization on the representable range -/

/-- Go's `int` is 64-bit two's complement: a value in `[-2^63, 2^63)`
rides through `IntKind.normalize` unchanged. (`Laws/Range` has the
nonnegative half; a right-to-left fill loop's index reaches `-1`, so the
signed half is needed too.) -/
theorem int_normalize_of_range {v : Int} (h0 : -(2 ^ 63) ≤ v) (h1 : v < 2 ^ 63) :
    IntKind.int.normalize v = v := by
  by_cases hneg : v < 0
  · have hmod : v % (2 : Int) ^ 64 = v + 2 ^ 64 := by
      omega
    simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, hmod, if_true,
      if_pos (show v + 2 ^ 64 ≥ (2 : Int) ^ (64 - 1) by omega)]
    omega
  · have hmod : v % (2 : Int) ^ 64 = v := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, hmod, if_true,
      if_neg (show ¬ (v ≥ (2 : Int) ^ (64 - 1)) by omega)]

/-! ## 3. Sorted-permutation uniqueness -/

/-- **Two sorted permutations of each other are equal.** Antisymmetry is
demanded only on the elements actually present, which is what makes this
usable at element types whose comparison ties distinct values (the
machine's sort compares `(Int × IntKind)` pairs by their `Int` only). -/
theorem eq_of_perm_of_pairwise {α : Type _} {le : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise le → l₂.Pairwise le →
      (∀ a ∈ l₁, ∀ b ∈ l₁, le a b → le b a → a = b) → l₁ = l₂
  | [], l₂, hp, _, _, _ => (hp.nil_eq).symm ▸ rfl
  | a :: t, [], hp, _, _, _ => absurd hp.length_eq (by simp)
  | a :: t, b :: t₂, hp, h₁, h₂, hanti => by
    have hab : a = b := by
      by_cases h : a = b
      · exact h
      · have hat₂ : a ∈ t₂ := by
          have : a ∈ b :: t₂ := hp.mem_iff.mp (by simp)
          rcases List.mem_cons.1 this with rfl | h'
          · exact absurd rfl h
          · exact h'
        have hbt : b ∈ t := by
          have : b ∈ a :: t := hp.mem_iff.mpr (by simp)
          rcases List.mem_cons.1 this with rfl | h'
          · exact absurd rfl h
          · exact h'
        have hle₁ : le a b := (List.pairwise_cons.1 h₁).1 b hbt
        have hle₂ : le b a := (List.pairwise_cons.1 h₂).1 a hat₂
        exact hanti a (by simp) b (by simp [hbt]) hle₁ hle₂
    subst hab
    have htt : t.Perm t₂ := hp.cons_inv
    have := eq_of_perm_of_pairwise htt (List.pairwise_cons.1 h₁).2
      (List.pairwise_cons.1 h₂).2
      (fun x hx y hy => hanti x (by simp [hx]) y (by simp [hy]))
    rw [this]

/-- **The machine's sort is order-blind.** `List.mergeSort` returns the
SAME list on every permutation of its input, provided the comparison is
transitive, total, and antisymmetric on the elements present. This is
what lets a proof reach a `slices.Sort` with the input known only as a
multiset — no enumeration of fill orders. -/
theorem mergeSort_eq_of_perm {α : Type _} {le : α → α → Bool}
    (htrans : ∀ a b c : α, le a b = true → le b c = true → le a c = true)
    (htotal : ∀ a b : α, (le a b || le b a) = true)
    {l₁ l₂ : List α} (hp : l₁.Perm l₂)
    (hanti : ∀ a ∈ l₁, ∀ b ∈ l₁, le a b = true → le b a = true → a = b) :
    l₁.mergeSort le = l₂.mergeSort le := by
  refine eq_of_perm_of_pairwise
    (((List.mergeSort_perm l₁ le).trans hp).trans (List.mergeSort_perm l₂ le).symm)
    (List.pairwise_mergeSort htrans htotal l₁)
    (List.pairwise_mergeSort htrans htotal l₂) ?_
  intro a ha b hb hab hba
  exact hanti a ((List.mergeSort_perm l₁ le).mem_iff.mp ha) b
    ((List.mergeSort_perm l₁ le).mem_iff.mp hb) hab hba

/-- **The machine's `sortSlice`, at one int kind.** The loaded elements
of an integer slice all carry the same `IntKind`, so the machine's
comparison `fun a b => a.1 ≤ b.1` is antisymmetric on them and the sort
is order-blind: any two permutations sort to the same list. -/
theorem mergeSort_intKind_eq_of_perm {l₁ l₂ : List (Int × IntKind)}
    (hp : l₁.Perm l₂) (hkind : ∀ x ∈ l₁, ∀ y ∈ l₁, x.2 = y.2) :
    l₁.mergeSort (fun a b => decide (a.1 ≤ b.1))
      = l₂.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
  refine mergeSort_eq_of_perm (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega)
    hp ?_
  intro a ha b hb hab hba
  simp only [decide_eq_true_eq] at hab hba
  have h1 : a.1 = b.1 := by omega
  have h2 : a.2 = b.2 := hkind a ha b hb
  exact Prod.ext h1 h2

end GoLean.Iris
