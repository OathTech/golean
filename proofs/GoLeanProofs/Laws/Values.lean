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
4. **The machine's bounded loops and its `slices.Sort` transition at a
   SYMBOLIC length** (`forIn_range'_inv`, `applyStmtOp_sortSlice_ints`,
   `buildDefaultArrayValue_int`; proof-automation arc phase 4,
   2026-08-01). `applyStmtOp`'s wide ops are written as `for i in [:n]`
   loops over the machine state; at a LITERAL `n` `simp` unrolls them,
   at a symbolic one nothing does. `forIn_range'_inv` is the induction
   those loops need — a bounded `List.range'` fold with a
   step-indexed invariant, stated over an arbitrary monad-free `f` so
   the caller's actual loop body unifies with it — and
   `applyStmtOp_sortSlice_ints` is what it buys: `slices.Sort` over a
   slice of already-normalized ints replaces the visible slots by the
   sorted image and leaves the tail alone, for ANY length. The sort's
   ANSWER is a premise (`hsorted`), so the caller may characterize it
   however it likes; `mergeSort_pairs_eq_of_perm` is the usable form —
   any sorted permutation of the loaded values IS the machine's answer.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

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


/-! ### Sorted-permutation bridge for the machine's sort -/

/-- **Any sorted permutation IS the machine's sort answer.** The machine
mergeSorts `(Int × IntKind)` pairs by their `Int`; if `srt` is a sorted
permutation of the loaded values, the sort returns exactly `srt`'s image.
Target-free: no program, no config, no quorum value. -/
theorem mergeSort_pairs_eq_of_perm {kind : IntKind} {vals srt : List Int}
    (hp : vals.Perm srt) (hsorted : srt.Pairwise (· ≤ ·)) :
    (vals.map (fun v => (v, kind))).mergeSort (fun a b => decide (a.1 ≤ b.1))
      = srt.map (fun v => (v, kind)) := by
  have htrans : ∀ a b c : Int × IntKind,
      decide (a.1 ≤ b.1) = true → decide (b.1 ≤ c.1) = true → decide (a.1 ≤ c.1) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    omega
  have htotal : ∀ a b : Int × IntKind,
      (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  refine eq_of_perm_of_pairwise (le := fun a b => decide (a.1 ≤ b.1) = true)
    (((List.mergeSort_perm _ _).trans (hp.map _)))
    (List.pairwise_mergeSort htrans htotal _) ?_ ?_
  · rw [List.pairwise_map]
    exact hsorted.imp (by intro a b h; simpa using h)
  · intro a ha b hb hab hba
    simp only [decide_eq_true_eq] at hab hba
    have h1 : a.1 = b.1 := by omega
    have hka : a.2 = kind := by
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).mem_iff.mp ha)
      rfl
    have hkb : b.2 = kind := by
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).mem_iff.mp hb)
      rfl
    exact Prod.ext h1 (hka.trans hkb.symm)

/-- The `some` entries are no more numerous than the entries. -/
theorem reduceOption_length_le {α : Type _} :
    ∀ l : List (Option α), (l.reduceOption).length ≤ l.length
  | [] => Nat.le_refl _
  | none :: t => by
    have ih := reduceOption_length_le t
    have hcons : (none :: t).reduceOption = t.reduceOption := rfl
    rw [hcons, List.length_cons]; omega
  | some v :: t => by
    have ih := reduceOption_length_le t
    have hcons : (some v :: t).reduceOption = v :: t.reduceOption := rfl
    rw [hcons, List.length_cons, List.length_cons]; omega

/-- **Zeros for the missing entries.** A right-to-left fill writes only
the `some` entries and leaves the low slots zero, so the slots the sort
sees are the multiset of `getD 0`s. Target-free. -/
theorem perm_replicate_reduceOption (d : Int) :
    ∀ l : List (Option Int),
      (List.replicate (l.length - (l.reduceOption).length) d
        ++ l.reduceOption).Perm (l.map (fun o => o.getD d))
  | [] => List.Perm.refl _
  | none :: t => by
    have ih := perm_replicate_reduceOption d t
    have hle : (t.reduceOption).length ≤ t.length := reduceOption_length_le t
    have hcons : (none :: t).reduceOption = t.reduceOption := rfl
    rw [hcons, List.length_cons, List.map_cons,
      show t.length + 1 - (t.reduceOption).length
          = (t.length - (t.reduceOption).length) + 1 from by omega,
      List.replicate_succ, List.cons_append]
    exact ih.cons _
  | some v :: t => by
    have ih := perm_replicate_reduceOption d t
    have hcons : (some v :: t).reduceOption = v :: t.reduceOption := rfl
    rw [hcons, List.length_cons, List.map_cons, List.length_cons,
      show t.length + 1 - ((t.reduceOption).length + 1)
          = t.length - (t.reduceOption).length from by omega]
    exact (List.perm_middle).trans (ih.cons _)

/-- Membership in the reported values: a value that survives
`reduceOption ∘ map f` came from an element the map sends to `some`. -/
theorem mem_reduceOption_map {α β : Type _} {f : α → Option β} {b : β} :
    ∀ {l : List α}, b ∈ (l.map f).reduceOption → ∃ a ∈ l, f a = some b
  | [], h => by simp [List.reduceOption] at h
  | a :: t, h => by
    cases hfa : f a with
    | none =>
      have h' : b ∈ (t.map f).reduceOption := by
        rw [List.map_cons, hfa] at h
        exact h
      obtain ⟨x, hx, hfx⟩ := mem_reduceOption_map h'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩
    | some c =>
      have h' : b ∈ c :: (t.map f).reduceOption := by
        rw [List.map_cons, hfa] at h
        exact h
      rcases List.mem_cons.1 h' with rfl | h''
      · exact ⟨a, by simp, hfa⟩
      · obtain ⟨x, hx, hfx⟩ := mem_reduceOption_map h''
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Erasing a `none` leaves the `some`s alone — exactly, not just up to
permutation. -/
theorem reduceOption_eraseIdx_none {α : Type _} :
    ∀ (l : List (Option α)) (i : Nat), l[i]? = some none →
      (l.eraseIdx i).reduceOption = l.reduceOption
  | [], _, h => by simp at h
  | none :: _, 0, _ => rfl
  | some _ :: _, 0, h => by simp at h
  | a :: t, i + 1, h => by
    have ih := reduceOption_eraseIdx_none t i (by simpa using h)
    cases a with
    | none => exact ih
    | some v =>
      show v :: (t.eraseIdx i).reduceOption = v :: t.reduceOption
      rw [ih]

/-- **The multiset-conservation step for a PARTIAL acked map.** Erasing
position `i` (whose entry is `some v`) from the "still to come" list and
prepending `v` to the "already written" list preserves the total
multiset of reported values — the `List.Perm` the ∀-config voter loop's
invariant carries. -/
theorem perm_eraseIdx_reduceOption {α : Type _} (t : List α) :
    ∀ (l : List (Option α)) (i : Nat) (v : α), l[i]? = some (some v) →
      ((l.eraseIdx i).reduceOption ++ (v :: t)).Perm (l.reduceOption ++ t)
  | [], _, _, h => by simp at h
  | some w :: rest, 0, v, h => by
    have hw : w = v := by simpa using h
    subst hw
    show (rest.reduceOption ++ w :: t).Perm (w :: rest.reduceOption ++ t)
    rw [List.cons_append]
    exact List.perm_middle
  | none :: _, 0, _, h => by simp at h
  | a :: rest, i + 1, v, h => by
    have ih := perm_eraseIdx_reduceOption t rest i v (by simpa using h)
    cases a with
    | none => exact ih
    | some w =>
      show (w :: ((rest.eraseIdx i).reduceOption ++ (v :: t))).Perm
        (w :: (rest.reduceOption ++ t))
      exact ih.cons w

/-! ## 4. Bounded machine loops: `forIn` over `[:n]`, and `sortSlice`

The machine's wide statement ops (`sortSlice`, `makeSlice`'s default
array) are `for i in [:n]` loops in the `Except` monad. These are the
lemmas that let a walk pass through one at a SYMBOLIC `n`. Target-free:
no program, no lowering, no quorum value occurs. -/

theorem forIn_range'_yield {β ε : Type} {f : Nat → β → Except ε (ForInStep β)}
    {Q : Nat → β → Prop} {out : Nat → β → β} {N : Nat}
    (hstep : ∀ (i : Nat) (b : β), i < N → Q i b →
      f i b = .ok (.yield (out i b)) ∧ Q (i + 1) (out i b)) :
    ∀ (n j : Nat), j + n ≤ N → ∀ b : β, Q j b →
      ∃ b', forIn (List.range' j n 1) b f = .ok b' ∧ Q (j + n) b'
  | 0, j, _, b, hb => ⟨b, rfl, by simpa using hb⟩
  | n + 1, j, hjn, b, hb => by
    obtain ⟨hf, hQ⟩ := hstep j b (by omega) hb
    have ih := forIn_range'_yield hstep n (j + 1) (by omega) (out j b) hQ
    obtain ⟨b', hb', hQ'⟩ := ih
    refine ⟨b', ?_, by rw [show j + (n + 1) = j + 1 + n by omega]; exact hQ'⟩
    rw [show List.range' j (n + 1) 1 = j :: List.range' (j + 1) n 1 from rfl,
      List.forIn_cons, hf]
    simp only [Bind.bind, Except.bind]
    exact hb'

/-- Overwriting a location with the value it already holds is a no-op. -/
theorem heap_set_self_of_lookup {h : Heap} {l : Loc} {c : HeapCell}
    (hl : Heap.lookup h l = some c) : Heap.set h l c = h := by
  induction h with
  | nil => simp [Heap.lookup] at hl
  | cons p rest ih =>
    obtain ⟨loc, old⟩ := p
    simp only [Heap.lookup] at hl
    cases hb : (loc == l) with
    | true =>
      simp only [hb, if_true] at hl
      injection hl with hl
      simp [Heap.set, hb, hl]
    | false =>
      simp only [hb, Bool.false_eq_true, if_false] at hl
      simp only [Heap.set, hb, Bool.false_eq_true, if_false]
      exact congrArg _ (ih hl)

theorem forIn_range'_inv {β ε : Type} {f : Nat → β → Except ε (ForInStep β)}
    (Q : Nat → β → Prop) (out : Nat → β → β) {N n j : Nat} {b res : β}
    (hstep : ∀ (i : Nat) (b' : β), i < N → Q i b' →
      f i b' = .ok (.yield (out i b')) ∧ Q (i + 1) (out i b'))
    (hjn : j + n ≤ N) (hb : Q j b) (hdet : ∀ b', Q (j + n) b' → b' = res) :
    forIn (List.range' j n 1) b f = .ok res := by
  obtain ⟨b', hb', hQ'⟩ := forIn_range'_yield hstep n j hjn b hb
  rw [hb', hdet b' hQ']

/-- The slice index location of a slice over the whole backing array. -/
theorem sliceIndexLoc_prefix {sta : Addr} {n cap j : Nat} (hj : j < n) (hnc : n ≤ cap) :
    sliceIndexLoc ⟨some (.base sta), 0, n, cap⟩ (Int.ofNat j)
      = .ok (.index (.base sta) (Int.ofNat j)) := by
  simp only [sliceIndexLoc, validateSlice, if_neg (by omega : ¬ n > cap),
    Bind.bind, Except.bind, pure, Except.pure, Int.ofNat_eq_natCast]
  simp only [if_neg (by omega : ¬ ((j : Int) < 0)),
    Int.toNat_natCast, if_pos hj, Nat.zero_add]

/-- Splitting a mapped list at a position — the `middle` shape the
positional read/write laws want. -/
theorem list_map_split {α β : Type _} (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) :
    l.map f = (l.take i).map f ++ f (l[i]'h) :: (l.drop (i + 1)).map f := by
  have h1 : l.take i ++ l.drop i = l := List.take_append_drop i l
  have h2 : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons h
  calc l.map f = (l.take i ++ l.drop i).map f := by rw [h1]
    _ = (l.take i).map f ++ (l.drop i).map f := List.map_append ..
    _ = (l.take i).map f ++ f (l[i]'h) :: (l.drop (i + 1)).map f := by
        rw [h2, List.map_cons]

theorem length_take_of_le {α : Type _} {l : List α} {i : Nat} (h : i ≤ l.length) :
    (l.take i).length = i := by simp; omega

/-- A heap cell holding an array of `cap` ints of one kind. -/
def intArrayCell (cap : Nat) (kind : IntKind) (l : List GoValue) : HeapCell :=
  ⟨some (.array cap (.int kind)), .array l.toArray⟩

/-- The int list as machine values. -/
def intVals (kind : IntKind) (l : List Int) : List GoValue :=
  l.map (fun v => .int v kind)

/-- The backing array's contents when the sort has written back its first
`i` slots: the sorted prefix, then the still-unwritten original suffix,
then the untouched tail. -/
def sortStage (kind : IntKind) (sorted vals : List Int) (tail : List GoValue)
    (i : Nat) : List GoValue :=
  intVals kind (sorted.take i) ++ (intVals kind (vals.drop i) ++ tail)

/-- ... and the state that array sits in, mid-writeback. -/
def sortStageState (σ : ExecState) (sta : Addr) (cap : Nat) (kind : IntKind)
    (sorted vals : List Int) (tail : List GoValue) (i : Nat) : ExecState :=
  { σ with
    heap := Heap.set σ.heap (.base sta)
      (intArrayCell cap kind (sortStage kind sorted vals tail i)) }

end GoLean.Iris
