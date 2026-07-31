import GoLeanProofs.Specs.QuorumTargets

/-!
# The quorum reference meets the declarative spec (target discharged)

`QuorumTargets.lean` pins the phase-0 statement
`committedIndexRef_meets_spec_statement`: the executable reference
(`committedIndexRef`, etcd's `majority.go` shape — insertion-sort the
acked-or-zero indexes ascending, read position `n - (n/2+1)`) satisfies
the declarative spec `IsCommittedIndex` (committedness + maximality +
the empty-config convention).

This file discharges it. Everything here is plain Lean over lists and
naturals: no Iris, no machine semantics.

Structure:

1. **Sort invariants** for the hand-rolled `insertAsc`/`sortAsc`:
   permutation (`sortAsc_perm`) and sortedness (`sortAsc_sorted`, as
   `List.Pairwise (· ≤ ·)`). Both by the obvious inductions; core's
   `mergeSort` lemmas do not apply because the reference deliberately
   hand-rolls the sort so instances compute by `rfl`.
2. **The counting bridge** `supporters_eq_countP`: `supporters` (a
   `filter`+`length` over the *config*) equals `countP (j ≤ ·)` over the
   *sorted acked multiset*, via `countP_eq_length_filter`, `countP_map`
   and `Perm.countP_eq`. Note this needs no distinctness of voters —
   which is why the `Nodup` hypothesis of the pinned target turns out to
   be unnecessary (see `committedIndexRef_meets_spec_of_any`).
3. **Two sorted-list counting lemmas** (`sorted_countP_ge`,
   `sorted_countP_lt`): in a sorted list, the count of elements `≥ j`
   is at least `length - k` when `j ≤ s[k]`, and at most
   `length - k - 1` when `s[k] < j`. Instantiated at
   `k = n - (n/2+1)` these are exactly committedness and maximality.
-/

namespace GoLean.Quorum

/-! ## 1. Invariants of the hand-rolled insertion sort -/

/-- `insertAsc` inserts: the result is a permutation of `x :: l`. -/
theorem insertAsc_perm (x : Nat) : ∀ l : List Nat, (insertAsc x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
      by_cases h : x ≤ y
      · simp only [insertAsc, if_pos h]
        exact List.Perm.refl _
      · simp only [insertAsc, if_neg h]
        exact ((insertAsc_perm x ys).cons y).trans (List.Perm.swap x y ys)

/-- `sortAsc` is a permutation of its input. -/
theorem sortAsc_perm : ∀ l : List Nat, (sortAsc l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertAsc_perm x (sortAsc xs)).trans ((sortAsc_perm xs).cons x)

@[simp] theorem sortAsc_length (l : List Nat) : (sortAsc l).length = l.length :=
  (sortAsc_perm l).length_eq

theorem mem_insertAsc {x a : Nat} {l : List Nat} :
    a ∈ insertAsc x l ↔ a = x ∨ a ∈ l := by
  rw [(insertAsc_perm x l).mem_iff, List.mem_cons]

/-- `insertAsc` preserves ascending sortedness. -/
theorem insertAsc_sorted (x : Nat) :
    ∀ {l : List Nat}, l.Pairwise (· ≤ ·) → (insertAsc x l).Pairwise (· ≤ ·)
  | [], _ => by simp [insertAsc]
  | y :: ys, h => by
      rw [List.pairwise_cons] at h
      by_cases hxy : x ≤ y
      · simp only [insertAsc, if_pos hxy]
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hxy
        · exact Nat.le_trans hxy (h.1 b hb)
      · simp only [insertAsc, if_neg hxy]
        refine List.pairwise_cons.2 ⟨?_, insertAsc_sorted x h.2⟩
        intro b hb
        rcases mem_insertAsc.1 hb with rfl | hb
        · omega
        · exact h.1 b hb

/-- `sortAsc` sorts: the result is ascending. -/
theorem sortAsc_sorted : ∀ l : List Nat, (sortAsc l).Pairwise (· ≤ ·)
  | [] => by simp [sortAsc]
  | x :: xs => insertAsc_sorted x (sortAsc_sorted xs)

/-! ## 2. The counting bridge -/

/-- `supporters` — a `filter`/`length` over the *config* — is the count
of acked-or-zero values `≥ j` in the *sorted* acked multiset. No
distinctness of voters is used: `countP` counts occurrences, and both
`map` and the sort preserve them. -/
theorem supporters_eq_countP (c : List Nat) (acked : Nat → Option Nat) (j : Nat) :
    supporters c acked j
      = (sortAsc (c.map (ackedOrZero acked))).countP (fun x => decide (j ≤ x)) := by
  rw [supporters, ← List.countP_eq_length_filter,
    List.Perm.countP_eq _ (sortAsc_perm (c.map (ackedOrZero acked))), List.countP_map]
  rfl

/-! ## 3. Counting `≥ j` in a sorted list, relative to a position -/

/-- In an ascending list, if the element at position `k` is `≥ j`, then
so is every element from `k` on: at least `length - k` elements are
`≥ j`. -/
theorem sorted_countP_ge (j : Nat) :
    ∀ (s : List Nat) (k : Nat), s.Pairwise (· ≤ ·) → ∀ (hk : k < s.length),
      j ≤ s[k] → s.length - k ≤ s.countP (fun x => decide (j ≤ x))
  | [], _, _, hk, _ => absurd hk (by simp)
  | x :: t, 0, hp, _, hj => by
      rw [List.getElem_cons_zero] at hj
      have hall : ∀ a ∈ t, decide (j ≤ a) = true := by
        intro a ha
        have hxa : x ≤ a := (List.pairwise_cons.1 hp).1 a ha
        simp only [decide_eq_true_eq]
        omega
      have ht : t.countP (fun x => decide (j ≤ x)) = t.length :=
        List.countP_eq_length.2 hall
      rw [List.countP_cons_of_pos (by simp only [decide_eq_true_eq]; omega), ht]
      simp only [List.length_cons]
      omega
  | x :: t, k + 1, hp, hk, hj => by
      rw [List.getElem_cons_succ] at hj
      have hk' : k < t.length := by simpa using hk
      have ih := sorted_countP_ge j t k (List.pairwise_cons.1 hp).2 hk' hj
      have hmono : t.countP (fun x => decide (j ≤ x))
          ≤ (x :: t).countP (fun x => decide (j ≤ x)) := by
        rw [List.countP_cons]
        exact Nat.le_add_right _ _
      simp only [List.length_cons]
      omega

/-- In an ascending list, if the element at position `k` is `< j`, then
every element `≥ j` sits strictly after `k`: at most `length - k - 1`
elements are `≥ j`. -/
theorem sorted_countP_lt (j : Nat) :
    ∀ (s : List Nat) (k : Nat), s.Pairwise (· ≤ ·) → ∀ (hk : k < s.length),
      s[k] < j → s.countP (fun x => decide (j ≤ x)) ≤ s.length - k - 1
  | [], _, _, hk, _ => absurd hk (by simp)
  | x :: t, 0, _, _, hj => by
      rw [List.getElem_cons_zero] at hj
      rw [List.countP_cons_of_neg (by simp only [decide_eq_true_eq]; omega)]
      have hle := List.countP_le_length (p := fun x => decide (j ≤ x)) (l := t)
      simp only [List.length_cons]
      omega
  | x :: t, k + 1, hp, hk, hj => by
      rw [List.getElem_cons_succ] at hj
      have hk' : k < t.length := by simpa using hk
      have hxt : x ≤ t[k] := (List.pairwise_cons.1 hp).1 _ (List.getElem_mem hk')
      have ih := sorted_countP_lt j t k (List.pairwise_cons.1 hp).2 hk' hj
      rw [List.countP_cons_of_neg (by simp only [decide_eq_true_eq]; omega)]
      simp only [List.length_cons]
      omega

/-! ## 4. The target -/

/-- **The agreement theorem, in its strongest form**: the executable
reference meets the declarative spec for *every* config — no
duplicate-freeness required. `supporters` is a count, not a set
cardinality, so repeated voters simply count repeatedly on both sides of
the bridge. -/
theorem committedIndexRef_meets_spec_of_any (c : List Nat) (acked : Nat → Option Nat) :
    IsCommittedIndex c acked (committedIndexRef c acked) := by
  cases c with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons v vs =>
    have hslen : (sortAsc ((v :: vs).map (ackedOrZero acked))).length = (v :: vs).length := by
      simp
    have hk : (v :: vs).length - quorumSize (v :: vs).length
        < (sortAsc ((v :: vs).map (ackedOrZero acked))).length := by
      rw [hslen]
      simp only [List.length_cons, quorumSize]
      omega
    have hr : committedIndexRef (v :: vs) acked
        = (sortAsc ((v :: vs).map (ackedOrZero acked)))[(v :: vs).length -
            quorumSize (v :: vs).length]'hk := by
      rw [List.getElem_eq_getD 0]
      rfl
    refine Or.inr ⟨by simp, ?_, ?_⟩
    · -- committedness: the top `n/2+1` elements of the sorted multiset are all ≥ r
      rw [supporters_eq_countP, hr]
      have h2 := sorted_countP_ge
        ((sortAsc ((v :: vs).map (ackedOrZero acked)))[(v :: vs).length -
          quorumSize (v :: vs).length]'hk)
        (sortAsc ((v :: vs).map (ackedOrZero acked)))
        ((v :: vs).length - quorumSize (v :: vs).length)
        (sortAsc_sorted _) hk (Nat.le_refl _)
      rw [hslen] at h2
      simp only [List.length_cons, quorumSize] at h2 ⊢
      omega
    · -- maximality: anything above r lives strictly after position n-(n/2+1)
      intro j hj
      rw [supporters_eq_countP]
      rw [hr] at hj
      have h2 := sorted_countP_lt j (sortAsc ((v :: vs).map (ackedOrZero acked)))
        ((v :: vs).length - quorumSize (v :: vs).length) (sortAsc_sorted _) hk hj
      rw [hslen] at h2
      simp only [List.length_cons, quorumSize] at h2 ⊢
      omega

/-- **The pinned target, discharged** (`QuorumTargets.lean` phase-0
statement): `committedIndexRef` meets `IsCommittedIndex` for every
duplicate-free config. Immediate from the `Nodup`-free form above; the
hypothesis is retained because the target statement is the pinned
interface. -/
theorem committedIndexRef_meets_spec : committedIndexRef_meets_spec_statement :=
  fun c acked _ => committedIndexRef_meets_spec_of_any c acked

/-! ## 5. Uniqueness — the spec is a CHARACTERIZATION, mechanized

`IsCommittedIndex`'s docstring asserted "it determines `r` uniquely".
That is what upgrades `quorumOneKnownMeetsSpec` from "the machine's
answer *is* a committed index" to "the machine computes Go's
`CommittedIndex`" — and it was prose, proven nowhere (pre-merge audit
2026-07-31, finding 5). It is mechanized here rather than softened,
because it is true and cheap: maximality at each of two witnesses
refutes the other being larger. -/

/-- **Uniqueness**: at most one `r` satisfies the spec for a given
config and acked data. -/
theorem isCommittedIndex_unique {c : List Nat} {acked : Nat → Option Nat}
    {r₁ r₂ : Nat} (h₁ : IsCommittedIndex c acked r₁)
    (h₂ : IsCommittedIndex c acked r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨hc₁, hr₁⟩ | ⟨hne₁, hsup₁, hmax₁⟩
  · rcases h₂ with ⟨_, hr₂⟩ | ⟨hne₂, _, _⟩
    · omega
    · exact absurd hc₁ hne₂
  · rcases h₂ with ⟨hc₂, _⟩ | ⟨_, hsup₂, hmax₂⟩
    · exact absurd hc₂ hne₁
    · rcases Nat.lt_trichotomy r₁ r₂ with hlt | heq | hgt
      · exact absurd hsup₂ (Nat.not_le.mpr (hmax₁ r₂ hlt))
      · exact heq
      · exact absurd hsup₁ (Nat.not_le.mpr (hmax₂ r₁ hgt))

/-- **The characterization**: `IsCommittedIndex` holds of exactly the
reference's answer. Existence is `committedIndexRef_meets_spec_of_any`,
uniqueness is the theorem above — together they say the declarative spec
and `majority.go`'s algorithm define the SAME function, so reading
"`r` is a committed index" as "`r` is what Go computes" is now a
theorem rather than a docstring. -/
theorem isCommittedIndex_iff (c : List Nat) (acked : Nat → Option Nat) (r : Nat) :
    IsCommittedIndex c acked r ↔ r = committedIndexRef c acked :=
  ⟨fun h => isCommittedIndex_unique h (committedIndexRef_meets_spec_of_any c acked),
   fun h => h ▸ committedIndexRef_meets_spec_of_any c acked⟩

end GoLean.Quorum

/-! ## Axiom pin

Strictly inside the allowlist `[propext, Classical.choice, Quot.sound]` —
the proof is classical-choice-free (`Classical.choice` is not used;
`Quot.sound` enters only through `List.Perm`/`omega` plumbing). No
`sorry`, no `native_decide`, no new axioms. -/

/-- info: 'GoLean.Quorum.committedIndexRef_meets_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GoLean.Quorum.committedIndexRef_meets_spec

/-- info: 'GoLean.Quorum.committedIndexRef_meets_spec_of_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GoLean.Quorum.committedIndexRef_meets_spec_of_any
