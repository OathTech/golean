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
distinctness of voters is used: `countP` counts occurrences, and the
`map`+`sort` preserve them. -/
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
      rw [List.countP_cons_of_pos _ (by simpa using hj), ht]
      simp
  | x :: t, k + 1, hp, hk, hj => by
      rw [List.getElem_cons_succ] at hj
      have hk' : k < t.length := by simpa using hk
      have ih := sorted_countP_ge j t k (List.pairwise_cons.1 hp).2 hk' hj
      have hmono : t.countP (fun x => decide (j ≤ x))
          ≤ (x :: t).countP (fun x => decide (j ≤ x)) := by
        rw [List.countP_cons]
        omega
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
      rw [List.countP_cons_of_neg _ (by simp; omega)]
      have := List.countP_le_length (p := fun x => decide (j ≤ x)) (l := t)
      simp only [List.length_cons]
      omega
  | x :: t, k + 1, hp, hk, hj => by
      rw [List.getElem_cons_succ] at hj
      have hk' : k < t.length := by simpa using hk
      have hxt : x ≤ t[k] := (List.pairwise_cons.1 hp).1 _ (List.getElem_mem hk')
      have ih := sorted_countP_lt j t k (List.pairwise_cons.1 hp).2 hk' hj
      rw [List.countP_cons_of_neg _ (by simp; omega)]
      simp only [List.length_cons]
      omega

/-! ## 4. The target -/

/-- **The agreement theorem, in its strongest form**: the executable
reference meets the declarative spec for *every* config — no
duplicate-freeness required. `supporters` is a count, not a set
cardinality, so repeated voters simply count repeatedly on both sides. -/
theorem committedIndexRef_meets_spec_of_any (c : List Nat) (acked : Nat → Option Nat) :
    IsCommittedIndex c acked (committedIndexRef c acked) := by
  match c with
  | [] => exact Or.inl ⟨rfl, rfl⟩
  | v :: vs =>
    set n := (v :: vs).length with hn
    set s := sortAsc ((v :: vs).map (ackedOrZero acked)) with hs
    have hslen : s.length = n := by simp [hs, hn]
    have hnpos : 0 < n := by simp [hn]
    have hk : n - quorumSize n < s.length := by
      rw [hslen, quorumSize]; omega
    have hr : committedIndexRef (v :: vs) acked = s[n - quorumSize n] := by
      rw [List.getElem_eq_getD 0]
      rfl
    refine Or.inr ⟨by simp, ?_, ?_⟩
    · rw [supporters_eq_countP, ← hs, hr]
      have := sorted_countP_ge s[n - quorumSize n] s (n - quorumSize n)
        (hs ▸ sortAsc_sorted _) hk (Nat.le_refl _)
      rw [hslen] at this
      rw [quorumSize] at this ⊢
      omega
    · intro j hj
      rw [supporters_eq_countP, ← hs]
      rw [hr] at hj
      have := sorted_countP_lt j s (n - quorumSize n) (hs ▸ sortAsc_sorted _) hk hj
      rw [hslen] at this
      rw [quorumSize] at this ⊢
      omega

/-- **The pinned target, discharged** (`QuorumTargets.lean` phase-0
statement): `committedIndexRef` meets `IsCommittedIndex` for every
duplicate-free config. Immediate from the `Nodup`-free form above; the
hypothesis is retained because the target statement is the pinned
interface. -/
theorem committedIndexRef_meets_spec : committedIndexRef_meets_spec_statement :=
  fun c acked _ => committedIndexRef_meets_spec_of_any c acked

end GoLean.Quorum

/-- info: 'GoLean.Quorum.committedIndexRef_meets_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GoLean.Quorum.committedIndexRef_meets_spec
