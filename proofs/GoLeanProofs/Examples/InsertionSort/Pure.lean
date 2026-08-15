import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.StepKit

/-!
# InsertionSort — Pure

Per-phase shard of `GoLeanProofs.Examples.InsertionSort` (examples
phase-2 slice 0, lever 2, 2026-08-14). Every statement and proof here
is BYTE-IDENTICAL to the pre-split module; only file placement changed,
so Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.InsertionSort`, whose docstring records the
example's design and the shard map.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The program-side statement vocabulary -/

/-- The swap block: `{ s[j-1], s[j] = s[j], s[j-1] }`. -/
abbrev isortSwapBlock : Stmt :=
  .block #[]
    #[.seqn
        #[.assignMany
            #[.addr (.indexAddr (.var "s")
                (.sub (.var "j") (.intLit 1 .int))),
              .addr (.indexAddr (.var "s") (.var "j"))]
            #[.indexGet (.var "s") (.var "j"),
              .indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int))]]]

/-- The inner `for`'s condition: Go's SHORT-CIRCUIT
`j > 0 && s[j-1] > s[j]`. -/
abbrev innerCond : Expr :=
  .and (.greaterCmp (.var "j") (.intLit 0 .int))
    (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "j") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "j")))

/-- The inner `for`-desugar body (its own `$forFirst`, SHADOWING the
outer one — the env carries both at different scopes). -/
abbrev innerWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j") (.sub (.var "j") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse innerCond (.seqn #[]) .breakStmt,
      isortSwapBlock]

/-- The inner `for` statement as lowered (declaration block for `j`,
then the `$forFirst` block around the while). -/
abbrev innerForBlock : Stmt :=
  .block #[]
    #[.block #[]
        #[.seqn
            #[.initialization { id := "j", typ := .int .int },
              .assign (.var "j") (.var "i")],
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) innerWhileBody]]]

/-- The outer `for`-desugar body: dispatch, exit test `i < len(s)`,
then the whole inner `for`. -/
abbrev outerWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i")
          (.length (.var "s") (some (.slice (.int .uint64)))))
        (.seqn #[]) .breakStmt,
      innerForBlock]

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def isortFunc : Func :=
  { id := { key := "insertionSort" },
    args := #[{ id := "s", typ := .slice (.int .uint64) }],
    results := #[],
    body := .block #[]
      #[.block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 1 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) outerWhileBody]]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? isortLowered.funcs ⟨"insertionSort"⟩ = some isortFunc :=
  rfl

/-- The driver: `insertionSort(s)` with the slice handle over the
backing array at `base` as the literal argument. -/
def isortCall (xs : List Int) (base : Nat) : Stmt :=
  .call #[] ⟨"insertionSort"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit xs.length .int) none]

/-- The framed seed: input backing cell at `base`, arbitrary frame
`fr`, allocator at `na`. Canonical placement: `isortSeed xs 0 [] 1`. -/
def isortSeed (xs : List Int) (base : Nat) (fr : Heap) (na : Nat) :
    ExecState :=
  { types := isortLowered.typeDefs.toList,
    functions := isortLowered.funcs,
    methods := isortLowered.methods,
    heap := sliceCells xs base ++ fr, nextAddr := na }

/-! ## The pure spec layer -/

/-- Insert `v` into a (sorted) list, AFTER all elements ≤ v (Go's
strict-`>` swap keeps equal elements in place — stability). -/
def insertSpec (v : Int) : List Int → List Int
  | [] => [v]
  | w :: rest => if w ≤ v then w :: insertSpec v rest else v :: w :: rest

/-- Insertion sort: fold the input left-to-right into a sorted prefix. -/
def sortSpec (xs : List Int) : List Int :=
  xs.foldl (fun acc v => insertSpec v acc) []

private theorem mem_insertSpec {v x : Int} {p : List Int}
    (h : x ∈ insertSpec v p) : x = v ∨ x ∈ p := by
  induction p with
  | nil =>
      simp only [insertSpec, List.mem_singleton] at h
      exact .inl h
  | cons w rest ih =>
      simp only [insertSpec] at h
      split at h
      · rw [List.mem_cons] at h
        rcases h with h | h
        · exact .inr (by simp [h])
        · rcases ih h with h | h
          · exact .inl h
          · exact .inr (by simp [h])
      · rw [List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · exact .inr h

private theorem insertSpec_length (v : Int) (p : List Int) :
    (insertSpec v p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons w rest ih =>
      simp only [insertSpec]
      split <;> simp [ih]

private theorem insertSpec_pairwise {v : Int} {p : List Int}
    (h : p.Pairwise (· ≤ ·)) : (insertSpec v p).Pairwise (· ≤ ·) := by
  induction p with
  | nil => simp [insertSpec]
  | cons w rest ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hw, hrest⟩ := h
      simp only [insertSpec]
      split
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, ih hrest⟩
        rcases mem_insertSpec hx with rfl | hx
        · assumption
        · exact hw x hx
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, by rw [List.pairwise_cons]; exact ⟨hw, hrest⟩⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact Int.le_trans (by omega) (hw x hx)

private theorem insertSpec_count (v w : Int) (p : List Int) :
    (insertSpec v p).count w = p.count w + (if v = w then 1 else 0) := by
  induction p with
  | nil => simp [insertSpec, List.count_cons, beq_iff_eq]
  | cons u rest ih =>
      simp only [insertSpec]
      split
      · rw [List.count_cons, ih, List.count_cons]
        omega
      · simp only [List.count_cons, beq_iff_eq]

private theorem sortSpec_go_length (xs acc : List Int) :
    (xs.foldl (fun acc v => insertSpec v acc) acc).length
      = acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons, ih, insertSpec_length, List.length_cons]
      omega

/-- `sortSpec` preserves length. -/
theorem sortSpec_length (xs : List Int) : (sortSpec xs).length = xs.length := by
  simpa [sortSpec] using sortSpec_go_length xs []

private theorem sortSpec_go_count (xs acc : List Int) (w : Int) :
    (xs.foldl (fun acc v => insertSpec v acc) acc).count w
      = acc.count w + xs.count w := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons, ih, insertSpec_count, List.count_cons,
        beq_iff_eq]
      split <;> omega

/-- `sortSpec` is a permutation, stated first-order: every value's
multiplicity is preserved. -/
theorem sortSpec_count (xs : List Int) (v : Int) :
    (sortSpec xs).count v = xs.count v := by
  simpa [sortSpec] using sortSpec_go_count xs [] v

private theorem sortSpec_go_pairwise (xs acc : List Int)
    (h : acc.Pairwise (· ≤ ·)) :
    (xs.foldl (fun acc v => insertSpec v acc) acc).Pairwise (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => simpa
  | cons x rest ih => exact ih _ (insertSpec_pairwise h)

private theorem sorted_of_pairwise {l : List Int}
    (h : l.Pairwise (· ≤ ·)) : Sorted l := by
  intro i j hij hj
  rw [List.pairwise_iff_getElem] at h
  have := h i j (by omega) hj hij
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : i < l.length),
    List.getElem?_eq_getElem hj]
  simpa using this

/-- `sortSpec` sorts (the shared gallery `Sorted` — one definition,
`GoLean.SliceMem.Sorted`). -/
theorem sortSpec_sorted (xs : List Int) : Sorted (sortSpec xs) :=
  sorted_of_pairwise (sortSpec_go_pairwise xs [] (by simp))

/-- Membership transport (for the uint64 range hypotheses). -/
theorem mem_sortSpec {x : Int} {xs : List Int}
    (h : x ∈ sortSpec xs) : x ∈ xs := by
  have h1 : 0 < (sortSpec xs).count x := List.count_pos_iff.mpr h
  rw [sortSpec_count] at h1
  exact List.count_pos_iff.mp h1

/-! ### sortPrefix: the outer-loop invariant's list -/

/-- The backing list after `k` elements are folded in: sorted prefix,
untouched suffix. -/
def sortPrefix (xs : List Int) (k : Nat) : List Int :=
  sortSpec (xs.take k) ++ xs.drop k

theorem sortPrefix_one (xs : List Int) : sortPrefix xs 1 = xs := by
  cases xs with
  | nil => rfl
  | cons x rest => simp [sortPrefix, sortSpec, insertSpec, List.take_succ_cons,
      List.drop_succ_cons]

theorem sortPrefix_full {xs : List Int} {k : Nat}
    (h : xs.length ≤ k) : sortPrefix xs k = sortSpec xs := by
  rw [sortPrefix, List.take_of_length_le h, List.drop_of_length_le h,
    List.append_nil]

/-- The fold step: the next element inserts into the sorted prefix. -/
theorem sortSpec_take_succ {xs : List Int} {k : Nat}
    (h : k < xs.length) :
    sortSpec (xs.take (k + 1))
      = insertSpec (xs.getD k 0) (sortSpec (xs.take k)) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  show sortSpec (xs.take k ++ [xs[k]]) = _
  rw [sortSpec, List.foldl_append]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem sortPrefix_decomp {xs : List Int} {k : Nat}
    (h : k < xs.length) :
    sortPrefix xs k = sortSpec (xs.take k) ++ xs.getD k 0 :: xs.drop (k + 1) := by
  rw [sortPrefix, List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

/-! ### bubbleState: the inner-loop invariant's prefix -/

/-- The sorted prefix `p` (length i) with `v` being bubbled down: `v`
currently sits at position `j`; the elements formerly at `j..i-1` are
shifted up by one. -/
def bubbleState (p : List Int) (v : Int) (j : Nat) : List Int :=
  p.take j ++ v :: p.drop j

theorem bubbleState_length {p : List Int} {v : Int} {j : Nat}
    (h : j ≤ p.length) :
    (bubbleState p v j).length = p.length + 1 := by
  simp [bubbleState]
  omega

theorem bubbleState_full (p : List Int) (v : Int) :
    bubbleState p v p.length = p ++ [v] := by
  simp [bubbleState]

private theorem bubbleState_getElem?_lt {p : List Int} {v : Int} {j k : Nat}
    (hk : k < j) (hj : j ≤ p.length) :
    (bubbleState p v j)[k]? = p[k]? := by
  rw [bubbleState, List.getElem?_append_left (by simp; omega),
    List.getElem?_take_of_lt hk]

private theorem bubbleState_getElem?_eq {p : List Int} {v : Int} {j : Nat}
    (hj : j ≤ p.length) :
    (bubbleState p v j)[j]? = some v := by
  rw [bubbleState, List.getElem?_append_right (by simp; omega)]
  simp [List.length_take, Nat.min_eq_left hj]

private theorem bubbleState_getElem?_gt {p : List Int} {v : Int} {j k : Nat}
    (hk : j < k) (hj : j ≤ p.length) :
    (bubbleState p v j)[k]? = p[k - 1]? := by
  rw [bubbleState, List.getElem?_append_right (by simp; omega)]
  rw [List.length_take, Nat.min_eq_left hj]
  cases hkk : k - j with
  | zero => omega
  | succ d =>
      simp only [List.getElem?_cons_succ, List.getElem?_drop]
      congr 1
      omega

theorem bubbleState_getD_lt {p : List Int} {v : Int} {j k : Nat}
    (hk : k < j) (hj : j ≤ p.length) :
    (bubbleState p v j).getD k 0 = p.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    bubbleState_getElem?_lt hk hj]

theorem bubbleState_getD_eq {p : List Int} {v : Int} {j : Nat}
    (hj : j ≤ p.length) :
    (bubbleState p v j).getD j 0 = v := by
  rw [List.getD_eq_getElem?_getD, bubbleState_getElem?_eq hj]
  rfl

/-- Membership transport for bubbleState. -/
theorem mem_bubbleState {p : List Int} {v x : Int} {j : Nat}
    (h : x ∈ bubbleState p v j) : x = v ∨ x ∈ p := by
  simp only [bubbleState, List.mem_append, List.mem_cons] at h
  rcases h with h | h | h
  · exact .inr (List.mem_of_mem_take h)
  · exact .inl h
  · exact .inr (List.mem_of_mem_drop h)

/-- **One machine swap advances the bubble**: writing `v` at `j-1` and
the old `p[j-1]` at `j` is exactly the bubble at `j-1` (the machine's
store order: `s[j-1] := s[j]` then `s[j] := old s[j-1]`). -/
theorem bubbleState_swap {p : List Int} {v : Int} {j : Nat}
    (h1 : 1 ≤ j) (hj : j ≤ p.length) :
    ((bubbleState p v j).set (j - 1) v).set j (p.getD (j - 1) 0)
      = bubbleState p v (j - 1) := by
  have hgetd : p[j - 1]? = some (p.getD (j - 1) 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  apply List.ext_getElem?
  intro k
  by_cases hk : k < p.length + 1
  · rw [List.getElem?_set, List.getElem?_set]
    simp only [List.length_set, bubbleState_length hj]
    by_cases hkj : j = k
    · subst hkj
      rw [if_pos rfl, if_pos (by omega),
        bubbleState_getElem?_gt (by omega) (by omega), hgetd]
    · rw [if_neg hkj]
      by_cases hkj1 : j - 1 = k
      · subst hkj1
        rw [if_pos rfl, if_pos (by omega),
          bubbleState_getElem?_eq (by omega)]
      · rw [if_neg hkj1]
        by_cases hlt : k < j - 1
        · rw [bubbleState_getElem?_lt hlt (by omega),
            bubbleState_getElem?_lt (by omega) hj]
        · rw [bubbleState_getElem?_gt (by omega) hj,
            bubbleState_getElem?_gt (by omega) (by omega)]
  · rw [List.getElem?_eq_none (by simp [List.length_set, bubbleState_length hj]; omega),
      List.getElem?_eq_none (by simp [bubbleState_length (by omega : j - 1 ≤ p.length)]; omega)]

/-- **At the inner exit the bubble IS the insertion**: once `j = 0` or
`p[j-1] ≤ v`, with everything from `j` up strictly greater than `v`,
the bubble equals `insertSpec v p`. -/
theorem bubbleState_exit {p : List Int} {v : Int} {j : Nat}
    (hsort : Sorted p) (hj : j ≤ p.length)
    (hstop : j = 0 ∨ p.getD (j - 1) 0 ≤ v)
    (hgt : ∀ k, j ≤ k → k < p.length → v < p.getD k 0) :
    bubbleState p v j = insertSpec v p := by
  induction p generalizing j with
  | nil =>
      have : j = 0 := by simpa using hj
      subst this
      rfl
  | cons w rest ih =>
      cases j with
      | zero =>
          have hvw : v < w := by
            have := hgt 0 (by omega) (by simp)
            simpa using this
          simp only [bubbleState, List.drop_zero, insertSpec,
            List.take_zero, List.nil_append]
          rw [if_neg (by omega)]
      | succ jj =>
          have hwv : w ≤ v := by
            rcases hstop with h | h
            · omega
            · calc w = (w :: rest).getD 0 0 := rfl
                _ ≤ (w :: rest).getD jj 0 := by
                    cases Nat.eq_zero_or_pos jj with
                    | inl hz => rw [hz]; exact Int.le_refl _
                    | inr hpos => exact hsort 0 jj hpos (by simp at hj ⊢; omega)
                _ ≤ v := by simpa using h
          have htail : Sorted rest := by
            intro a b hab hb
            have := hsort (a + 1) (b + 1) (by omega) (by simp; omega)
            simpa using this
          show w :: bubbleState rest v jj = insertSpec v (w :: rest)
          rw [insertSpec, if_pos hwv]
          congr 1
          refine ih htail (by simpa using hj) ?_ ?_
          · rcases hstop with h | h
            · omega
            · cases jj with
              | zero => exact .inl rfl
              | succ j2 =>
                  right
                  simpa using h
          · intro k hk hk'
            have := hgt (k + 1) (by omega) (by simpa using Nat.succ_lt_succ hk')
            simpa using this

/-- Set distributes over the append at in-prefix positions (the machine
stores on the FULL backing list). -/
theorem set_append_left {l1 l2 : List Int} {k : Nat} {x : Int}
    (h : k < l1.length) : (l1 ++ l2).set k x = l1.set k x ++ l2 := by
  induction l1 generalizing k with
  | nil => simp at h
  | cons a rest ih =>
      cases k with
      | zero => rfl
      | succ kk =>
          simp only [List.cons_append, List.set_cons_succ]
          rw [ih (by simpa using h)]


end GoLean.Examples.InsertionSort
