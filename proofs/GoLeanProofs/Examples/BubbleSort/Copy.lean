import GoLeanProofs.Examples.BubbleSort.Setup

/-!
# BubbleSort — the `pre` copy loop

Split from `BubbleSort.Harness` (proof-cost shard split: the raw
`with_unfolding_all rfl` segments of the setup and copy phases
together peaked over the ~2.5 GiB bar; the phases are independent, so
they elaborate in separate workers). Content and statements unchanged.
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw run segments — the copy loop -/

theorem cp_A0_rawB (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ch : Choices) :
    stepFnIter 25 (σB (bHeapCp nv sv n l lp xv siv civ true) 13)
      cpHeadCfgB ch
      = .ok (.retV (.bool (decide (civ < nv))) cpCmpKB,
          σB (bHeapCp nv sv n l lp xv siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_A1_rawB (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ch : Choices) :
    stepFnIter 29 (σB (bHeapCp nv sv n l lp xv siv civ false) 13)
      cpHeadCfgB ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < nv))) cpCmpKB,
          σB (bHeapCp nv sv n l lp xv siv
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 13, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `pre[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp_B1_rawB (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ch : Choices) :
    stepFnIter 16 (σB (bHeapCp nv sv n l lp xv siv civ false) 13)
      (.retV (.bool true) cpCmpKB) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [bSliceS n] [] cpEnvB2 (cpRhsKB civ)),
          σB (bHeapCp nv sv n l lp xv siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_B2_rawB (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σB (bHeapCp nv sv n l lp xv siv civ false) 13)
      (.retV w (cpRhsKB civ)) ch
      = .ok (.next (.storeK [cpRefB civ] [w] (.seqn #[]) cpEnvB2
            cpStTailB),
          σB (bHeapCp nv sv n l lp xv siv civ false) 13, ch) := by
  with_unfolding_all rfl

theorem cp_D_rawB (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ch : Choices) :
    stepFnIter 5 (σB (bHeapCp nv sv n l lp xv siv civ false) 13)
      (.next (.storeK [] [] (.seqn #[]) cpEnvB2 cpStTailB)) ch
      = .ok (cpHeadCfgB, σB (bHeapCp nv sv n l lp xv siv civ false) 13,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → the `bubbleSort(s)` argument delivered at
the drained `callArgsK`. 9 steps (no result variable is declared —
the subject returns nothing). -/
theorem cp_X_rawB (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ch : Choices) :
    stepFnIter 9 (σB (bHeapCp nv sv n l lp xv siv civ false) 13)
      (.retV (.bool false) cpCmpKB) ch
      = .ok (.retV (bSliceS n) bCallArgsK,
          σB (bHeapCp nv sv n l lp xv siv civ false) 13, ch) := by
  with_unfolding_all rfl

/-! ## The setup loop, cleaned + its induction (the P5 schema) -/

/-- One setup iteration from the exit test's true delivery at `i`:
68 steps advance the family prefix and the LCG accumulator. -/
theorem su_iterB (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∀ i, i < n → ∀ ch : Choices,
    stepFnIter 68
      (σB (bHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (bubFam i seed ++ List.replicate (n - i) 0)
        (bubX i seed) ((i : Nat) : Int) false) 10)
      (.retV (.bool true) suCmpKB) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suCmpKB,
          σB (bHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (bubFam (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            (bubX (i + 1) seed) ((i + 1 : Nat) : Int) false) 10, ch) := by
  intro i hi ch
  have hB1 := su_B1_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam i seed ++ List.replicate (n - i) 0)
    (bubX i seed) ((i : Nat) : Int) ch
  rw [bubX_step_norm, bubX_succ] at hB1
  have hxlt : SortShared.lcgStep bubA bubB (i + 1) seed < 2 ^ 64 :=
    SortShared.lcgStep_lt (by omega)
  have hw : (0 : Int) ≤ bubX (i + 1) seed
      ∧ bubX (i + 1) seed < 2 ^ 64 := by
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast hxlt
  have hst := storeTarget_slice_u64
    (σ := σB (bHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (bubFam i seed ++ List.replicate (n - i) 0)
      (bubX (i + 1) seed) ((i : Nat) : Int) false) 10)
    (a := ⟨5⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := bubFam i seed ++ List.replicate (n - i) 0)
    (w := bubX (i + 1) seed)
    (lookup_suB ((n : Nat) : Int) ((seed : Nat) : Int) n
      (bubFam i seed ++ List.replicate (n - i) 0)
      (bubX (i + 1) seed) ((i : Nat) : Int) false 10)
    (Nat.le_refl n) hi
    (by rw [List.length_append, SortShared.lcgFamily_length,
          List.length_replicate]
        omega)
    (by rw [List.length_append, SortShared.lcgFamily_length,
          List.length_replicate]
        omega)
    SortShared.lcgFamilyZ_range hw
  rw [Nat.zero_add, SortShared.lcgFamily_set hi] at hst
  have h1 := stepFnIter_chain hB1
    (stepFnIter_one (stepFn_store_step hst))
  have hD := su_D_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    (bubX (i + 1) seed) ((i : Nat) : Int) ch
  have h2 := stepFnIter_chain h1 hD
  have hA1 := su_A1_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
    (bubX (i + 1) seed) ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : i + 1 < 2 ^ 64)),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : i + 1 < 2 ^ 64))] at hA1
  exact stepFnIter_chain h2 hA1

/-- **The setup loop**, by the P5 iteration schema: `68·(n−i)` steps
materialize the wrapped LCG family. -/
theorem su_loopB (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (68 * (n - i))
      (σB (bHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
        (bubFam i seed ++ List.replicate (n - i) 0)
        (bubX i seed) ((i : Nat) : Int) false) 10)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suCmpKB) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suCmpKB,
          σB (bHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
            (bubFam n seed) (bubX n seed) ((n : Nat) : Int) false) 10,
          ch) := by
  intro i hin ch
  have hgen := stepFnIter_iterate (c := 68) (n := n)
    (T := fun j => σB (bHeapSu ((n : Nat) : Int) ((seed : Nat) : Int) n
      (bubFam j seed ++ List.replicate (n - j) 0)
      (bubX j seed) ((j : Nat) : Int) false) 10)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) suCmpKB)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact su_iterB n seed hn hseed j hj ch')
    i hin ch
  simpa using hgen

/-! ## The copy loop, cleaned + its induction -/

theorem cp_iterB (n seed : Nat) (m : Nat)
    (hn : n < 2 ^ 63) (hcap : n ≤ 8) (hm : m < n) (ch : Choices) :
    stepFnIter 53
      (σB (bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (bubFam n seed) (bubPre m seed) (bubX n seed) ((n : Nat) : Int)
        ((m : Nat) : Int) false) 13)
      (.retV (.bool true) cpCmpKB) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKB,
          σB (bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (bubFam n seed) (bubPre (m + 1) seed) (bubX n seed)
            ((n : Nat) : Int) ((m + 1 : Nat) : Int) false) 13, ch) := by
  have hB1 := cp_B1_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) (bubPre m seed) (bubX n seed) ((n : Nat) : Int)
    ((m : Nat) : Int) ch
  have hget : (⟨(bubFam n seed).map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (bubX (m + 1) seed) .uint64) := by
    rw [Nat.zero_add,
      getElem?_mapU _ _ (by rw [SortShared.lcgFamily_length]; omega),
      SortShared.lcgFamily_getD hm]
  have hread := stepFn_strict_apply (done := [bSliceS n]) (env := cpEnvB2)
    (k := cpRhsKB ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_cpS_B ((n : Nat) : Int) ((seed : Nat) : Int) n
        (bubFam n seed) (bubPre m seed) (bubX n seed) ((n : Nat) : Int)
        ((m : Nat) : Int) false 13)
      (Nat.le_refl n) hm hget)
  have hB2 := cp_B2_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) (bubPre m seed) (bubX n seed) ((n : Nat) : Int)
    ((m : Nat) : Int) (.int (bubX (m + 1) seed) .uint64) ch
  have hxlt : SortShared.lcgStep bubA bubB (m + 1) seed < 2 ^ 64 :=
    SortShared.lcgStep_lt (by omega)
  have hw : (0 : Int) ≤ bubX (m + 1) seed
      ∧ bubX (m + 1) seed < 2 ^ 64 :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast hxlt⟩
  have hst := storeTarget_arrayLocal_u64 (a := ⟨10⟩) (N := 8) (i := m)
    (ik := .uint64) (l := bubPre m seed)
    (w := bubX (m + 1) seed)
    (lookup_cpPre_B ((n : Nat) : Int) ((seed : Nat) : Int) n
      (bubFam n seed) (bubPre m seed) (bubX n seed) ((n : Nat) : Int)
      ((m : Nat) : Int) false 13)
    (by rw [bubPre, List.length_append, SortShared.lcgFamily_length,
          List.length_replicate]
        omega)
    (by rw [bubPre, List.length_append, SortShared.lcgFamily_length,
          List.length_replicate]
        omega)
    SortShared.lcgFamilyZ_range hw
  rw [SortShared.lcgFamily_set (by omega : m < 8)] at hst
  have hD := cp_D_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) (bubPre (m + 1) seed) (bubX n seed) ((n : Nat) : Int)
    ((m : Nat) : Int) ch
  have hA1 := cp_A1_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) (bubPre (m + 1) seed) (bubX n seed) ((n : Nat) : Int)
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : m + 1 < 2 ^ 64)),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : m + 1 < 2 ^ 64))] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The copy loop**: `53·(n−m)` steps materialize the `pre` array. -/
theorem cp_loopB (n seed : Nat) (hn : n < 2 ^ 63) (hcap : n ≤ 8) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (σB (bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
        (bubFam n seed) (bubPre m seed) (bubX n seed) ((n : Nat) : Int)
        ((m : Nat) : Int) false) 13)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cpCmpKB) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cpCmpKB,
          σB (bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
            (bubFam n seed) (bubPre n seed) (bubX n seed)
            ((n : Nat) : Int) ((n : Nat) : Int) false) 13, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => σB (bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n
      (bubFam n seed) (bubPre j seed) (bubX n seed) ((n : Nat) : Int)
      ((j : Nat) : Int) false) 13)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) cpCmpKB)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp_iterB n seed j hn hcap hj ch')
    m hmn ch
  simpa using hgen

end GoLean.Examples.BubbleSort
