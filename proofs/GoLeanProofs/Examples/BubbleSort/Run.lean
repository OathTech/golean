import GoLeanProofs.Examples.BubbleSort.Outer

/-!
# BubbleSort — the epilogue and the full harness run

The post-subject remainder — the `post` copy loop and the two result
stores — proven ONCE at the canonical placement (`post` at 16, its
counter at 17, its flag at 18) and transferred to the true
(subject-garbage-laden) placement in a single `transfer_seg16`
application inside `bH_runs`, the end-to-end composition.

Epilogue step counts (probe-measured, re-checked by `rfl`):
anchor → copy head 33; dispatch 25/29; one copy iteration 53;
exit → the `$res0` store point 14; store; → the `$res1` store point 8;
store; → the driver terminal 6.
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.Frame

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The `post` array's pure form -/

/-- The `post` array after `m` copy steps: the copied prefix,
zero-padded to the cap.
-- KIT-GAP WITNESS (see .tmp/kitgaps-bubble.md): the third and fourth
fixed-cap copy-loop instantiations in the gallery; `prefixPad`
generalized off `familyMod` would delete this block. -/
def bPost (l : List Int) (m : Nat) : List Int :=
  l.take m ++ List.replicate (8 - m) 0

theorem bPost_zero (l : List Int) : bPost l 0 = zeros8 := rfl

theorem bPost_length {l : List Int} {m : Nat} (hm : m ≤ 8)
    (hml : m ≤ l.length) :
    (bPost l m).length = 8 := by
  rw [bPost, List.length_append, List.length_take, List.length_replicate]
  omega

theorem bPost_range {l : List Int} {m : Nat}
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ v ∈ bPost l m, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hr v (List.mem_of_mem_take hv)
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

/-- One copy store advances the `post` prefix. -/
theorem bPost_set {l : List Int} {m : Nat} (hm : m < l.length)
    (hm8 : m < 8) :
    (bPost l m).set m (l.getD m 0) = bPost l (m + 1) := by
  have hlen : (l.take m).length = m := by
    rw [List.length_take]; omega
  have hnm : 8 - m = (8 - (m + 1)) + 1 := by omega
  rw [bPost, List.set_append_right _ _ (by omega : (l.take m).length ≤ m),
    hlen, Nat.sub_self, hnm, List.replicate_succ, List.set_cons_zero]
  rw [bPost, List.take_succ, List.getElem?_eq_getElem hm]
  rw [← getD_of_lt hm]
  simp

/-! ## The epilogue heap fronts -/

/-- The epilogue's canonical state: the fixed subject prefix with
`post` at 16, the counter at 17, the flag at 18. -/
def bHeapEp (n seed : Nat) (l : List Int) (endF : Int) (lq : List Int)
    (civ : Int) (ffv : Bool) : Heap :=
  bHeapSubj n seed l endF false ++
    [(.base ⟨16⟩, bArr8 lq), (.base ⟨17⟩, bu64 civ), (.base ⟨18⟩, bbool ffv)]

/-- The terminal heap (both results delivered), spelled flat. -/
def bHeapEnd (n seed : Nat) (l : List Int) (endF : Int)
    (r0 r1 lq : List Int) (civ : Int) : Heap :=
  [(.base ⟨0⟩, bu64 ((n : Nat) : Int)),
   (.base ⟨1⟩, bu64 ((seed : Nat) : Int)),
   (.base ⟨2⟩, bArr8 r0), (.base ⟨3⟩, bArr8 r1),
   (.base ⟨4⟩, bHandle n), (.base ⟨5⟩, bBack n l), (.base ⟨6⟩, bHandle n),
   (.base ⟨7⟩, bu64 (bubX n seed)), (.base ⟨8⟩, bu64 ((n : Nat) : Int)),
   (.base ⟨9⟩, bbool false),
   (.base ⟨10⟩, bArr8 (bubPre n seed)),
   (.base ⟨11⟩, bu64 ((n : Nat) : Int)), (.base ⟨12⟩, bbool false),
   (.base ⟨13⟩, bHandle n), (.base ⟨14⟩, bint endF),
   (.base ⟨15⟩, bbool false),
   (.base ⟨16⟩, bArr8 lq), (.base ⟨17⟩, bu64 civ),
   (.base ⟨18⟩, bbool false)]

/-! ## Heap-lookup facts at the epilogue placement -/

theorem lookup_epS (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ffv : Bool) :
    Heap.lookup (σB (bHeapEp n seed l endF lq civ ffv) 19).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapEp, bHeapSubj, bHeapCp, bHeapSu, bHeap0, Heap.lookup]

theorem lookup_epPost (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ffv : Bool) :
    Heap.lookup (σB (bHeapEp n seed l endF lq civ ffv) 19).heap
        (.base ⟨16⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapEp, bHeapSubj, bHeapCp, bHeapSu, bHeap0, Heap.lookup]

theorem lookup_ep2 (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ffv : Bool) :
    Heap.lookup (σB (bHeapEp n seed l endF lq civ ffv) 19).heap
        (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapEp, bHeapSubj, bHeapCp, bHeapSu, bHeap0, Heap.lookup]

theorem lookup_end3 (n seed : Nat) (l : List Int) (endF : Int)
    (r0 r1 lq : List Int) (civ : Int) :
    Heap.lookup (σB (bHeapEnd n seed l endF r0 r1 lq civ) 19).heap
        (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨r1.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapEnd, Heap.lookup]

/-! ## Raw segments — the epilogue -/

/-- The anchor → `var post` declared → the second copy loop's head.
33 steps. -/
theorem bEp_entry_raw (n seed : Nat) (l : List Int) (endF : Int)
    (ch : Choices) :
    stepFnIter 33 (σBOut n seed l endF false) (.next bAfterCallK) ch
      = .ok (epHeadCfgB,
          σB (bHeapEp n seed l endF zeros8 0 true) 19, ch) := by
  with_unfolding_all rfl

theorem ep_A0_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 25 (σB (bHeapEp n seed l endF lq civ true) 19)
      epHeadCfgB ch
      = .ok (.retV (.bool (decide (civ < ((n : Nat) : Int)))) epCmpKB,
          σB (bHeapEp n seed l endF lq civ false) 19, ch) := by
  with_unfolding_all rfl

theorem ep_A1_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 29 (σB (bHeapEp n seed l endF lq civ false) 19)
      epHeadCfgB ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < ((n : Nat) : Int)))) epCmpKB,
          σB (bHeapEp n seed l endF lq
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false) 19, ch) := by
  with_unfolding_all rfl

theorem ep_B1_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 16 (σB (bHeapEp n seed l endF lq civ false) 19)
      (.retV (.bool true) epCmpKB) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [bSliceS n] [] epEnvB2 (epRhsKB civ)),
          σB (bHeapEp n seed l endF lq civ false) 19, ch) := by
  with_unfolding_all rfl

theorem ep_B2_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σB (bHeapEp n seed l endF lq civ false) 19)
      (.retV w (epRhsKB civ)) ch
      = .ok (.next (.storeK [epRefB civ] [w] (.seqn #[]) epEnvB2
            epStTailB),
          σB (bHeapEp n seed l endF lq civ false) 19, ch) := by
  with_unfolding_all rfl

theorem ep_D_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 5 (σB (bHeapEp n seed l endF lq civ false) 19)
      (.next (.storeK [] [] (.seqn #[]) epEnvB2 epStTailB)) ch
      = .ok (epHeadCfgB, σB (bHeapEp n seed l endF lq civ false) 19,
          ch) := by
  with_unfolding_all rfl

/-- Copy exit → the `$res0 = pre` store point (the array value is read
raw from cell 10). 14 steps. -/
theorem ep_X_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 14 (σB (bHeapEp n seed l endF lq civ false) 19)
      (.retV (.bool false) epCmpKB) ch
      = .ok (.next (.storeK [bRes0Ref]
            [.array ⟨(bubPre n seed).map (fun v => .int v .uint64)⟩]
            (.seqn #[]) epEnvTail bEpiTail1),
          σB (bHeapEp n seed l endF lq civ false) 19, ch) := by
  with_unfolding_all rfl

/-- `$res0` delivered → the `$res1 = post` store point. 8 steps. -/
theorem ep_R2_raw (n seed : Nat) (l : List Int) (endF : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 8
      (σB (bHeapEnd n seed l endF (bubPre n seed) zeros8 lq civ) 19)
      (.next (.storeK [] [] (.seqn #[]) epEnvTail bEpiTail1)) ch
      = .ok (.next (.storeK [bRes1Ref]
            [.array ⟨lq.map (fun v => .int v .uint64)⟩]
            (.seqn #[]) epEnvTail bEpiTail2),
          σB (bHeapEnd n seed l endF (bubPre n seed) zeros8 lq civ) 19,
          ch) := by
  with_unfolding_all rfl

/-- `$res1` delivered → return, frame exit — the driver terminal.
6 steps. -/
theorem ep_fin_raw (n seed : Nat) (l : List Int) (endF : Int)
    (r1 lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 6
      (σB (bHeapEnd n seed l endF (bubPre n seed) r1 lq civ) 19)
      (.next (.storeK [] [] (.seqn #[]) epEnvTail bEpiTail2)) ch
      = .ok (.next .stop,
          σB (bHeapEnd n seed l endF (bubPre n seed) r1 lq civ) 19,
          ch) := by
  with_unfolding_all rfl

/-! ## The epilogue copy loop -/

theorem ep_iterB (n seed : Nat) (l : List Int) (endF : Int) (m : Nat)
    (hcap : n ≤ 8) (hln : l.length = n) (hm : m < n)
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (ch : Choices) :
    stepFnIter 53
      (σB (bHeapEp n seed l endF (bPost l m) ((m : Nat) : Int) false) 19)
      (.retV (.bool true) epCmpKB) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) epCmpKB,
          σB (bHeapEp n seed l endF (bPost l (m + 1))
            ((m + 1 : Nat) : Int) false) 19, ch) := by
  have hB1 := ep_B1_raw n seed l endF (bPost l m) ((m : Nat) : Int) ch
  have hget : (⟨l.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (l.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by rw [hln]; omega)]
  have hread := stepFn_strict_apply (done := [bSliceS n]) (env := epEnvB2)
    (k := epRhsKB ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_epS n seed l endF (bPost l m) ((m : Nat) : Int) false)
      (Nat.le_refl n) (by omega) hget)
  have hB2 := ep_B2_raw n seed l endF (bPost l m) ((m : Nat) : Int)
    (.int (l.getD m 0) .uint64) ch
  have hw : (0 : Int) ≤ l.getD m 0 ∧ l.getD m 0 < 2 ^ 64 :=
    hr _ (getD_mem (by rw [hln]; omega))
  have hst := storeTarget_arrayLocal_u64 (a := ⟨16⟩) (N := 8) (i := m)
    (ik := .uint64) (l := bPost l m) (w := l.getD m 0)
    (lookup_epPost n seed l endF (bPost l m) ((m : Nat) : Int) false)
    (by rw [bPost_length (by omega) (by rw [hln]; omega)]; omega)
    (bPost_length (by omega) (by rw [hln]; omega)) (bPost_range hr) hw
  rw [bPost_set (by rw [hln]; omega) (by omega)] at hst
  have hD := ep_D_raw n seed l endF (bPost l (m + 1)) ((m : Nat) : Int) ch
  have hA1 := ep_A1_raw n seed l endF (bPost l (m + 1)) ((m : Nat) : Int)
    ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : m + 1 < 2 ^ 64)),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : m + 1 < 2 ^ 64))] at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

theorem ep_loopB (n seed : Nat) (l : List Int) (endF : Int)
    (hcap : n ≤ 8) (hln : l.length = n)
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (σB (bHeapEp n seed l endF (bPost l m) ((m : Nat) : Int) false) 19)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        epCmpKB) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) epCmpKB,
          σB (bHeapEp n seed l endF (bPost l n) ((n : Nat) : Int)
            false) 19, ch) := by
  intro m hmn ch
  have hgen := stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => σB (bHeapEp n seed l endF (bPost l j)
      ((j : Nat) : Int) false) 19)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) epCmpKB)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact ep_iterB n seed l endF j hcap hln hj hr ch')
    m hmn ch
  simpa using hgen

/-! ## The epilogue, composed (canonical placement) -/

/-- **The epilogue run**: from the post-call anchor at the canonical
placement, the `post` copy loop and the two result stores reach the
DRIVER TERMINAL within `53·n + 88` steps, with `pre` in `$res0` and
the (sorted) copy in `$res1`. -/
theorem bEp_runs (n seed : Nat) (l : List Int) (endF : Int)
    (hcap : n ≤ 8) (hln : l.length = n)
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (ch : Choices) :
    ∃ k : Nat, k ≤ 53 * n + 88 ∧
      stepFnIter k (σBOut n seed l endF false) (.next bAfterCallK) ch
        = .ok (.next .stop,
            σB (bHeapEnd n seed l endF (bubPre n seed) (bPost l n)
              (bPost l n) ((n : Nat) : Int)) 19, ch) := by
  have hE := bEp_entry_raw n seed l endF ch
  have hA0 := ep_A0_raw n seed l endF zeros8 0 ch
  have hloop := ep_loopB n seed l endF hcap hln hr 0 (by omega) ch
  rw [show bPost l 0 = zeros8 from rfl,
    show ((0 : Nat) : Int) = (0 : Int) from rfl] at hloop
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hloop
  have hX := ep_X_raw n seed l endF (bPost l n) ((n : Nat) : Int) ch
  -- the $res0 store
  have hpre_len : (bubPre n seed).length = 8 := by
    rw [bubPre, List.length_append, SortShared.lcgFamily_length,
      List.length_replicate]
    omega
  have hst0 : storeTarget
      (σB (bHeapEp n seed l endF (bPost l n) ((n : Nat) : Int) false) 19)
      bRes0Ref (.array ⟨(bubPre n seed).map (fun v => .int v .uint64)⟩)
      = .ok (σB (bHeapEnd n seed l endF (bubPre n seed) zeros8
          (bPost l n) ((n : Nat) : Int)) 19) :=
    storeTarget_addr
      (lookup_ep2 n seed l endF (bPost l n) ((n : Nat) : Int) false)
      (normalizeValueForTy_arr_u64 hpre_len SortShared.lcgFamilyZ_range)
  have hR2 := ep_R2_raw n seed l endF (bPost l n) ((n : Nat) : Int) ch
  -- the $res1 store
  have hst1 : storeTarget
      (σB (bHeapEnd n seed l endF (bubPre n seed) zeros8 (bPost l n)
        ((n : Nat) : Int)) 19)
      bRes1Ref (.array ⟨(bPost l n).map (fun v => .int v .uint64)⟩)
      = .ok (σB (bHeapEnd n seed l endF (bubPre n seed) (bPost l n)
          (bPost l n) ((n : Nat) : Int)) 19) :=
    storeTarget_addr
      (lookup_end3 n seed l endF (bubPre n seed) zeros8 (bPost l n)
        ((n : Nat) : Int))
      (normalizeValueForTy_arr_u64 (bPost_length (by omega) (by rw [hln]; omega))
        (bPost_range hr))
  have hF := ep_fin_raw n seed l endF (bPost l n) (bPost l n)
    ((n : Nat) : Int) ch
  refine ⟨33 + 25 + 53 * (n - 0) + 14 + 1 + 8 + 1 + 6, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hE hA0) hloop) hX)
        (stepFnIter_one (stepFn_store_step hst0))) hR2)
          (stepFnIter_one (stepFn_store_step hst1))) hF

/-! ## The full harness run -/

/-- The sorted list, as statement-adjacent vocabulary for the
composition: `sortSpec` of the LCG family. -/
abbrev bubSorted (n seed : Nat) : List Int :=
  GoLean.Examples.InsertionSort.sortSpec (bubFam n seed)

theorem bubSorted_length (n seed : Nat) : (bubSorted n seed).length = n := by
  rw [bubSorted, GoLean.Examples.InsertionSort.sortSpec_length,
    SortShared.lcgFamily_length]

theorem bubSorted_range (n seed : Nat) :
    ∀ x ∈ bubSorted n seed, 0 ≤ x ∧ x < 2 ^ 64 := fun x hx =>
  SortShared.lcgFamily_range bubA bubB n seed x
    (GoLean.Examples.InsertionSort.mem_sortSpec hx)

/-- **The harness run, end to end**: within
`(105·n + 116)·n + 174·n + 318` steps the harness reaches the driver
terminal with the pre-copy in `$res0` and the SORTED copy —
`sortSpec` of the family — in `$res1`. -/
theorem bH_runs (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ (105 * n + 116) * n + 174 * n + 318 ∧
      stepFnIter k (σB (bHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4)
        bHC0 ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩) = some (bArr8 (bubPre n seed))
      ∧ Heap.lookup σf.heap (.base ⟨3⟩)
          = some (bArr8 (bPost (bubSorted n seed) n)) := by
  have hn : n < 2 ^ 63 := by omega
  have hfam_len : (bubFam n seed).length = n :=
    SortShared.lcgFamily_length bubA bubB n seed
  have hfam_range : ∀ x ∈ bubFam n seed, 0 ≤ x ∧ x < 2 ^ 64 :=
    SortShared.lcgFamily_range bubA bubB n seed
  -- entry
  have hE1 := b_E1_raw ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hmk := stepFnIter_one
    (stepFn_makeSlice_u64_step (env := envC4B)
      (k := .seq [bS2, bS3, bS4, bS5, bS6, bS7, bS8, bS9, bS10] envC4B
        (.frame [] [] [] [] .stop))
      (b_make_apply ((n : Nat) : Int) ((seed : Nat) : Int) n ch))
  have hE2 := b_E2_raw ((n : Nat) : Int) ((seed : Nat) : Int) n ch
  rw [unorm_of_range (v := ((seed : Nat) : Int)) (by omega)
    (by exact_mod_cast hseed)] at hE2
  -- the setup loop
  have hA0 := su_A0_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (List.replicate n 0) ((seed : Nat) : Int) 0 ch
  have hsu := su_loopB n seed hn hseed 0 (by omega) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hsu
  have hentry := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hmk) hE2) hA0) hsu
  -- the setup exit and the copy loop
  have hX := su_X_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) (bubX n seed) ((n : Nat) : Int) ch
  have hcA0 := cp_A0_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) zeros8 (bubX n seed) ((n : Nat) : Int) 0 ch
  have hcp := cp_loopB n seed hn hcap 0 (by omega) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hcp
  have hcpX := cp_X_rawB ((n : Nat) : Int) ((seed : Nat) : Int) n
    (bubFam n seed) (bubPre n seed) (bubX n seed) ((n : Nat) : Int)
    ((n : Nat) : Int) ch
  have hthru := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hentry hX) hcA0) hcp) hcpX
  -- the subject prologue
  have hEnter := b_enter_raw n seed (bubFam n seed) ch
  have hlenap0 : applyStrictOp (σB (bHeapPre1 n seed (bubFam n seed)) 15)
      (.lengthOf (some (.slice tU64))) [bSliceS n]
      = .ok (.int ((n : Nat) : Int) .int,
          σB (bHeapPre1 n seed (bubFam n seed)) 15) :=
    applyStrictOp_len_slice (Nat.le_refl n)
  have hlenap := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := bEnvEnd) (k := bEndRhsK)
      (ch := ch) hlenap0)
  have hpreB := b_preB_raw n seed (bubFam n seed) ch
  rw [inorm_nat_of_lt hn] at hpreB
  have hOA0 := bO_A0_raw n seed (bubFam n seed) ((n : Nat) : Int) [] 16 ch
  have hthru2 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hthru hEnter) hlenap) hpreB) hOA0
  -- the subject loop
  have hI0 : BubbleInv (bubFam n seed) (bubFam n seed) n := by
    have := bubbleInv_init (bubFam n seed)
    rwa [hfam_len] at this
  obtain ⟨k1, σA', d', fr', endF, hk1, hsubj, hFSd⟩ := bOuter_loop n seed
    (bubFam n seed) hn hfam_len hfam_range (n - 1) n (bubFam n seed)
    (σBOut n seed (bubFam n seed) ((n : Nat) : Int) false) 0 [] rfl
    (Nat.le_refl n) hfam_len hI0 hfam_range
    (frameSim_zero16 n seed (bubFam n seed) ((n : Nat) : Int) false) ch
  -- the epilogue, transferred through the surviving frame simulation
  obtain ⟨k2, hk2, hep⟩ := bEp_runs n seed (bubSorted n seed) endF hcap
    (bubSorted_length n seed) (bubSorted_range n seed) ch
  obtain ⟨σf, hrunT, hFSf⟩ := transfer_seg16 hFSd hep
    (renCfg_banchor d') (renCfg_bstop d')
  have hread2 := hFSf.lookup_some (l := .base ⟨2⟩)
    (c := bArr8 (bubPre n seed)) (by simp [bHeapEnd, Heap.lookup])
  have hread3 := hFSf.lookup_some (l := .base ⟨3⟩)
    (c := bArr8 (bPost (bubSorted n seed) n))
    (by simp [bHeapEnd, Heap.lookup])
  have hren2 : renameLoc (ρ16 d') (.base ⟨2⟩) = .base ⟨2⟩ := by
    simp [renameLoc, ρ16]
  have hren3 : renameLoc (ρ16 d') (.base ⟨3⟩) = .base ⟨3⟩ := by
    simp [renameLoc, ρ16]
  rw [hren2, renCell_arr8B] at hread2
  rw [hren3, renCell_arr8B] at hread3
  -- the chain
  have hall := stepFnIter_chain (stepFnIter_chain hthru2 hsubj) hrunT
  refine ⟨10 + 1 + 55 + 25 + 68 * (n - 0) + 39 + 25 + 53 * (n - 0) + 9
      + 14 + 1 + 18 + 25 + k1 + k2, σf, ?_, hall, hread2, hread3⟩
  have hmuls : (105 * n + 116) * (n - 1) ≤ (105 * n + 116) * n :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end GoLean.Examples.BubbleSort
