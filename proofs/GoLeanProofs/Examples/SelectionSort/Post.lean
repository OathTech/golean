import GoLeanProofs.Examples.SelectionSort.Frame

/-!
# SelectionSort — Post (the second copy loop and the epilogue)

The post-subject phase, proven as ONE canonical run from the
post-subject anchor (`.next sAfterCallK`) to the DRIVER TERMINAL:
`var post [8]uint64` (canonical cells 16/17/18), the copy loop
`post[i] = s[i]`, then `$res0 = pre; $res1 = post; return`. The run
theorem `post_runs` is transferred to the true placement in ONE
`transfer_seg16` application by `SelectionSort/Run.lean`.

Segment counts (probe-measured, re-checked by `rfl`): anchor → copy
head 33; dispatch 25/29; one iteration 53; exit → the `$res0` store
14; between-stores 8; tail 6. Total `53·n + 88`, exact.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Examples.SortShared

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The copy-prefix of the sorted backing

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (selsort)): the copy-OUT loop's
prefix (`takePad`) has no kit form — `SliceMem.prefixPad`'s set lemma
is `familyMod`-keyed, and this loop copies COMPUTED data. Consumers:
selsort (here), bubble (chartered). -/

/-- The `post` array after `m` copy steps. -/
def selPost (lf : List Int) (m : Nat) : List Int :=
  lf.take m ++ List.replicate (8 - m) 0

theorem selPost_length {lf : List Int} {n m : Nat} (hlen : lf.length = n)
    (hm : m ≤ n) (hcap : n ≤ 8) : (selPost lf m).length = 8 := by
  rw [selPost, List.length_append, List.length_take,
    List.length_replicate]
  omega

theorem selPost_range {lf : List Int} {m : Nat}
    (hr : ∀ x ∈ lf, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ v ∈ selPost lf m, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hr v (List.mem_of_mem_take hv)
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem selPost_full {lf : List Int} {n : Nat} (hlen : lf.length = n) :
    selPost lf n = selPad8 lf := by
  rw [selPost, selPad8, hlen, List.take_of_length_le (by omega)]

/-- One copy store advances the prefix. -/
theorem selPost_set {lf : List Int} {n m : Nat} (hlen : lf.length = n)
    (hm : m < n) (hcap : n ≤ 8) :
    (selPost lf m).set m (lf.getD m 0) = selPost lf (m + 1) := by
  have hlt : (lf.take m).length = m := by
    rw [List.length_take]
    omega
  have hnm : 8 - m = (8 - (m + 1)) + 1 := by omega
  have hget : lf.getD m 0 = lf[m]'(by omega) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : m < lf.length)]
    rfl
  have htake : lf.take (m + 1) = lf.take m ++ [lf[m]'(by omega)] := by
    rw [List.take_add_one,
      List.getElem?_eq_getElem (by omega : m < lf.length)]
    rfl
  rw [selPost, selPost, htake, List.set_append_right _ _ (by omega), hlt,
    Nat.sub_self, hnm, List.replicate_succ, List.set_cons_zero, hget,
    List.append_assoc]
  rfl

/-! ## Raw segments -/

/-- Anchor → the post copy loop head: `var post` at 16, `i := 0` at
17, the flag at 18. 33 steps. -/
theorem pR1_raw (n seed : Nat) (lf : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 33 (σOut n seed lf iv false) (.next sAfterCallK) ch
      = .ok (cp2HeadCfg, σPost n seed lf iv zeros8 0 true, ch) := by
  with_unfolding_all rfl

theorem cp2_A0_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 25 (σPost n seed lf iv lq civ true) cp2HeadCfg ch
      = .ok (.retV (.bool (decide (civ < ((n : Nat) : Int)))) cp2CmpK,
          σPost n seed lf iv lq civ false, ch) := by
  with_unfolding_all rfl

theorem cp2_A1_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 29 (σPost n seed lf iv lq civ false) cp2HeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1))
              < ((n : Nat) : Int)))) cp2CmpK,
          σPost n seed lf iv lq
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (civ + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- Copy phase 1: test true → the `post[i]` target banked, the `s[i]`
read at its apply point. 16 steps. -/
theorem cp2_B1_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 16 (σPost n seed lf iv lq civ false)
      (.retV (.bool true) cp2CmpK) ch
      = .ok (.retV (.int civ .uint64)
            (.strictK .indexGet [sHandle n] [] cp2Env2 (cp2RhsK civ)),
          σPost n seed lf iv lq civ false, ch) := by
  with_unfolding_all rfl

theorem cp2_B2_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σPost n seed lf iv lq civ false)
      (.retV w (cp2RhsK civ)) ch
      = .ok (.next (.storeK [cp2Ref civ] [w] (.seqn #[]) cp2Env2
            cp2StTail),
          σPost n seed lf iv lq civ false, ch) := by
  with_unfolding_all rfl

theorem cp2_D_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 5 (σPost n seed lf iv lq civ false)
      (.next (.storeK [] [] (.seqn #[]) cp2Env2 cp2StTail)) ch
      = .ok (cp2HeadCfg, σPost n seed lf iv lq civ false, ch) := by
  with_unfolding_all rfl

/-- Copy exit: test false → break → `$res0 = pre` pending (the array's
contents are symbolic, so the store is split out). 14 steps. -/
theorem pX_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ch : Choices) :
    stepFnIter 14 (σPost n seed lf iv lq civ false)
      (.retV (.bool false) cp2CmpK) ch
      = .ok (.next (.storeK [res0Ref]
            [.array ⟨(selPad8 (selFam n seed)).map
              (fun v => .int v .uint64)⟩] (.seqn #[])
            [postScope, baseScope] epiTail),
          σPost n seed lf iv lq civ false, ch) := by
  with_unfolding_all rfl

/-- Between the stores: `$res1 = post` pending. 8 steps. -/
theorem pY_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (ch : Choices) :
    stepFnIter 8 (σRes0 n seed lf iv lq)
      (.next (.storeK [] [] (.seqn #[]) [postScope, baseScope] epiTail))
      ch
      = .ok (.next (.storeK [res1Ref]
            [.array ⟨lq.map (fun v => .int v .uint64)⟩] (.seqn #[])
            [postScope, baseScope] epiTail2),
          σRes0 n seed lf iv lq, ch) := by
  with_unfolding_all rfl

/-- The tail: return, barrier exit — the driver terminal. 6 steps. -/
theorem pZ_raw (n seed : Nat) (lf : List Int) (iv : Int)
    (lq : List Int) (ch : Choices) :
    stepFnIter 6 (σEnd n seed lf iv lq)
      (.next (.storeK [] [] (.seqn #[]) [postScope, baseScope] epiTail2))
      ch
      = .ok (.next .stop, σEnd n seed lf iv lq, ch) := by
  with_unfolding_all rfl

/-! ## One copy iteration and the loop -/

theorem cp2_iter (n seed : Nat) (lf : List Int) (iv : Int) (m : Nat)
    (hlen : lf.length = n) (hcap : n ≤ 8) (hm : m < n)
    (hr : ∀ x ∈ lf, 0 ≤ x ∧ x < 2 ^ 64) (ch : Choices) :
    stepFnIter 53
      (σPost n seed lf iv (selPost lf m) ((m : Nat) : Int) false)
      (.retV (.bool true) cp2CmpK) ch
      = .ok (.retV (.bool (decide
            (((m + 1 : Nat) : Int) < ((n : Nat) : Int)))) cp2CmpK,
          σPost n seed lf iv (selPost lf (m + 1)) ((m + 1 : Nat) : Int)
            false, ch) := by
  have hB1 := cp2_B1_raw n seed lf iv (selPost lf m) ((m : Nat) : Int) ch
  have hget : (⟨lf.map (fun v => .int v .uint64)⟩ :
      Array GoValue)[0 + m]?
      = some (.int (lf.getD m 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU _ _ (by omega)]
  have hread := stepFn_strict_apply (done := [sHandle n]) (env := cp2Env2)
    (k := cp2RhsK ((m : Nat) : Int)) (ch := ch)
    (applyStrictOp_indexGet_slice (ik := .uint64)
      (lookup_σPost5 n seed lf iv (selPost lf m) ((m : Nat) : Int) false)
      (Nat.le_refl n) hm hget)
  have hB2 := cp2_B2_raw n seed lf iv (selPost lf m) ((m : Nat) : Int)
    (.int (lf.getD m 0) .uint64) ch
  have hw : (0 : Int) ≤ lf.getD m 0 ∧ lf.getD m 0 < 2 ^ 64 :=
    hr _ (getD_mem (by omega))
  have hst := storeTarget_arrayLocal_u64 (a := ⟨16⟩) (N := 8) (i := m)
    (ik := .uint64) (l := selPost lf m) (w := lf.getD m 0)
    (lookup_σPost16 n seed lf iv (selPost lf m) ((m : Nat) : Int) false)
    (by rw [selPost_length hlen (by omega) hcap]; omega)
    (selPost_length hlen (by omega) hcap) (selPost_range hr) hw
  rw [selPost_set hlen hm hcap] at hst
  have hD := cp2_D_raw n seed lf iv (selPost lf (m + 1))
    ((m : Nat) : Int) ch
  have hA1 := cp2_A1_raw n seed lf iv (selPost lf (m + 1))
    ((m : Nat) : Int) ch
  rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((m + 1 : Nat) : Int)) (by omega) (by omega)]
    at hA1
  have h1 := stepFnIter_chain hB1 (stepFnIter_one hread)
  have h2 := stepFnIter_chain h1 hB2
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst))
  exact stepFnIter_chain (stepFnIter_chain h3 hD) hA1

/-- **The post copy loop** (P5 schema): `53·(n−m)` steps. -/
theorem cp2_loop (n seed : Nat) (lf : List Int) (iv : Int)
    (hlen : lf.length = n) (hcap : n ≤ 8)
    (hr : ∀ x ∈ lf, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (53 * (n - m))
      (σPost n seed lf iv (selPost lf m) ((m : Nat) : Int) false)
      (.retV (.bool (decide (((m : Nat) : Int) < ((n : Nat) : Int))))
        cp2CmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) cp2CmpK,
          σPost n seed lf iv (selPost lf n) ((n : Nat) : Int) false,
          ch) := by
  intro m hmn ch
  exact stepFnIter_iterate (c := 53) (n := n)
    (T := fun j => σPost n seed lf iv (selPost lf j) ((j : Nat) : Int)
      false)
    (C := fun j => .retV (.bool (decide (((j : Nat) : Int)
      < ((n : Nat) : Int)))) cp2CmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact cp2_iter n seed lf iv j hlen hcap hj hr ch')
    m hmn ch

/-! ## The canonical post-phase run, end to end -/

/-- **The post phase** (EXACT, branch-free): `53·n + 88` steps from the
post-subject anchor to the driver terminal, with the padded family in
`$res0` and the padded sorted backing in `$res1`. -/
theorem post_runs (n seed : Nat) (lf : List Int) (iv : Int)
    (hlen : lf.length = n) (hcap : n ≤ 8)
    (hr : ∀ x ∈ lf, 0 ≤ x ∧ x < 2 ^ 64) (ch : Choices) :
    stepFnIter (53 * n + 88) (σOut n seed lf iv false)
      (.next sAfterCallK) ch
      = .ok (.next .stop, σEnd n seed lf iv (selPad8 lf), ch) := by
  have hR1 := pR1_raw n seed lf iv ch
  have hA0 := cp2_A0_raw n seed lf iv zeros8 0 ch
  have hloop := cp2_loop n seed lf iv hlen hcap hr 0 (by omega) ch
  rw [show selPost lf 0 = zeros8 from rfl,
    show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hloop
  have h1 := stepFnIter_chain (stepFnIter_chain hR1 hA0) hloop
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at h1
  have hX := pX_raw n seed lf iv (selPost lf n) ((n : Nat) : Int) ch
  have h2 := stepFnIter_chain h1 hX
  -- the $res0 = pre store
  have hpreLen : (selPad8 (selFam n seed)).length = 8 := by
    rw [← selPre_full]
    exact selPre_length hcap
  have hpreRange : ∀ v ∈ selPad8 (selFam n seed), 0 ≤ v ∧ v < 2 ^ 64 := by
    rw [← selPre_full]
    exact selPre_range
  have hst0 : storeTarget
      (σPost n seed lf iv (selPost lf n) ((n : Nat) : Int) false)
      res0Ref
      (.array ⟨(selPad8 (selFam n seed)).map (fun v => .int v .uint64)⟩)
      = .ok (σRes0 n seed lf iv (selPost lf n)) :=
    storeTarget_addr
      (lookup_σPost2 n seed lf iv (selPost lf n) ((n : Nat) : Int) false)
      (normalizeValueForTy_arr_u64 hpreLen hpreRange)
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (stepFn_store_step hst0))
  have hY := pY_raw n seed lf iv (selPost lf n) ch
  have h4 := stepFnIter_chain h3 hY
  -- the $res1 = post store
  have hpostLen : (selPost lf n).length = 8 :=
    selPost_length hlen (by omega) hcap
  have hst1 : storeTarget (σRes0 n seed lf iv (selPost lf n)) res1Ref
      (.array ⟨(selPost lf n).map (fun v => .int v .uint64)⟩)
      = .ok (σEnd n seed lf iv (selPost lf n)) :=
    storeTarget_addr
      (lookup_σRes0_3 n seed lf iv (selPost lf n))
      (normalizeValueForTy_arr_u64 hpostLen (selPost_range hr))
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (stepFn_store_step hst1))
  have hZ := pZ_raw n seed lf iv (selPost lf n) ch
  have h6 := stepFnIter_chain h5 hZ
  rw [selPost_full hlen] at h6
  have harith : 33 + 25 + 53 * (n - 0) + 14 + 1 + 8 + 1 + 6
      = 53 * n + 88 := by omega
  rw [harith] at h6
  exact h6

end GoLean.Examples.SelectionSort
