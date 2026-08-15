import GoLeanProofs.Examples.SelectionSort.HarnessR

/-!
# SelectionSort — Subject (the nested loop at the CANONICAL placement)

One outer pass, proven at the tight placement (`m`/`j`/`$forFirst` at
16/17/18): the pass entry, the inner scan (a plain strong induction on
the ascending counter `j`, invariant `m = minIdx l i (j-i-1)`), the
unconditional swap, and the next outer dispatch. The frame layer in
`SelectionSort/Frame.lean` transfers each pass to the true
(garbage-laden) placement and retires the pass cells.

Segment counts (probe-measured, re-checked by `rfl`):

| segment | steps |
|---|---|
| outer dispatch (first / later) | 25 / 29, + 1 len + 1 cmp |
| pass entry (`m := i`, `j := i+1`, flag) | 50 |
| inner dispatch (first / later) | 25 / 29, + 1 len + 1 cmp |
| inner body reads + compare | 11 + 1 + 5 + 1 + 1 |
| `m := j` arm / skip arm | 17 / 5 |
| inner exit → swap → outer head | 37 |
| outer exit → the post anchor | 8 |

One inner iteration ≤ 67 steps; one pass ≤ `67·n + 145`.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Examples.SortShared

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw segments — the outer spine (tail-parametric) -/

theorem o_A0_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σOutT n seed l iv true tail na) outerHeadCfg ch
      = .ok (.retV (sHandle n) (lenKO iv),
          σOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

theorem o_A1_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σOutT n seed l iv false tail na) outerHeadCfg ch
      = .ok (.retV (sHandle n)
            (lenKO (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σOutT n seed l
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

theorem o_OB_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 1 (σOutT n seed l iv false tail na)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpK)) ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) outerCmpK,
          σOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- Outer exit: test false → break unwinding, subject frame exit → the
post-phase anchor. 8 steps; state untouched. -/
theorem o_exit_raw (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 8 (σOutT n seed l iv false tail na)
      (.retV (.bool false) outerCmpK) ch
      = .ok (.next sAfterCallK, σOutT n seed l iv false tail na, ch) := by
  with_unfolding_all rfl

/-- The outer `len(s)` apply, cleaned (tail-parametric). -/
theorem o_len_step (n seed : Nat) (l : List Int) (iv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFn (σOutT n seed l iv false tail na)
      (.retV (sHandle n) (lenKO iv)) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpK),
        σOutT n seed l iv false tail na, ch) :=
  stepFn_strict_apply (done := [])
    (applyStrictOp_len_slice (Nat.le_refl n))

/-! ## Raw segments — the pass (TIGHT placement) -/

/-- Pass entry: outer test true → `m := i` at 16, `j := i + 1` at 17,
the inner flag at 18 → the inner loop head. 50 steps. -/
theorem passA_raw (n seed : Nat) (l : List Int) (iv : Int)
    (ch : Choices) :
    stepFnIter 50 (σOut n seed l iv false)
      (.retV (.bool true) outerCmpK) ch
      = .ok (innerHeadCfg,
          σIn n seed l iv (IntKind.normalize .int iv)
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            true, ch) := by
  with_unfolding_all rfl

theorem i_I0_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 25 (σIn n seed l iv mv jv true) innerHeadCfg ch
      = .ok (.retV (sHandle n) (lenKI jv),
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

theorem i_I1_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 29 (σIn n seed l iv mv jv false) innerHeadCfg ch
      = .ok (.retV (sHandle n)
            (lenKI (IntKind.normalize .int (IntKind.normalize .int (jv + 1)))),
          σIn n seed l iv mv
            (IntKind.normalize .int (IntKind.normalize .int (jv + 1)))
            false, ch) := by
  with_unfolding_all rfl

theorem i_len_step (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFn (σIn n seed l iv mv jv false)
      (.retV (sHandle n) (lenKI jv)) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int jv .int] [] ([] :: envI) innerCmpK),
        σIn n seed l iv mv jv false, ch) :=
  stepFn_strict_apply (done := [])
    (applyStrictOp_len_slice (Nat.le_refl n))

theorem i_IB_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 1 (σIn n seed l iv mv jv false)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] ([] :: envI) innerCmpK)) ch
      = .ok (.retV (.bool (decide (jv < ((n : Nat) : Int)))) innerCmpK,
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- Inner body A: test true → the `s[j]` read's apply point. 11
steps. -/
theorem i_CA_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 11 (σIn n seed l iv mv jv false)
      (.retV (.bool true) innerCmpK) ch
      = .ok (.retV (.int jv .int) (idx1K n),
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- Inner body B: `s[j]` banked → the `s[m]` read's apply point.
5 steps. -/
theorem i_CB_raw (n seed : Nat) (l : List Int) (iv mv jv a : Int)
    (ch : Choices) :
    stepFnIter 5 (σIn n seed l iv mv jv false)
      (.retV (.int a .uint64)
        (.strictK .lessCmp [] [.indexGet (.var "s") (.var "m")] envB2
          mIfK)) ch
      = .ok (.retV (.int mv .int) (idx2K n a),
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- Inner body C: both elements banked → the `<` verdict at the `if`.
1 step. -/
theorem i_CC_raw (n seed : Nat) (l : List Int) (iv mv jv a b : Int)
    (ch : Choices) :
    stepFnIter 1 (σIn n seed l iv mv jv false)
      (.retV (.int b .uint64)
        (.strictK .lessCmp [.int a .uint64] [] envB2 mIfK)) ch
      = .ok (.retV (.bool (decide (a < b))) mIfK,
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- The SKIP arm: `s[j] < s[m]` false → the inner loop head. 5 steps. -/
theorem i_F_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (σIn n seed l iv mv jv false)
      (.retV (.bool false) mIfK) ch
      = .ok (innerHeadCfg, σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- The UPDATE arm: `m := j` → the inner loop head. 17 steps. -/
theorem i_T_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 17 (σIn n seed l iv mv jv false)
      (.retV (.bool true) mIfK) ch
      = .ok (innerHeadCfg,
          σIn n seed l iv (IntKind.normalize .int jv) jv false, ch) := by
  with_unfolding_all rfl

/-! ## Raw segments — the swap -/

/-- Swap phase 1: inner test false → break out of the inner loop →
both `assignMany` targets resolved → the first right-hand side's
(`s[m]`) apply point. 22 steps. -/
theorem sw_X1_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 22 (σIn n seed l iv mv jv false)
      (.retV (.bool false) innerCmpK) ch
      = .ok (.retV (.int mv .int)
            (.strictK .indexGet [sHandle n] [] envSw (swRhsK1 n iv mv)),
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 2: `s[m]` banked → the `s[i]` read's apply point.
5 steps. -/
theorem sw_X2_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (w : GoValue) (ch : Choices) :
    stepFnIter 5 (σIn n seed l iv mv jv false)
      (.retV w (swRhsK1 n iv mv)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sHandle n] [] envSw (swRhsK2 n iv mv w)),
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase 3: both right-hand sides banked → the store spine.
1 step. -/
theorem sw_X3_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (w w2 : GoValue) (ch : Choices) :
    stepFnIter 1 (σIn n seed l iv mv jv false)
      (.retV w2 (swRhsK2 n iv mv w)) ch
      = .ok (.next (.storeK [refIdx n iv, refIdx n mv] [w, w2]
            (.seqn #[]) envSw swTail),
          σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → the OUTER loop head. 5 steps. -/
theorem sw_X4_raw (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ch : Choices) :
    stepFnIter 5 (σIn n seed l iv mv jv false)
      (.next (.storeK [] [] (.seqn #[]) envSw swTail)) ch
      = .ok (outerHeadCfg, σIn n seed l iv mv jv false, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned element reads/stores at the tight state -/

/-- One element read at the tight in-pass state. -/
theorem stepFn_read_σIn {n seed : Nat} {l : List Int} {iv mv jv : Int}
    {ffIv : Bool} {k : Nat} {env : LocalEnv} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σIn n seed l iv mv jv ffIv)
      (.retV (.int ((k : Nat) : Int) .int)
        (.strictK .indexGet [sHandle n] [] env K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K,
          σIn n seed l iv mv jv ffIv, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice (lookup_σIn5 n seed l iv mv jv ffIv)
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One element store at the tight in-pass state. -/
theorem store_σIn {n seed : Nat} {l : List Int} {iv mv jv : Int}
    {ffIv : Bool} {k : Nat} {w : Int}
    (hk : k < n) (hlen : l.length = n)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget (σIn n seed l iv mv jv ffIv) (refIdx n ((k : Nat) : Int))
      (.int w .uint64)
      = .ok (σIn n seed (l.set k w) iv mv jv ffIv) := by
  have h := storeTarget_slice_u64 (a := ⟨5⟩) (off := 0) (len := n)
    (cap := n) (i := k) (n := n) (ik := .int) (l := l) (w := w)
    (lookup_σIn5 n seed l iv mv jv ffIv) (Nat.le_refl n) hk (by omega)
    hlen hl hw
  rw [Nat.zero_add] at h
  exact h

/-! ## The inner induction

Invariant at the exit-test delivery with counter `j`: the `m` cell
holds `minIdx l i (j - i - 1)` — the first minimum of `l[i..j)`. -/

/-- **The inner scan**: from the exit-test delivery at `j` — the `m`
cell holding `minIdx l i (j-i-1)` — the run reaches the exit-test's
`false` delivery at `n` with `m = minIdx l i (n - i - 1)`, within
`67·(n - j)` steps. `m` is an explicit parameter pinned by `hm` so the
two branches instantiate the follow-on segments directly (a `rw` at
the cast value would clobber the `j` occurrences). -/
theorem inner_loop (n seed : Nat) (l : List Int) (i : Nat)
    (hlen : l.length = n) (hcap : n ≤ 8) (hi : i < n) :
    ∀ μ j m, μ = n - j → i < j → j ≤ n →
    m = minIdx l i (j - i - 1) → ∀ ch : Choices,
    ∃ k, k ≤ 67 * (n - j) ∧
      stepFnIter k
        (σIn n seed l ((i : Nat) : Int)
          ((m : Nat) : Int) ((j : Nat) : Int) false)
        (.retV (.bool (decide (((j : Nat) : Int) < ((n : Nat) : Int))))
          innerCmpK) ch
        = .ok (.retV (.bool (decide
              (((n : Nat) : Int) < ((n : Nat) : Int)))) innerCmpK,
            σIn n seed l ((i : Nat) : Int)
              ((minIdx l i (n - i - 1) : Nat) : Int) ((n : Nat) : Int)
              false, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro j m hμ hij hjn hm ch
    rcases Nat.lt_or_ge j n with hlt | hge
    · -- one more inspected position
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hmle : m ≤ i + (j - i - 1) := hm ▸ minIdx_le l i _
      have hmn : m < n := by omega
      have hCA := i_CA_raw n seed l ((i : Nat) : Int)
        ((m : Nat) : Int) ((j : Nat) : Int) ch
      have hread1 := stepFn_read_σIn (n := n) (seed := seed) (l := l)
        (iv := ((i : Nat) : Int)) (mv := ((m : Nat) : Int))
        (jv := ((j : Nat) : Int)) (ffIv := false) (k := j)
        (env := envB2)
        (K := .strictK .lessCmp [] [.indexGet (.var "s") (.var "m")]
          envB2 mIfK) (ch := ch) hlt hlen
      have hCB := i_CB_raw n seed l ((i : Nat) : Int)
        ((m : Nat) : Int) ((j : Nat) : Int) (l.getD j 0) ch
      have hread2 := stepFn_read_σIn (n := n) (seed := seed) (l := l)
        (iv := ((i : Nat) : Int)) (mv := ((m : Nat) : Int))
        (jv := ((j : Nat) : Int)) (ffIv := false) (k := m)
        (env := envB2)
        (K := .strictK .lessCmp [.int (l.getD j 0) .uint64] [] envB2
          mIfK) (ch := ch) hmn hlen
      have hCC := i_CC_raw n seed l ((i : Nat) : Int)
        ((m : Nat) : Int) ((j : Nat) : Int)
        (l.getD j 0) (l.getD m 0) ch
      have h19 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain hCA (stepFnIter_one hread1)) hCB)
        (stepFnIter_one hread2)) hCC
      -- the branch IS the minIdx recursion
      have hstep := minIdx_step l hij
      have hj1 : (j + 1) - i - 1 = j - i := by omega
      by_cases hcmp : l.getD j 0 < l.getD m 0
      · -- m := j
        rw [decide_eq_true hcmp] at h19
        have hT := i_T_raw n seed l ((i : Nat) : Int)
          ((m : Nat) : Int) ((j : Nat) : Int) ch
        rw [inorm_of_range (v := ((j : Nat) : Int)) (by omega) (by omega)]
          at hT
        have hI1 := i_I1_raw n seed l ((i : Nat) : Int)
          ((j : Nat) : Int) ((j : Nat) : Int) ch
        rw [show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((j + 1 : Nat) : Int)) (by omega) (by omega),
          inorm_of_range (v := ((j + 1 : Nat) : Int)) (by omega) (by omega)]
          at hI1
        have hlen1 := stepFnIter_one (i_len_step n seed l ((i : Nat) : Int)
          ((j : Nat) : Int) ((j + 1 : Nat) : Int) ch)
        have hIB := i_IB_raw n seed l ((i : Nat) : Int)
          ((j : Nat) : Int) ((j + 1 : Nat) : Int) ch
        obtain ⟨k, hk, hrec⟩ := ih (n - (j + 1)) (by omega) (j + 1) j
          rfl (by omega) (by omega)
          (by rw [hj1, hstep, ← hm, if_pos hcmp]) ch
        refine ⟨19 + 17 + 29 + 1 + 1 + k, by omega, ?_⟩
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain h19 hT) hI1) hlen1) hIB)
          hrec
      · -- m unchanged
        rw [decide_eq_false hcmp] at h19
        have hF := i_F_raw n seed l ((i : Nat) : Int)
          ((m : Nat) : Int) ((j : Nat) : Int) ch
        have hI1 := i_I1_raw n seed l ((i : Nat) : Int)
          ((m : Nat) : Int) ((j : Nat) : Int) ch
        rw [show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((j + 1 : Nat) : Int)) (by omega) (by omega),
          inorm_of_range (v := ((j + 1 : Nat) : Int)) (by omega) (by omega)]
          at hI1
        have hlen1 := stepFnIter_one (i_len_step n seed l ((i : Nat) : Int)
          ((m : Nat) : Int) ((j + 1 : Nat) : Int) ch)
        have hIB := i_IB_raw n seed l ((i : Nat) : Int)
          ((m : Nat) : Int) ((j + 1 : Nat) : Int) ch
        obtain ⟨k, hk, hrec⟩ := ih (n - (j + 1)) (by omega) (j + 1) m
          rfl (by omega) (by omega)
          (by rw [hj1, hstep, ← hm, if_neg hcmp]) ch
        refine ⟨19 + 5 + 29 + 1 + 1 + k, by omega, ?_⟩
        exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain h19 hF) hI1) hlen1) hIB)
          hrec
    · -- j = n: already at the exit delivery
      have hje : j = n := by omega
      subst hje
      subst hm
      exact ⟨0, by omega, rfl⟩

/-! ## One composed pass -/

/-- **One outer pass at the tight placement**: from the outer test's
`true` delivery at `i` (16-cell state) to the NEXT outer test delivery
at `i + 1` (19-cell state), with the backing swapped at the suffix
minimum — within `67·n + 145` steps. -/
theorem pass_seg (n seed : Nat) (l : List Int) (i : Nat)
    (hlen : l.length = n) (hcap : n ≤ 8) (hi : i < n)
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (ch : Choices) :
    ∃ k, k ≤ 67 * n + 145 ∧
      stepFnIter k (σOut n seed l ((i : Nat) : Int) false)
        (.retV (.bool true) outerCmpK) ch
        = .ok (.retV (.bool (decide
              (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) outerCmpK,
            σIn n seed (swapList l i (minIdx l i (n - i - 1)))
              ((i + 1 : Nat) : Int)
              ((minIdx l i (n - i - 1) : Nat) : Int) ((n : Nat) : Int)
              false, ch) := by
  have hmle : minIdx l i (n - i - 1) ≤ i + (n - i - 1) := minIdx_le l i _
  have hmge : i ≤ minIdx l i (n - i - 1) := le_minIdx l i _
  have hmn : minIdx l i (n - i - 1) < n := by omega
  -- pass entry
  have hPA := passA_raw n seed l ((i : Nat) : Int) ch
  rw [inorm_of_range (v := ((i : Nat) : Int)) (by omega) (by omega),
    show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)]
    at hPA
  -- first inner dispatch
  have hI0 := i_I0_raw n seed l ((i : Nat) : Int) ((i : Nat) : Int)
    ((i + 1 : Nat) : Int) ch
  have hlen1 := stepFnIter_one (i_len_step n seed l ((i : Nat) : Int)
    ((i : Nat) : Int) ((i + 1 : Nat) : Int) ch)
  have hIB := i_IB_raw n seed l ((i : Nat) : Int) ((i : Nat) : Int)
    ((i + 1 : Nat) : Int) ch
  -- the inner scan, from j = i + 1 (m = i = minIdx l i 0)
  obtain ⟨k1, hk1, hscan⟩ := inner_loop n seed l i hlen hcap hi
    (n - (i + 1)) (i + 1) i rfl (by omega) (by omega)
    (by rw [show (i + 1) - i - 1 = 0 from by omega, minIdx]) ch
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hscan
  -- the swap
  have hX1 := sw_X1_raw n seed l ((i : Nat) : Int)
    ((minIdx l i (n - i - 1) : Nat) : Int) ((n : Nat) : Int) ch
  have hrd1 := stepFn_read_σIn (n := n) (seed := seed) (l := l)
    (iv := ((i : Nat) : Int))
    (mv := ((minIdx l i (n - i - 1) : Nat) : Int))
    (jv := ((n : Nat) : Int)) (ffIv := false)
    (k := minIdx l i (n - i - 1)) (env := envSw)
    (K := swRhsK1 n ((i : Nat) : Int)
      ((minIdx l i (n - i - 1) : Nat) : Int)) (ch := ch) hmn hlen
  have hX2 := sw_X2_raw n seed l ((i : Nat) : Int)
    ((minIdx l i (n - i - 1) : Nat) : Int) ((n : Nat) : Int)
    (.int (l.getD (minIdx l i (n - i - 1)) 0) .uint64) ch
  have hrd2 := stepFn_read_σIn (n := n) (seed := seed) (l := l)
    (iv := ((i : Nat) : Int))
    (mv := ((minIdx l i (n - i - 1) : Nat) : Int))
    (jv := ((n : Nat) : Int)) (ffIv := false) (k := i) (env := envSw)
    (K := swRhsK2 n ((i : Nat) : Int)
      ((minIdx l i (n - i - 1) : Nat) : Int)
      (.int (l.getD (minIdx l i (n - i - 1)) 0) .uint64)) (ch := ch)
    hi hlen
  have hX3 := sw_X3_raw n seed l ((i : Nat) : Int)
    ((minIdx l i (n - i - 1) : Nat) : Int) ((n : Nat) : Int)
    (.int (l.getD (minIdx l i (n - i - 1)) 0) .uint64)
    (.int (l.getD i 0) .uint64) ch
  -- store 1: s[i] := old s[m]
  have hst1 := store_σIn (n := n) (seed := seed) (l := l)
    (iv := ((i : Nat) : Int))
    (mv := ((minIdx l i (n - i - 1) : Nat) : Int))
    (jv := ((n : Nat) : Int)) (ffIv := false) (k := i)
    (w := l.getD (minIdx l i (n - i - 1)) 0) hi hlen hr
    (hr _ (getD_mem (by omega)))
  have hstep1 := stepFn_store_step
    (rs := [refIdx n ((minIdx l i (n - i - 1) : Nat) : Int)])
    (vs := [.int (l.getD i 0) .uint64]) (body := .seqn #[])
    (env := envSw) (k := swTail) (ch := ch) hst1
  -- store 2: s[m] := old s[i]
  have hr1 : ∀ x ∈ l.set i (l.getD (minIdx l i (n - i - 1)) 0),
      0 ≤ x ∧ x < 2 ^ 64 := by
    intro x hx
    rcases mem_set_of_mem hx with rfl | hx
    · exact hr _ (getD_mem (by omega))
    · exact hr x hx
  have hst2 := store_σIn (n := n) (seed := seed)
    (l := l.set i (l.getD (minIdx l i (n - i - 1)) 0))
    (iv := ((i : Nat) : Int))
    (mv := ((minIdx l i (n - i - 1) : Nat) : Int))
    (jv := ((n : Nat) : Int)) (ffIv := false)
    (k := minIdx l i (n - i - 1)) (w := l.getD i 0)
    (by omega) (by rw [List.length_set]; exact hlen) hr1
    (hr _ (getD_mem (by omega)))
  have hstep2 := stepFn_store_step (rs := []) (vs := [])
    (body := .seqn #[]) (env := envSw) (k := swTail) (ch := ch) hst2
  rw [show (l.set i (l.getD (minIdx l i (n - i - 1)) 0)).set
        (minIdx l i (n - i - 1)) (l.getD i 0)
      = swapList l i (minIdx l i (n - i - 1)) from rfl] at hstep2
  have hX4 := sw_X4_raw n seed (swapList l i (minIdx l i (n - i - 1)))
    ((i : Nat) : Int) ((minIdx l i (n - i - 1) : Nat) : Int)
    ((n : Nat) : Int) ch
  -- the next outer dispatch (19-cell state; tail-parametric)
  have hO1 : stepFnIter 29
      (σIn n seed (swapList l i (minIdx l i (n - i - 1)))
        ((i : Nat) : Int) ((minIdx l i (n - i - 1) : Nat) : Int)
        ((n : Nat) : Int) false) outerHeadCfg ch
      = .ok (.retV (sHandle n)
            (lenKO (IntKind.normalize .int (IntKind.normalize .int
              (((i : Nat) : Int) + 1)))),
          σIn n seed (swapList l i (minIdx l i (n - i - 1)))
            (IntKind.normalize .int (IntKind.normalize .int
              (((i : Nat) : Int) + 1)))
            ((minIdx l i (n - i - 1) : Nat) : Int) ((n : Nat) : Int)
            false, ch) :=
    o_A1_raw n seed (swapList l i (minIdx l i (n - i - 1)))
      ((i : Nat) : Int)
      [(.base ⟨16⟩, sint ((minIdx l i (n - i - 1) : Nat) : Int)),
       (.base ⟨17⟩, sint ((n : Nat) : Int)), (.base ⟨18⟩, sbool false)]
      19 ch
  rw [show (((i : Nat) : Int) + 1) = ((i + 1 : Nat) : Int) from by omega,
    inorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    inorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)]
    at hO1
  have hlenO : stepFn
      (σIn n seed (swapList l i (minIdx l i (n - i - 1)))
        ((i + 1 : Nat) : Int) ((minIdx l i (n - i - 1) : Nat) : Int)
        ((n : Nat) : Int) false)
      (.retV (sHandle n) (lenKO ((i + 1 : Nat) : Int))) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] []
            ([] :: envO) outerCmpK),
        σIn n seed (swapList l i (minIdx l i (n - i - 1)))
          ((i + 1 : Nat) : Int) ((minIdx l i (n - i - 1) : Nat) : Int)
          ((n : Nat) : Int) false, ch) :=
    o_len_step n seed (swapList l i (minIdx l i (n - i - 1)))
      ((i + 1 : Nat) : Int)
      [(.base ⟨16⟩, sint ((minIdx l i (n - i - 1) : Nat) : Int)),
       (.base ⟨17⟩, sint ((n : Nat) : Int)), (.base ⟨18⟩, sbool false)]
      19 ch
  have hOB : stepFnIter 1
      (σIn n seed (swapList l i (minIdx l i (n - i - 1)))
        ((i + 1 : Nat) : Int) ((minIdx l i (n - i - 1) : Nat) : Int)
        ((n : Nat) : Int) false)
      (.retV (.int ((n : Nat) : Int) .int)
        (.strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] []
          ([] :: envO) outerCmpK)) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) outerCmpK,
          σIn n seed (swapList l i (minIdx l i (n - i - 1)))
            ((i + 1 : Nat) : Int) ((minIdx l i (n - i - 1) : Nat) : Int)
            ((n : Nat) : Int) false, ch) :=
    o_OB_raw n seed (swapList l i (minIdx l i (n - i - 1)))
      ((i + 1 : Nat) : Int)
      [(.base ⟨16⟩, sint ((minIdx l i (n - i - 1) : Nat) : Int)),
       (.base ⟨17⟩, sint ((n : Nat) : Int)), (.base ⟨18⟩, sbool false)]
      19 ch
  refine ⟨50 + 25 + 1 + 1 + k1 + 22 + 1 + 5 + 1 + 1 + 1 + 1 + 5 + 29
    + 1 + 1, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            hPA hI0) hlen1) hIB) hscan) hX1)
              (stepFnIter_one hrd1)) hX2) (stepFnIter_one hrd2)) hX3)
                (stepFnIter_one hstep1)) (stepFnIter_one hstep2)) hX4)
                  hO1) (stepFnIter_one hlenO)) hOB

end GoLean.Examples.SelectionSort
