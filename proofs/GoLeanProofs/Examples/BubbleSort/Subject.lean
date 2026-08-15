import GoLeanProofs.Examples.BubbleSort.Copy

/-!
# BubbleSort — Subject (the nested loops, at the tight placement)

The `bubbleSort(s)` call: frame entry, the `end := len(s)` prologue,
and one outer PASS proven at the TIGHT canonical placement (`swapped`
at 16, the inner counter at 17, the inner flag at 18). The machine
re-allocates those three cells on every outer pass, so a pass is
proven ONCE here and transferred to the true (garbage-laden) placement
by the frame layer (`BubbleSort.Frame`).

Machine ↔ pure interface: at inner counter `i = m+1` the backing list
is `passL l m` and the `swapped` cell is `passB l m` (`Pure.lean`).
The inner induction runs to the INNER EXIT and delivers `!swapped` at
its `if` continuation; the pass lemmas then split on the flag —
`bPass_swapped` ends at the next outer exit-test delivery,
`bPass_early` at the post-call anchor (`.next bAfterCallK`).

Per-segment step counts (probe-measured, re-checked by `rfl`):

| phase | steps |
|---|---|
| call delivered → `enterFrame` → `len(s)` apply | 14 |
| `len` apply → outer head | 1 + 18 |
| outer dispatch (first / later) | 25 / 29 |
| outer exit → the post-call anchor | 8 |
| pass entry (3 allocations) → inner head | 46 |
| inner dispatch (first / later) | 25 / 29 |
| condition reads (split at both `s[·]` applies) | 15 + 1 + 5 + 1 + 1 |
| no-swap arm → inner head | 5 |
| swap arm (2 reads, 2 stores, `swapped = true`) | 22+1+9+1+1+2+17 |
| inner exit → the `!swapped` delivery | 11 |
| `!swapped` false → outer head | 5 |
| `!swapped` true → the post-call anchor (early return) | 12 |
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The parked pre-subject heap fronts -/

/-- The copy-loop state at its PARKED final values. -/
def bHeapCpP (n seed : Nat) (l : List Int) : Heap :=
  bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n l (bubPre n seed)
    (bubX n seed) ((n : Nat) : Int) ((n : Nat) : Int) false

/-- Mid-prologue: the `s` parameter bound, `end` declared at its
default. -/
def bHeapPre1 (n seed : Nat) (l : List Int) : Heap :=
  bHeapCpP n seed l ++ [(.base ⟨13⟩, bHandle n), (.base ⟨14⟩, bint 0)]

/-! ## Raw segments — frame entry and prologue -/

/-- The call: argument delivered → `enterFrame` (the one
program-consulting step) → `end` declared → the `len(s)` apply point.
14 steps. -/
theorem b_enter_raw (n seed : Nat) (l : List Int) (ch : Choices) :
    stepFnIter 14 (σB (bHeapCpP n seed l) 13)
      (.retV (bSliceS n) bCallArgsK) ch
      = .ok (.retV (bSliceS n) bLenKB,
          σB (bHeapPre1 n seed l) 15, ch) := by
  with_unfolding_all rfl

/-- Prologue B: the length delivered → `end := len(s)`, the first-pass
flag, the outer loop head. 18 steps. -/
theorem b_preB_raw (n seed : Nat) (l : List Int) (ch : Choices) :
    stepFnIter 18 (σB (bHeapPre1 n seed l) 15)
      (.retV (.int ((n : Nat) : Int) .int) bEndRhsK) ch
      = .ok (bOuterHeadCfg,
          σBOut n seed l (IntKind.normalize .int ((n : Nat) : Int)) true,
          ch) := by
  with_unfolding_all rfl

/-! ## Raw segments — the outer loop -/

theorem bO_A0_raw (n seed : Nat) (l : List Int) (endv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 25 (σBOutT n seed l endv true tail na) bOuterHeadCfg ch
      = .ok (.retV (.bool (decide (1 < endv))) bOuterCmpK,
          σBOutT n seed l endv false tail na, ch) := by
  with_unfolding_all rfl

theorem bO_A1_raw (n seed : Nat) (l : List Int) (endv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 29 (σBOutT n seed l endv false tail na) bOuterHeadCfg ch
      = .ok (.retV (.bool (decide
            (1 < IntKind.normalize .int (IntKind.normalize .int (endv - 1)))))
            bOuterCmpK,
          σBOutT n seed l
            (IntKind.normalize .int (IntKind.normalize .int (endv - 1)))
            false tail na, ch) := by
  with_unfolding_all rfl

/-- Outer exit: `end ≤ 1` → break unwinding, subject frame exit → the
post-call anchor. State untouched. 8 steps. -/
theorem bO_exit_raw (n seed : Nat) (l : List Int) (endv : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 8 (σBOutT n seed l endv false tail na)
      (.retV (.bool false) bOuterCmpK) ch
      = .ok (.next bAfterCallK, σBOutT n seed l endv false tail na,
          ch) := by
  with_unfolding_all rfl

/-- Pass entry: outer test true → `swapped := false` at 16, `i := 1`
at 17, the inner `$forFirst` at 18 (allocations — TIGHT placement
only) → the inner loop head. 46 steps. -/
theorem bP_entry_raw (n seed : Nat) (l : List Int) (endv : Int)
    (ch : Choices) :
    stepFnIter 46 (σBOut n seed l endv false)
      (.retV (.bool true) bOuterCmpK) ch
      = .ok (bInnerHeadCfg, σBIn n seed l endv 1 false true, ch) := by
  with_unfolding_all rfl

/-! ## Raw segments — the inner loop -/

theorem bI_A0_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 25 (σBIn n seed l endv iv swv true) bInnerHeadCfg ch
      = .ok (.retV (.bool (decide (iv < endv))) bInnerCmpK,
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

theorem bI_A1_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 29 (σBIn n seed l endv iv swv false) bInnerHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1))
              < endv))) bInnerCmpK,
          σBIn n seed l endv
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            swv false, ch) := by
  with_unfolding_all rfl

/-- Condition phase A: test true → the `s[i-1]` read's apply point.
15 steps. -/
theorem bI_B1_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 15 (σBIn n seed l endv iv swv false)
      (.retV (.bool true) bInnerCmpK) ch
      = .ok (.retV (.int (IntKind.normalize .int (iv - 1)) .int)
            (bGtK1 n),
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- Condition phase B: `s[i-1]` banked → the `s[i]` read's apply
point. 5 steps. -/
theorem bI_B2_raw (n seed : Nat) (l : List Int) (endv iv a : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 5 (σBIn n seed l endv iv swv false)
      (.retV (.int a .uint64)
        (.strictK .greaterCmp [] [.indexGet (.var "s") (.var "i")] bEnvC
          bSwIfK)) ch
      = .ok (.retV (.int iv .int) (bGtK2 n a),
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- Condition phase C: both elements banked → the `>` verdict. 1
step. -/
theorem bI_B3_raw (n seed : Nat) (l : List Int) (endv iv a b : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 1 (σBIn n seed l endv iv swv false)
      (.retV (.int b .uint64)
        (.strictK .greaterCmp [.int a .uint64] [] bEnvC bSwIfK)) ch
      = .ok (.retV (.bool (decide (b < a))) bSwIfK,
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- The NO-SWAP arm: the pair is ordered → back to the inner head.
5 steps. -/
theorem bI_ns_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 5 (σBIn n seed l endv iv swv false)
      (.retV (.bool false) bSwIfK) ch
      = .ok (bInnerHeadCfg, σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase A: the `if` fires → both target refs resolved → the
first rhs read's (`s[i]`) apply point. 22 steps. -/
theorem bSw_A_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 22 (σBIn n seed l endv iv swv false)
      (.retV (.bool true) bSwIfK) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [bSliceS n] [] bEnvSw2
              (bRhsK1 n (IntKind.normalize .int (iv - 1)) iv)),
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase B: the first rhs value banked → the second rhs read's
(`s[i-1]`) apply point. 9 steps. -/
theorem bSw_B_raw (n seed : Nat) (l : List Int) (endv iv idx1 : Int)
    (swv : Bool) (wj : GoValue) (ch : Choices) :
    stepFnIter 9 (σBIn n seed l endv iv swv false)
      (.retV wj (bRhsK1 n idx1 iv)) ch
      = .ok (.retV (.int (IntKind.normalize .int (iv - 1)) .int)
            (.strictK .indexGet [bSliceS n] [] bEnvSw2
              (bRhsK2 n idx1 iv wj)),
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- Swap phase C: both rhs values banked → the two stores begin.
1 step. -/
theorem bSw_C_raw (n seed : Nat) (l : List Int) (endv iv idx1 : Int)
    (swv : Bool) (wj wi : GoValue) (ch : Choices) :
    stepFnIter 1 (σBIn n seed l endv iv swv false)
      (.retV wi (bRhsK2 n idx1 iv wj)) ch
      = .ok (.next (.storeK [bRefj n idx1, bRefj n iv] [wj, wi]
            (.seqn #[]) bEnvSw2 bSwTail),
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- Swap tail: stores done → `swapped = true` (raw: cell 16 at the
tight placement) → the inner head. 17 steps. -/
theorem bSw_D_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 17 (σBIn n seed l endv iv swv false)
      (.next (.storeK [] [] (.seqn #[]) bEnvSw2 bSwTail)) ch
      = .ok (bInnerHeadCfg, σBIn n seed l endv iv true false, ch) := by
  with_unfolding_all rfl

/-- Inner exit: `i ≥ end` → break unwinds the inner loop → the
`!swapped` verdict delivered (the `not` op is Bool-level, raw).
11 steps. -/
theorem bI_X_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 11 (σBIn n seed l endv iv swv false)
      (.retV (.bool false) bInnerCmpK) ch
      = .ok (.retV (.bool (!swv)) bNotIfK,
          σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-- The EARLY RETURN: `!swapped` is true → `return` unwinds both loops
and the frame → the post-call anchor. 12 steps. -/
theorem bRet_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 12 (σBIn n seed l endv iv swv false)
      (.retV (.bool true) bNotIfK) ch
      = .ok (.next bAfterCallK, σBIn n seed l endv iv swv false,
          ch) := by
  with_unfolding_all rfl

/-- The continue arm: `!swapped` is false → the outer loop head.
5 steps. -/
theorem bCont_raw (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv : Bool) (ch : Choices) :
    stepFnIter 5 (σBIn n seed l endv iv swv false)
      (.retV (.bool false) bNotIfK) ch
      = .ok (bOuterHeadCfg, σBIn n seed l endv iv swv false, ch) := by
  with_unfolding_all rfl

/-! ## Cleaned per-element facts at the tight in-pass state -/

/-- One element read at the tight in-pass state. -/
theorem stepFn_read_σBIn {n seed : Nat} {l : List Int} {endv iv : Int}
    {swv : Bool} {k : Nat} {env : LocalEnv} {K : Cont} {ch : Choices}
    (hk : k < n) (hlen : l.length = n) :
    stepFn (σBIn n seed l endv iv swv false)
      (.retV (.int ((k : Nat) : Int) .int)
        (.strictK .indexGet [bSliceS n] [] env K)) ch
      = .ok (.retV (.int (l.getD k 0) .uint64) K,
          σBIn n seed l endv iv swv false, ch) :=
  stepFn_strict_apply
    (applyStrictOp_indexGet_slice
      (lookup_σBIn5 n seed l endv iv swv false)
      (Nat.le_refl n) hk
      (by rw [Nat.zero_add]; exact getElem?_mapU l k (by omega)))

/-- One element store at the tight in-pass state. -/
theorem store_σBIn {n seed : Nat} {l : List Int} {endv iv : Int}
    {swv : Bool} {k : Nat} {w : Int}
    (hk : k < n) (hlen : l.length = n)
    (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget (σBIn n seed l endv iv swv false)
      (bRefj n ((k : Nat) : Int)) (.int w .uint64)
      = .ok (σBIn n seed (l.set k w) endv iv swv false) := by
  have h := storeTarget_slice_u64 (a := ⟨5⟩) (off := 0) (len := n)
    (cap := n) (i := k) (n := n) (ik := .int) (l := l) (w := w)
    (lookup_σBIn5 n seed l endv iv swv false)
    (Nat.le_refl n) hk (by omega) hlen hl hw
  rw [Nat.zero_add] at h
  exact h

/-! ## The inner induction

At counter `iv = m+1` the list is `passL l0 m` and the flag is
`passB l0 m`; the run continues to the INNER EXIT and delivers
`!(passB l0 (e-1))` at the `!swapped` continuation. -/

theorem bInner_loop (n seed : Nat) (l0 : List Int) (e : Nat)
    (hn : n < 2 ^ 63) (hln : l0.length = n)
    (he : e ≤ n) (hr : ∀ x ∈ l0, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ μ m, μ = e - (m + 1) → m + 1 ≤ e → ∀ ch : Choices,
    ∃ k, k ≤ 105 * μ + 11 ∧
      stepFnIter k
        (σBIn n seed (passL l0 m) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) (passB l0 m) false)
        (.retV (.bool (decide
          (((m + 1 : Nat) : Int) < ((e : Nat) : Int)))) bInnerCmpK) ch
        = .ok (.retV (.bool (!(passB l0 (e - 1)))) bNotIfK,
            σBIn n seed (passL l0 (e - 1)) ((e : Nat) : Int)
              ((e : Nat) : Int) (passB l0 (e - 1)) false, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hμ hme ch
    have hlen : (passL l0 m).length = n := by
      rw [passL_length, hln]
    have hrL : ∀ x ∈ passL l0 m, 0 ≤ x ∧ x < 2 ^ 64 := fun x hx =>
      hr x (passL_mem (by rw [hln]; omega) hx)
    rcases Nat.lt_or_ge (m + 1) e with hlt | hge
    · -- one more iteration
      rw [show (decide (((m + 1 : Nat) : Int) < ((e : Nat) : Int)))
          = true from decide_eq_true (by exact_mod_cast hlt)]
      have hm1n : m + 1 < n := by omega
      -- condition reads
      have hB1 := bI_B1_raw n seed (passL l0 m) ((e : Nat) : Int)
        ((m + 1 : Nat) : Int) (passB l0 m) ch
      rw [show (((m + 1 : Nat) : Int) - 1) = ((m : Nat) : Int) from by
          omega,
        inorm_of_range (v := ((m : Nat) : Int)) (by omega)
          (by exact_mod_cast (by omega : m < 2 ^ 63))] at hB1
      have hread1 := stepFn_read_σBIn (n := n) (seed := seed)
        (l := passL l0 m) (endv := ((e : Nat) : Int))
        (iv := ((m + 1 : Nat) : Int)) (swv := passB l0 m) (k := m)
        (env := bEnvC)
        (K := .strictK .greaterCmp [] [.indexGet (.var "s") (.var "i")]
          bEnvC bSwIfK) (ch := ch) (by omega) hlen
      have hB2 := bI_B2_raw n seed (passL l0 m) ((e : Nat) : Int)
        ((m + 1 : Nat) : Int) ((passL l0 m).getD m 0) (passB l0 m) ch
      have hread2raw := stepFn_read_σBIn (n := n) (seed := seed)
        (l := passL l0 m) (endv := ((e : Nat) : Int))
        (iv := ((m + 1 : Nat) : Int)) (swv := passB l0 m) (k := m + 1)
        (env := bEnvC)
        (K := .strictK .greaterCmp
          [.int ((passL l0 m).getD m 0) .uint64] [] bEnvC bSwIfK)
        (ch := ch) (by omega) hlen
      have hB3 := bI_B3_raw n seed (passL l0 m) ((e : Nat) : Int)
        ((m + 1 : Nat) : Int) ((passL l0 m).getD m 0)
        ((passL l0 m).getD (m + 1) 0) (passB l0 m) ch
      have h23 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain hB1 (stepFnIter_one hread1)) hB2)
        (stepFnIter_one hread2raw)) hB3
      -- the verdict is the pure step's flag
      have hverdict : (decide ((passL l0 m).getD (m + 1) 0
            < (passL l0 m).getD m 0))
          = bstepB (passL l0 m) (m + 1) := by
        rw [bstepB, Nat.succ_sub_one]
      rw [hverdict] at h23
      by_cases hfire : bstepB (passL l0 m) (m + 1) = true
      · -- SWAP
        rw [hfire] at h23
        have hcmp : (passL l0 m).getD (m + 1) 0
            < (passL l0 m).getD m 0 := by
          rw [bstepB, Nat.succ_sub_one, decide_eq_true_iff] at hfire
          exact hfire
        have hSA := bSw_A_raw n seed (passL l0 m) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) (passB l0 m) ch
        rw [show (((m + 1 : Nat) : Int) - 1) = ((m : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((m : Nat) : Int)) (by omega)
            (by exact_mod_cast (by omega : m < 2 ^ 63))] at hSA
        have hgetj := stepFn_read_σBIn (n := n) (seed := seed)
          (l := passL l0 m) (endv := ((e : Nat) : Int))
          (iv := ((m + 1 : Nat) : Int)) (swv := passB l0 m) (k := m + 1)
          (env := bEnvSw2)
          (K := bRhsK1 n ((m : Nat) : Int) ((m + 1 : Nat) : Int))
          (ch := ch) (by omega) hlen
        have hSB := bSw_B_raw n seed (passL l0 m) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) ((m : Nat) : Int) (passB l0 m)
          (.int ((passL l0 m).getD (m + 1) 0) .uint64) ch
        rw [show (((m + 1 : Nat) : Int) - 1) = ((m : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((m : Nat) : Int)) (by omega)
            (by exact_mod_cast (by omega : m < 2 ^ 63))] at hSB
        have hgetj1 := stepFn_read_σBIn (n := n) (seed := seed)
          (l := passL l0 m) (endv := ((e : Nat) : Int))
          (iv := ((m + 1 : Nat) : Int)) (swv := passB l0 m) (k := m)
          (env := bEnvSw2)
          (K := bRhsK2 n ((m : Nat) : Int) ((m + 1 : Nat) : Int)
            (.int ((passL l0 m).getD (m + 1) 0) .uint64))
          (ch := ch) (by omega) hlen
        have hSC := bSw_C_raw n seed (passL l0 m) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) ((m : Nat) : Int) (passB l0 m)
          (.int ((passL l0 m).getD (m + 1) 0) .uint64)
          (.int ((passL l0 m).getD m 0) .uint64) ch
        -- store 1: s[m] := old s[m+1]
        have hst1 := store_σBIn (n := n) (seed := seed)
          (l := passL l0 m) (endv := ((e : Nat) : Int))
          (iv := ((m + 1 : Nat) : Int)) (swv := passB l0 m) (k := m)
          (w := (passL l0 m).getD (m + 1) 0) (by omega) hlen hrL
          (hrL _ (getD_mem (by rw [hlen]; omega)))
        have hstep1 := stepFn_store_step
          (rs := [bRefj n ((m + 1 : Nat) : Int)])
          (vs := [.int ((passL l0 m).getD m 0) .uint64])
          (body := .seqn #[]) (env := bEnvSw2) (k := bSwTail) (ch := ch)
          hst1
        -- store 2: s[m+1] := old s[m]
        have hrL1 : ∀ x ∈ (passL l0 m).set m ((passL l0 m).getD (m + 1) 0),
            0 ≤ x ∧ x < 2 ^ 64 := by
          intro x hx
          rcases mem_set_of_mem hx with rfl | hx
          · exact hrL _ (getD_mem (by rw [hlen]; omega))
          · exact hrL x hx
        have hst2 := store_σBIn (n := n) (seed := seed)
          (l := (passL l0 m).set m ((passL l0 m).getD (m + 1) 0))
          (endv := ((e : Nat) : Int)) (iv := ((m + 1 : Nat) : Int))
          (swv := passB l0 m) (k := m + 1)
          (w := (passL l0 m).getD m 0) (by omega)
          (by rw [List.length_set]; exact hlen) hrL1
          (hrL _ (getD_mem (by rw [hlen]; omega)))
        have hstep2 := stepFn_store_step (rs := []) (vs := [])
          (body := .seqn #[]) (env := bEnvSw2) (k := bSwTail) (ch := ch)
          hst2
        -- the surgery: the two sets ARE the pure step
        have hsurg : ((passL l0 m).set m ((passL l0 m).getD (m + 1) 0)).set
            (m + 1) ((passL l0 m).getD m 0)
            = passL l0 (m + 1) := by
          rw [passL, bstepL, Nat.succ_sub_one, if_pos hcmp]
        rw [hsurg] at hstep2
        have hSD := bSw_D_raw n seed (passL l0 (m + 1)) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) (passB l0 m) ch
        -- the pass flag after a fired step is true
        have hflag : passB l0 (m + 1) = true := by
          rw [passB, hfire, Bool.or_true]
        -- next dispatch
        have hA1 := bI_A1_raw n seed (passL l0 (m + 1)) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) true ch
        rw [show ((m + 1 : Nat) : Int) + 1 = ((m + 2 : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega)
            (by exact_mod_cast (by omega : m + 2 < 2 ^ 63)),
          inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega)
            (by exact_mod_cast (by omega : m + 2 < 2 ^ 63))] at hA1
        obtain ⟨k, hk, hrec⟩ := ih (e - (m + 2)) (by omega) (m + 1) rfl
          (by omega) ch
        rw [← hflag] at hSD hA1
        refine ⟨105 + k, by omega, ?_⟩
        have hsw := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            (stepFnIter_chain h23 hSA) (stepFnIter_one hgetj)) hSB)
            (stepFnIter_one hgetj1)) hSC) (stepFnIter_one hstep1))
          (stepFnIter_one hstep2)
        exact stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hsw hSD) hA1) hrec
      · -- NO SWAP
        have hfire' : bstepB (passL l0 m) (m + 1) = false :=
          Bool.eq_false_iff.mpr hfire
        rw [hfire'] at h23
        have hid : passL l0 (m + 1) = passL l0 m := by
          rw [passL, bstepL, Nat.succ_sub_one, if_neg]
          rw [bstepB, Nat.succ_sub_one, decide_eq_false_iff_not] at hfire'
          exact hfire'
        have hflag : passB l0 (m + 1) = passB l0 m := by
          rw [passB, hfire', Bool.or_false]
        have hns := bI_ns_raw n seed (passL l0 m) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) (passB l0 m) ch
        have hA1 := bI_A1_raw n seed (passL l0 m) ((e : Nat) : Int)
          ((m + 1 : Nat) : Int) (passB l0 m) ch
        rw [show ((m + 1 : Nat) : Int) + 1 = ((m + 2 : Nat) : Int) from by
            omega,
          inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega)
            (by exact_mod_cast (by omega : m + 2 < 2 ^ 63)),
          inorm_of_range (v := ((m + 2 : Nat) : Int)) (by omega)
            (by exact_mod_cast (by omega : m + 2 < 2 ^ 63))] at hA1
        obtain ⟨k, hk, hrec⟩ := ih (e - (m + 2)) (by omega) (m + 1) rfl
          (by omega) ch
        rw [hid, hflag] at hrec
        refine ⟨57 + k, by omega, ?_⟩
        exact stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain h23 hns) hA1) hrec
    · -- the inner exit
      have hme' : m + 1 = e := by omega
      rw [show (decide (((m + 1 : Nat) : Int) < ((e : Nat) : Int)))
          = false from decide_eq_false (by exact_mod_cast (by omega :
            ¬ (m + 1 < e)))]
      have hm' : e - 1 = m := by omega
      rw [hm', ← hme']
      exact ⟨11, by omega, bI_X_raw n seed (passL l0 m)
        ((m + 1 : Nat) : Int) ((m + 1 : Nat) : Int) (passB l0 m) ch⟩

/-! ## One pass, composed (two exits) -/

/-- **A swapped pass at the tight placement**: outer test true at the
16-cell state, the pass runs, at least one swap fired → the NEXT outer
exit-test delivery at the 19-cell state, with `end` decremented.
`k ≤ 105·e + 116`. -/
theorem bPass_swapped (n seed : Nat) (l : List Int) (e : Nat)
    (hn : n < 2 ^ 63) (hln : l.length = n)
    (h2 : 2 ≤ e) (he : e ≤ n) (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64)
    (hsw : passB l (e - 1) = true) (ch : Choices) :
    ∃ k, k ≤ 105 * e + 116 ∧
      stepFnIter k (σBOut n seed l ((e : Nat) : Int) false)
        (.retV (.bool true) bOuterCmpK) ch
        = .ok (.retV (.bool (decide (1 < ((e - 1 : Nat) : Int))))
              bOuterCmpK,
            σBIn n seed (passL l (e - 1)) ((e - 1 : Nat) : Int)
              ((e : Nat) : Int) true false, ch) := by
  have hPA := bP_entry_raw n seed l ((e : Nat) : Int) ch
  have hI0 := bI_A0_raw n seed l ((e : Nat) : Int) 1 false ch
  obtain ⟨kin, hkin, hinner⟩ := bInner_loop n seed l e hn hln he hr
    (e - (0 + 1)) 0 rfl (by omega) ch
  rw [hsw] at hinner
  have hC := bCont_raw n seed (passL l (e - 1)) ((e : Nat) : Int)
    ((e : Nat) : Int) true ch
  have hA1 : stepFnIter 29
      (σBIn n seed (passL l (e - 1)) ((e : Nat) : Int)
        ((e : Nat) : Int) true false) bOuterHeadCfg ch
      = .ok (.retV (.bool (decide
            (1 < IntKind.normalize .int (IntKind.normalize .int
              (((e : Nat) : Int) - 1))))) bOuterCmpK,
          σBIn n seed (passL l (e - 1))
            (IntKind.normalize .int (IntKind.normalize .int
              (((e : Nat) : Int) - 1)))
            ((e : Nat) : Int) true false, ch) :=
    bO_A1_raw n seed (passL l (e - 1)) ((e : Nat) : Int)
      [(.base ⟨16⟩, bbool true), (.base ⟨17⟩, bint ((e : Nat) : Int)),
       (.base ⟨18⟩, bbool false)] 19 ch
  rw [show (((e : Nat) : Int) - 1) = ((e - 1 : Nat) : Int) from by omega,
    inorm_of_range (v := ((e - 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : e - 1 < 2 ^ 63)),
    inorm_of_range (v := ((e - 1 : Nat) : Int)) (by omega)
      (by exact_mod_cast (by omega : e - 1 < 2 ^ 63))] at hA1
  refine ⟨46 + 25 + kin + 5 + 29, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hPA hI0) hinner) hC) hA1

/-- **A swap-free pass at the tight placement — the EARLY RETURN**:
outer test true, the pass runs with no swap → the post-call anchor.
`k ≤ 105·e + 94`. -/
theorem bPass_early (n seed : Nat) (l : List Int) (e : Nat)
    (hn : n < 2 ^ 63) (hln : l.length = n)
    (h2 : 2 ≤ e) (he : e ≤ n) (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64)
    (hsw : passB l (e - 1) = false) (ch : Choices) :
    ∃ k, k ≤ 105 * e + 94 ∧
      stepFnIter k (σBOut n seed l ((e : Nat) : Int) false)
        (.retV (.bool true) bOuterCmpK) ch
        = .ok (.next bAfterCallK,
            σBIn n seed l ((e : Nat) : Int) ((e : Nat) : Int) false
              false, ch) := by
  have hPA := bP_entry_raw n seed l ((e : Nat) : Int) ch
  have hI0 := bI_A0_raw n seed l ((e : Nat) : Int) 1 false ch
  obtain ⟨kin, hkin, hinner⟩ := bInner_loop n seed l e hn hln he hr
    (e - (0 + 1)) 0 rfl (by omega) ch
  rw [hsw, passB_false_id hsw] at hinner
  have hR := bRet_raw n seed l ((e : Nat) : Int) ((e : Nat) : Int)
    false ch
  refine ⟨46 + 25 + kin + 12, by omega, ?_⟩
  exact stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hPA hI0) hinner) hR

end GoLean.Examples.BubbleSort
