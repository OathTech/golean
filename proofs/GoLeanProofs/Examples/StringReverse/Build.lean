import GoLeanProofs.Examples.StringReverse.Machine

/-!
# StringReverse — the `buildStr` phase

Entry (the harness prologue and the `buildStr(n, seed)` call), the
build loop — `out += string(rune(97 + (seed+i)%26))` — and the exit
into the `reverseString` call's argument point.

Per-segment step counts (probe-measured with `.tmp/Probe.lean`, then
re-checked by `rfl` here): entry → args delivered 10; frame prologue
43; dispatch first/later 25/29; one iteration 65; exit → next call's
argument delivered 33.

The loop's per-iteration conditioned steps are PURE facts — the `%`
(kit) and the ASCII `string(rune(·))` (Machine) — because a Go string
is a value, not a heap object; everything else in the iteration is
`with_unfolding_all rfl`.
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw segments — PROGRAM-generic throughout -/

/-- Entry: body start → the `buildStr` call's second argument
delivered. 10 steps. -/
theorem s_E1_raw (σ : ExecState) (nv sv : Int) (ch : Choices) :
    stepFnIter 10 (sSt σ (sHeap0 nv sv) 5) sHC0 ch
      = .ok (.retV (.int sv .uint64) (buCallK1 nv),
          sSt σ (sHeapPre nv sv) 6, ch) := by
  with_unfolding_all rfl

/-- The `buildStr` frame prologue: `out := ""`, `i := 0`, the
first-pass flag → the loop head. 43 steps. -/
theorem bu_pro_raw (σ : ExecState) (nv sv bnv bsv : Int) (ch : Choices) :
    stepFnIter 43 (sSt σ (sHeapBF nv sv bnv bsv) 9)
      (.exec buildStrFunc.body buFrameEnv buFrameK) ch
      = .ok (buHeadCfg,
          sSt σ (sHeapBu nv sv bnv bsv GoString.empty 0 true) 12, ch) := by
  with_unfolding_all rfl

/-- Build dispatch, first pass: flag true → the exit test delivered.
25 steps. -/
theorem bu_A0_raw (σ : ExecState) (nv sv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 25 (sSt σ (sHeapBu nv sv bnv bsv ov iv true) 12) buHeadCfg ch
      = .ok (.retV (.bool (decide (iv < bnv))) buCmpK,
          sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12, ch) := by
  with_unfolding_all rfl

/-- Build dispatch, later passes: `i++`, exit test delivered.
29 steps. -/
theorem bu_A1_raw (σ : ExecState) (nv sv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 29 (sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12) buHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < bnv))) buCmpK,
          sSt σ (sHeapBu nv sv bnv bsv ov
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false) 12, ch) := by
  with_unfolding_all rfl

/-- Build body A: test true → the `%` apply point (the wrapped
`seed+i` sum banked, the divisor delivered). 24 steps. -/
theorem bu_B1_raw (σ : ExecState) (nv sv bnv bsv : Int) (ov : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 24 (sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12)
      (.retV (.bool true) buCmpK) ch
      = .ok (.retV (.int 26 .uint64)
            (buModK ov (IntKind.normalize .uint64 (bsv + iv))),
          sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12, ch) := by
  with_unfolding_all rfl

/-- Build body B: the `%` result delivered → `97 + r`, the `rune`
conversion → the `string(rune(·))` apply point. 2 steps. -/
theorem bu_B2_raw (σ : ExecState) (nv sv bnv bsv : Int) (ov : GoString)
    (iv rv : Int) (ch : Choices) :
    stepFnIter 2 (sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12)
      (.retV (.int rv .uint64) (buA97K ov)) ch
      = .ok (.retV (.int (IntKind.normalize .int32
              (IntKind.normalize .uint64 (97 + rv))) .int32) (buRuneK ov),
          sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12, ch) := by
  with_unfolding_all rfl

/-- Build body C: the one-byte string delivered → the append, the
store, the loop head. 8 steps. -/
theorem bu_B3_raw (σ : ExecState) (nv sv bnv bsv : Int) (ov w : GoString)
    (iv : Int) (ch : Choices) :
    stepFnIter 8 (sSt σ (sHeapBu nv sv bnv bsv ov iv false) 12)
      (.retV (.string w) (buAppK ov)) ch
      = .ok (buHeadCfg,
          sSt σ (sHeapBu nv sv bnv bsv (GoString.append ov w) iv false) 12,
          ch) := by
  with_unfolding_all rfl

/-- Build exit: test false → `$res0 := out`, the frame pop into `pre`,
`var post`, and the `reverseString(pre)` argument delivered. 33 steps. -/
theorem bu_X_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (iv : Int) (ch : Choices) :
    stepFnIter 33 (sSt σ (sHeapBu nv sv bnv bsv (gs l) iv false) 12)
      (.retV (.bool false) buCmpK) ch
      = .ok (.retV (.string (gs l)) revCallK0,
          sSt σ (sHeapBX nv sv bnv bsv l iv) 13, ch) := by
  with_unfolding_all rfl

/-! ## One iteration, cleaned -/

/-- One build iteration from the exit test's true delivery at `i`:
65 steps materialize the next family byte. -/
theorem bu_iter (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 64)
    (i : Nat) (hi : i < n) (ch : Choices) :
    stepFnIter 65
      (sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (strFamily i seed)) ((i : Nat) : Int) false) 12)
      (.retV (.bool true) buCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) buCmpK,
          sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
            ((n : Nat) : Int) ((seed : Nat) : Int)
            (gs (strFamily (i + 1) seed)) ((i + 1 : Nat) : Int) false) 12,
          ch) := by
  have hB1 := bu_B1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (strFamily i seed))
    ((i : Nat) : Int) ch
  rw [unorm_add_nat seed i] at hB1
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int (((seed + i) % 2 ^ 64 : Nat) : Int) .uint64])
    (env := buEnv2) (k := buA97K (gs (strFamily i seed))) (ch := ch)
    (applyStrictOp_mod_u64
      (σ := sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((n : Nat) : Int) ((seed : Nat) : Int) (gs (strFamily i seed))
        ((i : Nat) : Int) false) 12)
      (a := (seed + i) % 2 ^ 64) (b := 26) (by omega) (by omega)))
  have hB2 := bu_B2_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (strFamily i seed))
    ((i : Nat) : Int) ((((seed + i) % 2 ^ 64) % 26 : Nat) : Int) ch
  have hbyte : strByte seed i < 128 := strByte_lt seed i
  rw [show (97 : Int) + ((((seed + i) % 2 ^ 64) % 26 : Nat) : Int)
        = ((strByte seed i : Nat) : Int) from by
      simp only [strByte]; omega,
    unorm_nat_of_lt (by omega : strByte seed i < 2 ^ 64),
    i32norm_nat_of_lt (by omega : strByte seed i < 2 ^ 31)] at hB2
  have hrune := stepFnIter_one (stepFn_strict_apply
    (done := []) (env := buEnv2) (k := buAppK (gs (strFamily i seed)))
    (ch := ch)
    (applyStrictOp_stringFromRune_ascii
      (σ := sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((n : Nat) : Int) ((seed : Nat) : Int) (gs (strFamily i seed))
        ((i : Nat) : Int) false) 12)
      (c := strByte seed i) (ik := .int32) hbyte))
  have hB3 := bu_B3_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (strFamily i seed))
    (gs [UInt8.ofNat (strByte seed i)]) ((i : Nat) : Int) ch
  rw [gs_append, ← strFamily_succ] at hB3
  have hA1 := bu_A1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) (gs (strFamily (i + 1) seed))
    ((i : Nat) : Int) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64),
    unorm_nat_of_lt (by omega : i + 1 < 2 ^ 64)] at hA1
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hB1 hmod) hB2) hrune) hB3) hA1

/-! ## The loop (the P5 iteration schema) -/

/-- **The build loop**: `65·(n−i)` steps materialize the family. -/
theorem bu_loop (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 64) :
    ∀ i, i ≤ n → ∀ ch : Choices,
    stepFnIter (65 * (n - i))
      (sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
        ((n : Nat) : Int) ((seed : Nat) : Int)
        (gs (strFamily i seed)) ((i : Nat) : Int) false) 12)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        buCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) buCmpK,
          sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
            ((n : Nat) : Int) ((seed : Nat) : Int)
            (gs (strFamily n seed)) ((n : Nat) : Int) false) 12, ch) := by
  intro i hin ch
  exact stepFnIter_iterate (c := 65) (n := n)
    (T := fun j => sSt σ (sHeapBu ((n : Nat) : Int) ((seed : Nat) : Int)
      ((n : Nat) : Int) ((seed : Nat) : Int)
      (gs (strFamily j seed)) ((j : Nat) : Int) false) 12)
    (C := fun j => .retV (.bool (decide
      (((j : Nat) : Int) < ((n : Nat) : Int)))) buCmpK)
    (fun j hj ch' => by
      rw [show (decide (((j : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hj)]
      exact bu_iter σ n seed hn j hj ch')
    i hin ch

end GoLean.Examples.StringReverse
