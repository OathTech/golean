import GoLeanProofs.Examples.StringReverse.Build

/-!
# StringReverse — the `reverseString` phase

The subject's frame: prologue (`out := ""`, `i := len(s)-1`), the
down-counting loop `out += string(rune(s[i]))`, and the exit into the
`isStringPalindrome` call's argument point.

Per-segment step counts (probe-measured, re-checked by `rfl`):
prologue 49; dispatch first/later 25/29; one iteration 57; exit → next
call's argument delivered 33.

The invariant is `revPre`: after `m` iterations the accumulator holds
the reversal of the LAST `m` bytes. The per-iteration conditioned
steps are the byte read (`applyStrictOp_indexGet_string`) and the
ASCII `string(rune(·))` — the loop carries `∀ b ∈ l, b.toNat < 128`
for the second, because the machine models the rune round-trip
faithfully (a high byte would come back UTF-8 expanded).
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw segments — PROGRAM-generic throughout -/

/-- The `reverseString` frame prologue: `out := ""`, `i := len(s)-1`
(the length is DEFINITIONAL — a string is a value), the first-pass
flag → the loop head. 49 steps. -/
theorem rv_pro_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (ch : Choices) :
    stepFnIter 49 (sSt σ (sHeapRF nv sv bnv bsv l biv) 15)
      (.exec reverseStringFunc.body revFrameEnv revFrameK) ch
      = .ok (revHeadCfg,
          sSt σ (sHeapRev nv sv bnv bsv l biv GoString.empty
            (IntKind.normalize .int
              (IntKind.normalize .int ((l.length : Int) - 1))) true) 18,
          ch) := by
  with_unfolding_all rfl

/-- Reverse dispatch, first pass. 25 steps. -/
theorem rv_A0_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (ch : Choices) :
    stepFnIter 25 (sSt σ (sHeapRev nv sv bnv bsv l biv rov riv true) 18)
      revHeadCfg ch
      = .ok (.retV (.bool (decide (riv ≥ 0))) revCmpK,
          sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18, ch) := by
  with_unfolding_all rfl

/-- Reverse dispatch, later passes: `i--`, exit test delivered.
29 steps. -/
theorem rv_A1_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (ch : Choices) :
    stepFnIter 29 (sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18)
      revHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .int (IntKind.normalize .int (riv - 1))
              ≥ 0))) revCmpK,
          sSt σ (sHeapRev nv sv bnv bsv l biv rov
            (IntKind.normalize .int (IntKind.normalize .int (riv - 1)))
            false) 18, ch) := by
  with_unfolding_all rfl

/-- Reverse body A: test true → the `s[i]` apply point (`s` banked,
`i` delivered). 17 steps. -/
theorem rv_B1_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (ch : Choices) :
    stepFnIter 17 (sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18)
      (.retV (.bool true) revCmpK) ch
      = .ok (.retV (.int riv .int) (revIdxK rov l),
          sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18, ch) := by
  with_unfolding_all rfl

/-- Reverse body B: the byte delivered → the `rune` conversion →
the `string(rune(·))` apply point. 1 step. -/
theorem rv_B2_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv b : Int) (ch : Choices) :
    stepFnIter 1 (sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18)
      (.retV (.int b .uint8) (revConvK rov)) ch
      = .ok (.retV (.int (IntKind.normalize .int32 b) .int32)
            (revRuneK rov),
          sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18, ch) := by
  with_unfolding_all rfl

/-- Reverse body C: the one-byte string delivered → the append, the
store, the loop head. 8 steps. -/
theorem rv_B3_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov w : GoString) (riv : Int) (ch : Choices) :
    stepFnIter 8 (sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18)
      (.retV (.string w) (revAppK rov)) ch
      = .ok (revHeadCfg,
          sSt σ (sHeapRev nv sv bnv bsv l biv (GoString.append rov w) riv
            false) 18, ch) := by
  with_unfolding_all rfl

/-- Reverse exit: test false → `$res0 := out`, the frame pop into
`post`, `var isPalin`, and the `isStringPalindrome(pre)` argument
delivered. 33 steps. -/
theorem rv_X_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (ch : Choices) :
    stepFnIter 33 (sSt σ (sHeapRev nv sv bnv bsv l biv rov riv false) 18)
      (.retV (.bool false) revCmpK) ch
      = .ok (.retV (.string (gs l)) palCallK0,
          sSt σ (sHeapRX nv sv bnv bsv l biv rov riv) 19, ch) := by
  with_unfolding_all rfl

/-! ## One iteration, cleaned -/

/-- One reverse iteration from the exit test's true delivery at `m`
(counting ITERATIONS, so the index cell is `n-1-m`): 57 steps append
the byte at `n-1-m`. -/
theorem rv_iter (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (n : Nat) (hln : l.length = n) (hn : n < 2 ^ 63)
    (hascii : ∀ b ∈ l, b.toNat < 128) (m : Nat) (hm : m < n)
    (ch : Choices) :
    stepFnIter 57
      (sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l m))
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
      (.retV (.bool true) revCmpK) ch
      = .ok (.retV (.bool (decide
            ((((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) ≥ 0)))
            revCmpK,
          sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l (m + 1)))
            (((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) false) 18,
          ch) := by
  have hidx : n - 1 - m < l.length := by omega
  have hB1 := rv_B1_raw σ nv sv bnv bsv l biv (gs (revPre l m))
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  have hcast : (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
      = ((n - 1 - m : Nat) : Int) := by omega
  have hread := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := revEnv2)
    (k := revConvK (gs (revPre l m))) (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l m))
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
      (i := n - 1 - m) (ik := .int) hidx))
  rw [← hcast] at hread
  have hB2 := rv_B2_raw σ nv sv bnv bsv l biv (gs (revPre l m))
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
    (((l.getD (n - 1 - m) 0).toNat : Nat) : Int) ch
  have hbmem : (l.getD (n - 1 - m) 0).toNat < 128 :=
    hascii _ (getD_mem_u8 hidx)
  rw [i32norm_nat_of_lt (by omega : (l.getD (n - 1 - m) 0).toNat < 2 ^ 31)]
    at hB2
  have hrune := stepFnIter_one (stepFn_strict_apply
    (done := []) (env := revEnv2) (k := revAppK (gs (revPre l m)))
    (ch := ch)
    (applyStrictOp_stringFromRune_ascii
      (σ := sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l m))
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
      (c := (l.getD (n - 1 - m) 0).toNat) (ik := .int32) hbmem))
  rw [UInt8.ofNat_toNat] at hrune
  have hB3 := rv_B3_raw σ nv sv bnv bsv l biv (gs (revPre l m))
    (gs [l.getD (n - 1 - m) 0])
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  rw [gs_append,
    show revPre l m ++ [l.getD (n - 1 - m) 0] = revPre l (m + 1) from by
      rw [revPre_succ (by omega : m < l.length), hln]] at hB3
  have hA1 := rv_A1_raw σ nv sv bnv bsv l biv (gs (revPre l (m + 1)))
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  rw [show IntKind.normalize .int (IntKind.normalize .int
        ((((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1))
      = (((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) from by
    rw [inorm_of_range
        (v := (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1)
        (by omega) (by omega),
      inorm_of_range
        (v := (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1)
        (by omega) (by omega)]
    omega] at hA1
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hB1 hread) hB2) hrune) hB3) hA1

/-! ## The loop (the P5 iteration schema) -/

/-- **The reverse loop**: `57·(n−m)` steps materialize the reversal —
the exit test at `m = n` delivers `decide (-1 ≥ 0) = false`. -/
theorem rv_loop (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (n : Nat) (hln : l.length = n) (hn : n < 2 ^ 63)
    (hascii : ∀ b ∈ l, b.toNat < 128) :
    ∀ m, m ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - m))
      (sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l m))
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 18)
      (.retV (.bool (decide
        ((((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ≥ 0))) revCmpK) ch
      = .ok (.retV (.bool (decide
            ((((n : Nat) : Int) - 1 - ((n : Nat) : Int)) ≥ 0))) revCmpK,
          sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l n))
            (((n : Nat) : Int) - 1 - ((n : Nat) : Int)) false) 18,
          ch) := by
  intro m hmn ch
  exact stepFnIter_iterate (c := 57) (n := n)
    (T := fun j => sSt σ (sHeapRev nv sv bnv bsv l biv (gs (revPre l j))
      (((n : Nat) : Int) - 1 - ((j : Nat) : Int)) false) 18)
    (C := fun j => .retV (.bool (decide
      ((((n : Nat) : Int) - 1 - ((j : Nat) : Int)) ≥ 0))) revCmpK)
    (fun j hj ch' => by
      rw [show (decide ((((n : Nat) : Int) - 1 - ((j : Nat) : Int)) ≥ 0))
            = true from decide_eq_true (by omega)]
      exact rv_iter σ nv sv bnv bsv l biv n hln hn hascii j hj ch')
    m hmn ch

end GoLean.Examples.StringReverse
