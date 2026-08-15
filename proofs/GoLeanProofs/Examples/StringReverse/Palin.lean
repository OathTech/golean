import GoLeanProofs.Examples.StringReverse.Rev

/-!
# StringReverse — the `isStringPalindrome` phase

The companion subject's frame, and the shape that makes it interesting:
the EARLY RETURN. The first mismatched byte pair leaves the function
immediately with verdict `0`, so the loop induction below does not stop
at a loop head — it runs all the way to the DRIVER TERMINAL, and both
ways out (the middle is reached, or a pair mismatches) land on the same
`.next .stop` with the verdict `palinSpec l` delivered through the
frame pop AND the harness epilogue (`$res0 := pre; $res1 := post;
$res2 := isPalin; return`). The final `i`/`j` cells differ between the
two exits, so they are existentially quantified — nothing returned
reads them.

Per-segment step counts (probe-measured at the mismatch path,
`rfl`-checked here; the match/A1 counts coincide with ArrayPalindrome's
subject loop, whose statement shapes are identical): prologue 47;
dispatch first/later 25/18; body to the `!=` verdict 19; full matched
iteration 68; mismatch → terminal 60; middle exit → terminal 58.
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Raw segments — PROGRAM-generic throughout -/

/-- The `isStringPalindrome` frame prologue: `i := 0`,
`j := len(s)-1`, the first-pass flag → the loop head. 47 steps. -/
theorem p_pro_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (ch : Choices) :
    stepFnIter 47 (sSt σ (sHeapPF nv sv bnv bsv l biv rov riv) 21)
      (.exec isStringPalindromeFunc.body pFrameEnv palFrameK) ch
      = .ok (pHeadCfg,
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv 0
            (IntKind.normalize .int
              (IntKind.normalize .int ((l.length : Int) - 1))) true) 24,
          ch) := by
  with_unfolding_all rfl

/-- Palindrome dispatch, first pass. 25 steps. -/
theorem p_A0_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv : Int) (ch : Choices) :
    stepFnIter 25
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv true) 24)
      pHeadCfg ch
      = .ok (.retV (.bool (decide (piv < pjv))) pCmpIfK,
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24,
          ch) := by
  with_unfolding_all rfl

/-- Palindrome dispatch, later passes (the else-arm is empty — both
index steps live in the body). 18 steps. -/
theorem p_A1_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv : Int) (ch : Choices) :
    stepFnIter 18
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      pHeadCfg ch
      = .ok (.retV (.bool (decide (piv < pjv))) pCmpIfK,
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24,
          ch) := by
  with_unfolding_all rfl

/-- Body A: test true → the `s[i]` apply point. 11 steps. -/
theorem p_B1_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv : Int) (ch : Choices) :
    stepFnIter 11
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      (.retV (.bool true) pCmpIfK) ch
      = .ok (.retV (.int piv .int) (pIdx1K l),
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24,
          ch) := by
  with_unfolding_all rfl

/-- Body B: `s[i]` banked → the `s[j]` apply point. 5 steps. -/
theorem p_B2_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv a : Int) (ch : Choices) :
    stepFnIter 5
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      (.retV (.int a .uint8)
        (.strictK (.neqCmp (.int .uint8)) []
          [.indexGet (.var "s") (.var "j")] pEnvB2 pNeIfK)) ch
      = .ok (.retV (.int pjv .int) (pIdx2K l a),
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24,
          ch) := by
  with_unfolding_all rfl

/-- Body C: both bytes banked → the `!=` verdict. 1 step. -/
theorem p_B3_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv a b : Int) (ch : Choices) :
    stepFnIter 1
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      (.retV (.int b .uint8)
        (.strictK (.neqCmp (.int .uint8)) [.int a .uint8] [] pEnvB2
          pNeIfK)) ch
      = .ok (.retV (.bool (!(a == b))) pNeIfK,
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24,
          ch) := by
  with_unfolding_all rfl

/-- The MATCH branch: the pair agreed → `i++`, `j--`, the loop head.
31 steps. -/
theorem p_match_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv : Int) (ch : Choices) :
    stepFnIter 31
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      (.retV (.bool false) pNeIfK) ch
      = .ok (pHeadCfg,
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv
            (IntKind.normalize .int (IntKind.normalize .int (piv + 1)))
            (IntKind.normalize .int (IntKind.normalize .int (pjv - 1)))
            false) 24, ch) := by
  with_unfolding_all rfl

/-- The MISMATCH exit: `return 0`, the frame pop into `isPalin`, and
the whole harness epilogue to the DRIVER TERMINAL. 60 steps. -/
theorem p_bail_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv : Int) (ch : Choices) :
    stepFnIter 60
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      (.retV (.bool true) pNeIfK) ch
      = .ok (.next .stop,
          sSt σ (sHeapEnd nv sv bnv bsv l biv rov riv piv pjv 0) 24,
          ch) := by
  with_unfolding_all rfl

/-- The MIDDLE exit: `i ≥ j` → `return 1`, the frame pop, the same
epilogue. 58 steps. -/
theorem p_out_raw (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv piv pjv : Int) (ch : Choices) :
    stepFnIter 58
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv piv pjv false) 24)
      (.retV (.bool false) pCmpIfK) ch
      = .ok (.next .stop,
          sSt σ (sHeapEnd nv sv bnv bsv l biv rov riv piv pjv 1) 24,
          ch) := by
  with_unfolding_all rfl

/-! ## One iteration / the two exits, cleaned -/

/-- One full subject iteration (the pair matched): 68 steps from the
exit test's true delivery at `m` to the next delivery at `m+1`. -/
theorem p_iter (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (n : Nat)
    (hln : l.length = n) (hn : n < 2 ^ 63) (m : Nat) (hm : m < n / 2)
    (heq : l.getD m 0 = l.getD (n - 1 - m) 0) (ch : Choices) :
    stepFnIter 68
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
      (.retV (.bool true) pCmpIfK) ch
      = .ok (.retV (.bool (decide (((m + 1 : Nat) : Int)
            < ((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)))) pCmpIfK,
          sSt σ (sHeapPal nv sv bnv bsv l biv rov riv
            ((m + 1 : Nat) : Int)
            (((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) false) 24,
          ch) := by
  have hmn : m < n := by omega
  have hjn : n - 1 - m < n := by omega
  have hjcast : (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
      = ((n - 1 - m : Nat) : Int) := by omega
  have hB1 := p_B1_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  have hread1 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := pEnvB2)
    (k := .strictK (.neqCmp (.int .uint8)) []
      [.indexGet (.var "s") (.var "j")] pEnvB2 pNeIfK) (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
      (i := m) (ik := .int) (by omega)))
  have hB2 := p_B2_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
    (((l.getD m 0).toNat : Nat) : Int) ch
  have hread2 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := pEnvB2)
    (k := .strictK (.neqCmp (.int .uint8))
      [.int (((l.getD m 0).toNat : Nat) : Int) .uint8] [] pEnvB2 pNeIfK)
    (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
      (i := n - 1 - m) (ik := .int) (by omega)))
  rw [← hjcast] at hread2
  have hB3 := p_B3_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
    (((l.getD m 0).toNat : Nat) : Int)
    (((l.getD (n - 1 - m) 0).toNat : Nat) : Int) ch
  rw [show (!((((l.getD m 0).toNat : Nat) : Int)
        == (((l.getD (n - 1 - m) 0).toNat : Nat) : Int))) = false from by
      rw [byteInt_beq_of_eq heq]; rfl] at hB3
  have hM := p_match_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  rw [show IntKind.normalize .int (IntKind.normalize .int
        (((m : Nat) : Int) + 1)) = ((m + 1 : Nat) : Int) from by
      rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) from by omega,
        inorm_nat_of_lt (by omega), inorm_nat_of_lt (by omega)],
    show IntKind.normalize .int (IntKind.normalize .int
        ((((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1))
        = ((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int) from by
      rw [inorm_of_range
          (v := (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1)
          (by omega) (by omega),
        inorm_of_range
          (v := (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) - 1)
          (by omega) (by omega)]
      omega] at hM
  have hA1 := p_A1_raw σ nv sv bnv bsv l biv rov riv ((m + 1 : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m + 1 : Nat) : Int)) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain hB1 hread1) hB2) hread2) hB3) hM) hA1

/-- **The mismatch exit**: a pair disagrees at `m` → verdict `0` and
the DRIVER TERMINAL. 79 steps from the exit test's true delivery. -/
theorem p_bail (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (n : Nat)
    (hln : l.length = n) (m : Nat) (hm : m < n / 2)
    (hne : ¬ (l.getD m 0 = l.getD (n - 1 - m) 0)) (ch : Choices) :
    stepFnIter 79
      (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
      (.retV (.bool true) pCmpIfK) ch
      = .ok (.next .stop,
          sSt σ (sHeapEnd nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
            (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) 0) 24, ch) := by
  have hmn : m < n := by omega
  have hjn : n - 1 - m < n := by omega
  have hjcast : (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
      = ((n - 1 - m : Nat) : Int) := by omega
  have hB1 := p_B1_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  have hread1 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := pEnvB2)
    (k := .strictK (.neqCmp (.int .uint8)) []
      [.indexGet (.var "s") (.var "j")] pEnvB2 pNeIfK) (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
      (i := m) (ik := .int) (by omega)))
  have hB2 := p_B2_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
    (((l.getD m 0).toNat : Nat) : Int) ch
  have hread2 := stepFnIter_one (stepFn_strict_apply
    (done := [.string (gs l)]) (env := pEnvB2)
    (k := .strictK (.neqCmp (.int .uint8))
      [.int (((l.getD m 0).toNat : Nat) : Int) .uint8] [] pEnvB2 pNeIfK)
    (ch := ch)
    (applyStrictOp_indexGet_string
      (σ := sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
        (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
      (i := n - 1 - m) (ik := .int) (by omega)))
  rw [← hjcast] at hread2
  have hB3 := p_B3_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int))
    (((l.getD m 0).toNat : Nat) : Int)
    (((l.getD (n - 1 - m) 0).toNat : Nat) : Int) ch
  rw [show (!((((l.getD m 0).toNat : Nat) : Int)
        == (((l.getD (n - 1 - m) 0).toNat : Nat) : Int))) = true from by
      rw [byteInt_beq_of_ne hne]; rfl] at hB3
  have hX := p_bail_raw σ nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
    (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) ch
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hB1 hread1) hB2) hread2) hB3) hX

/-! ## The subject loop, to the driver terminal -/

/-- **The subject loop**: from the exit-test delivery at `m` — every
earlier pair known to match — the run reaches the DRIVER TERMINAL
within `68·μ + 79` steps with `palinSpec l` as the verdict. The final
`i`/`j` are existentially quantified: the two exits stop at different
places and nothing returned depends on them. -/
theorem p_loop (σ : ExecState) (nv sv bnv bsv : Int) (l : List UInt8)
    (biv : Int) (rov : GoString) (riv : Int) (n : Nat)
    (hln : l.length = n) (hn : n < 2 ^ 63) :
    ∀ μ m : Nat, m ≤ n / 2 → μ = n / 2 - m → PalinUpTo l m →
    ∀ ch : Choices,
    ∃ (k : Nat) (piv pjv : Int), k ≤ 68 * μ + 79 ∧
      stepFnIter k
        (sSt σ (sHeapPal nv sv bnv bsv l biv rov riv ((m : Nat) : Int)
          (((n : Nat) : Int) - 1 - ((m : Nat) : Int)) false) 24)
        (.retV (.bool (decide (((m : Nat) : Int)
          < ((n : Nat) : Int) - 1 - ((m : Nat) : Int)))) pCmpIfK) ch
        = .ok (.next .stop,
            sSt σ (sHeapEnd nv sv bnv bsv l biv rov riv piv pjv
              (palinSpec l)) 24, ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m hmc hμ hup ch
    rcases Nat.lt_or_ge m (n / 2) with hlt | hge
    · rw [show (decide (((m : Nat) : Int)
          < ((n : Nat) : Int) - 1 - ((m : Nat) : Int))) = true from
        decide_eq_true (by omega)]
      by_cases heq : l.getD m 0 = l.getD (n - 1 - m) 0
      · -- the pair matches: one full iteration, then recurse
        obtain ⟨k, piv, pjv, hk, hrun⟩ := ih (μ - 1) (by omega) (m + 1)
          (by omega) (by omega)
          (palinUpTo_succ hup (by rw [hln]; exact heq)) ch
        refine ⟨68 + k, piv, pjv, by omega, ?_⟩
        exact stepFnIter_chain
          (p_iter σ nv sv bnv bsv l biv rov riv n hln hn m hlt heq ch) hrun
      · -- the pair disagrees: the early return, verdict 0
        refine ⟨79, ((m : Nat) : Int),
          (((n : Nat) : Int) - 1 - ((m : Nat) : Int)), by omega, ?_⟩
        rw [show palinSpec l = 0 from
          palinSpec_of_mismatch (by omega : m < l.length)
            (by rw [hln]; exact heq)]
        exact p_bail σ nv sv bnv bsv l biv rov riv n hln m hlt heq ch
    · -- the walk met in the middle: verdict 1
      have hmn : m = n / 2 := by omega
      subst hmn
      rw [show (decide (((n / 2 : Nat) : Int)
          < ((n : Nat) : Int) - 1 - ((n / 2 : Nat) : Int))) = false from
        decide_eq_false (by omega)]
      refine ⟨58, ((n / 2 : Nat) : Int),
        (((n : Nat) : Int) - 1 - ((n / 2 : Nat) : Int)), by omega, ?_⟩
      rw [show palinSpec l = 1 from
        palinSpec_of_full (by rw [hln]; exact hup)]
      exact p_out_raw σ nv sv bnv bsv l biv rov riv _ _ ch

end GoLean.Examples.StringReverse
