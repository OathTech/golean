import GoLeanProofs.Examples.StringReverse.Palin

/-!
# StringReverse — the harness run, end to end

The assembly: entry → the `buildStr` frame and its loop → the
`reverseString` frame and its loop → the `isStringPalindrome` frame
and its two-exit walk to the DRIVER TERMINAL. PROGRAM-generic
throughout — the three steps that consult the program (the frame
entries) are conditioned through `StepKit.stepFn_call_enter`, and the
pinned program is unfolded exactly SEVEN times in the whole example:
the four lowering pins, and the three `enterFrame` discharges.

Fuel accounting (branch-uniform worst case, `156·n + 372`):
`65` per build iteration, `57` per reverse iteration, `68` per full
palindrome iteration (at most `n/2`, charged as `34·n`), plus the
fixed `372` — entry 10, three `enterFrame`s, prologues 43/49/47,
first dispatches 25×3, the two inter-frame exits 33×2, and the
palindrome exit's worst tail 79.
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- **The harness run, PROGRAM-generic**: within `156·n + 372` steps
the run reaches the driver terminal with the family bytes in `$res0`,
their reversal in `$res1`, and `palinSpec` of the family in `$res2`. -/
theorem s_runs_generic (σ : ExecState) (n seed : Nat) (hn : n < 2 ^ 63)
    (henterBu : enterFrame
        (sSt σ (sHeapPre ((n : Nat) : Int) ((seed : Nat) : Int)) 6)
        ⟨"buildStr"⟩
        [.int ((n : Nat) : Int) .uint64, .int ((seed : Nat) : Int) .uint64]
      = .ok (buildStrFunc, buFrameEnv, [.base ⟨8⟩],
          sSt σ (sHeapBF ((n : Nat) : Int) ((seed : Nat) : Int)
            ((n : Nat) : Int) ((seed : Nat) : Int)) 9))
    (henterRev : ∀ (l : List UInt8) (biv : Int),
      enterFrame (sSt σ (sHeapBX ((n : Nat) : Int) ((seed : Nat) : Int)
          ((n : Nat) : Int) ((seed : Nat) : Int) l biv) 13)
        ⟨"reverseString"⟩ [.string (gs l)]
      = .ok (reverseStringFunc, revFrameEnv, [.base ⟨14⟩],
          sSt σ (sHeapRF ((n : Nat) : Int) ((seed : Nat) : Int)
            ((n : Nat) : Int) ((seed : Nat) : Int) l biv) 15))
    (henterPal : ∀ (l : List UInt8) (biv : Int) (rov : GoString)
        (riv : Int),
      enterFrame (sSt σ (sHeapRX ((n : Nat) : Int) ((seed : Nat) : Int)
          ((n : Nat) : Int) ((seed : Nat) : Int) l biv rov riv) 19)
        ⟨"isStringPalindrome"⟩ [.string (gs l)]
      = .ok (isStringPalindromeFunc, pFrameEnv, [.base ⟨20⟩],
          sSt σ (sHeapPF ((n : Nat) : Int) ((seed : Nat) : Int)
            ((n : Nat) : Int) ((seed : Nat) : Int) l biv rov riv) 21))
    (ch : Choices) :
    ∃ (k : Nat) (piv pjv : Int), k ≤ 156 * n + 372 ∧
      stepFnIter k
        (sSt σ (sHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 5) sHC0 ch
        = .ok (.next .stop,
            sSt σ (sHeapEnd ((n : Nat) : Int) ((seed : Nat) : Int)
              ((n : Nat) : Int) ((seed : Nat) : Int) (strFamily n seed)
              ((n : Nat) : Int) (gs (strFamily n seed).reverse) (-1)
              piv pjv (palinSpec (strFamily n seed))) 24, ch) := by
  have hn64 : n < 2 ^ 64 := by omega
  let l : List UInt8 := strFamily n seed
  have hlen : l.length = n := strFamily_length n seed
  have hascii : ∀ b ∈ l, b.toNat < 128 := strFamily_ascii
  -- entry and the buildStr frame
  have hE1 := s_E1_raw σ ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hentBu := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := buShapes) (env := hEnv1) (k := hAfterBu)
      (vals := [.int ((n : Nat) : Int) .uint64])
      (v := .int ((seed : Nat) : Int) .uint64) henterBu)
  have hpro := bu_pro_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) ch
  have hA0 := bu_A0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) GoString.empty 0 ch
  have hbuLoop := bu_loop σ n seed hn64 0 (by omega) ch
  rw [show gs (strFamily 0 seed) = GoString.empty from by
        rw [strFamily_zero]; rfl,
      show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hbuLoop
  have h1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain hE1 hentBu) hpro) hA0) hbuLoop
  -- the buildStr exit and the reverseString frame
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at h1
  have hbuX := bu_X_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int) ch
  have hentRev := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := revShapes) (env := hEnv2)
      (k := hAfterRev) (vals := []) (v := .string (gs l))
      (henterRev l ((n : Nat) : Int)))
  have hrvPro := rv_pro_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int) ch
  rw [show IntKind.normalize .int (IntKind.normalize .int
        ((l.length : Int) - 1))
      = ((n : Nat) : Int) - 1 - ((0 : Nat) : Int) from by
    rw [hlen, inorm_of_range (v := ((n : Nat) : Int) - 1)
        (by omega) (by omega),
      inorm_of_range (v := ((n : Nat) : Int) - 1) (by omega) (by omega)]
    omega] at hrvPro
  have hrvA0 := rv_A0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int)
    GoString.empty (((n : Nat) : Int) - 1 - ((0 : Nat) : Int)) ch
  have hrvLoop := rv_loop σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int) n hlen hn
    hascii 0 (by omega) ch
  rw [show gs (revPre l 0) = GoString.empty from by
        rw [revPre_zero]; rfl] at hrvLoop
  have h2 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 hbuX) hentRev) hrvPro) hrvA0)
    hrvLoop
  -- the reverseString exit and the isStringPalindrome frame
  rw [show (decide ((((n : Nat) : Int) - 1 - ((n : Nat) : Int)) ≥ 0))
      = false from decide_eq_false (by omega)] at h2
  have hrvX := rv_X_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int)
    (gs (revPre l n)) (((n : Nat) : Int) - 1 - ((n : Nat) : Int)) ch
  have hentPal := stepFnIter_one (ch := ch)
    (stepFn_call_enter (plans := palShapes) (env := hEnv3)
      (k := hAfterPal) (vals := []) (v := .string (gs l))
      (henterPal l ((n : Nat) : Int) (gs (revPre l n))
        (((n : Nat) : Int) - 1 - ((n : Nat) : Int))))
  have hpPro := p_pro_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int)
    (gs (revPre l n)) (((n : Nat) : Int) - 1 - ((n : Nat) : Int)) ch
  rw [show IntKind.normalize .int (IntKind.normalize .int
        ((l.length : Int) - 1))
      = ((n : Nat) : Int) - 1 - ((0 : Nat) : Int) from by
    rw [hlen, inorm_of_range (v := ((n : Nat) : Int) - 1)
        (by omega) (by omega),
      inorm_of_range (v := ((n : Nat) : Int) - 1) (by omega) (by omega)]
    omega] at hpPro
  have hpA0 := p_A0_raw σ ((n : Nat) : Int) ((seed : Nat) : Int)
    ((n : Nat) : Int) ((seed : Nat) : Int) l ((n : Nat) : Int)
    (gs (revPre l n)) (((n : Nat) : Int) - 1 - ((n : Nat) : Int)) 0
    (((n : Nat) : Int) - 1 - ((0 : Nat) : Int)) ch
  obtain ⟨k3, piv, pjv, hk3, hpLoop⟩ := p_loop σ ((n : Nat) : Int)
    ((seed : Nat) : Int) ((n : Nat) : Int) ((seed : Nat) : Int) l
    ((n : Nat) : Int) (gs (revPre l n))
    (((n : Nat) : Int) - 1 - ((n : Nat) : Int)) n hlen hn (n / 2) 0
    (by omega) (by omega) (palinUpTo_zero l) ch
  rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hpLoop
  have h3 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h2 hrvX) hentPal) hpPro) hpA0)
    hpLoop
  -- the terminal state, at the clean spellings
  rw [show revPre l n = l.reverse from by rw [← hlen, revPre_full],
    show ((n : Nat) : Int) - 1 - ((n : Nat) : Int) = (-1 : Int) from by
      omega] at h3
  exact ⟨10 + 1 + 43 + 25 + 65 * (n - 0) + 33 + 1 + 49 + 25
    + 57 * (n - 0) + 33 + 1 + 47 + 25 + k3, piv, pjv, by omega, h3⟩

end GoLean.Examples.StringReverse
