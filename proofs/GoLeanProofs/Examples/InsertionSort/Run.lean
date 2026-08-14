import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.InsertionSort.Count

/-!
# InsertionSort — Run

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
open GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## Composition: the remainder run, the full harness run, and the
§11 headline -/

private theorem renCfg_stop11 (d : Nat) :
    renameConfig (ρ11 d) (.next .stop) = .next .stop := rfl

/-- **The remainder run** (post-subject, canonical placement): from the
post-subject anchor the scan, rebuild, and count phases run to the
DRIVER TERMINAL with the verdict 1 in the result cell — within
`(110·n + 220)·n + 114·n + 350` steps. -/
private theorem hremainder_runs (n seed : Nat) (hn : n < 2 ^ 63) (ivF : Int)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ (110 * n + 220) * n + 114 * n + 350 ∧
      stepFnIter k (σHOut n seed (sortSpec (isFamily n seed)) ivF false)
        (.next hAfterCallK) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩) = some (ucell 1) := by
  have hll : (sortSpec (isFamily n seed)).length = n := by
    rw [sortSpec_length, isFamily_length]
  have htl : (isFamily n seed).length = n := isFamily_length n seed
  have hsort := sortSpec_sorted (isFamily n seed)
  have hcount : ∀ v, cntSpec v (sortSpec (isFamily n seed))
      = cntSpec v (isFamily n seed) := fun v => by
    rw [cntSpec_eq_count, cntSpec_eq_count, sortSpec_count]
  -- the scan
  have hR1 := hR1_raw n seed ivF (sortSpec (isFamily n seed)) ch
  have hd0 := hsc_d0_raw n seed ivF (sortSpec (isFamily n seed)) 1 ch
  obtain ⟨k1, mf, hk1, hmf, hscan⟩ := hscan_loop n seed hn ivF
    (sortSpec (isFamily n seed)) hll hsort (n - 1) 1 rfl (by omega) ch
  rw [show ((1 : Nat) : Int) = (1 : Int) from rfl] at hscan
  -- scan exit → the second makeSlice → the rebuild entry
  have hX := hsc_X_raw n seed ivF (sortSpec (isFamily n seed))
    ((mf : Nat) : Int) ch
  have hms := hstep_Ims2 n seed ivF (sortSpec (isFamily n seed))
    ((mf : Nat) : Int) ch
  have hR2 := hR2_raw n seed ivF (sortSpec (isFamily n seed))
    ((mf : Nat) : Int) ch
  have hrb0 := hrb_d0_raw n seed ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (List.replicate n 0) 0 ch
  have hrb := hrebuild_loop n seed hn ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (n - 0) 0 rfl (by omega) ch
  rw [show isFamily 0 seed ++ List.replicate (n - 0) (0 : Int)
        = List.replicate n 0 from by simp [isFamily],
    show ((0 : Nat) : Int) = (0 : Int) from rfl] at hrb
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hrb
  -- the count entry
  have hce := hcnt_entry_raw n seed ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (isFamily n seed) ch
  have hcd0 := hcnt_d0_raw n seed ivF ((mf : Nat) : Int)
    (sortSpec (isFamily n seed)) (isFamily n seed) 0 [] 21 ch
  -- the count loop
  obtain ⟨k2, σf, hk2, hcout, hread⟩ := hcnt_outer_loop n seed hn ivF
    ((mf : Nat) : Int) (sortSpec (isFamily n seed)) (isFamily n seed)
    hll htl hcount (n - 0) 0
    (σCntOut n seed ivF ((mf : Nat) : Int) (sortSpec (isFamily n seed))
      (isFamily n seed) 0 false) [] rfl (by omega)
    (frameSim_zero21 n seed ivF ((mf : Nat) : Int)
      (sortSpec (isFamily n seed)) (isFamily n seed) 0 false) ch
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl] at hcout
  -- the chain
  have h1 := stepFnIter_chain hR1 hd0
  have h2 := stepFnIter_chain h1 hscan
  have h3 := stepFnIter_chain h2 hX
  have h4 := stepFnIter_chain h3 (stepFnIter_one hms)
  have h5 := stepFnIter_chain h4 hR2
  have h6 := stepFnIter_chain h5 hrb0
  have h7 := stepFnIter_chain h6 hrb
  have h8 := stepFnIter_chain h7 hce
  have h9 := stepFnIter_chain h8 hcd0
  have h10 := stepFnIter_chain h9 hcout
  refine ⟨42 + 25 + k1 + 15 + 1 + 42 + 25 + 57 * (n - 0) + 35 + 25 + k2,
    σf, ?_, h10, hread⟩
  have hmulc : (110 * n + 220) * (n - 0) ≤ (110 * n + 220) * n :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The full harness run**: from the cleaned prelude state, the
whole three-phase harness completes at the driver terminal with the
verdict 1 in the result cell — within
`(92·n+160)·n + (110·n+220)·n + 285·n + 505` steps. -/
theorem isortH_runs (n seed : Nat) (hn : n < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ (92 * n + 160) * n + (110 * n + 220) * n + 285 * n + 505 ∧
      stepFnIter k (σIStart n seed) iHC₀ ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩) = some (ucell 1) := by
  -- the prelude → the setup loop
  have hA1 := hseg_IA1_raw n seed ch
  have hmk := hstep_ImakeSlice n seed ch
  have hA2 := hseg_IA2_raw n seed ch
  have hd0 := hsegISU_d0_raw n (seed : Int) 0 (List.replicate n 0) ch
  have hsetup := hIsetup_loop n seed hn (n - 0) 0 rfl (by omega) ch
  rw [show isFamily 0 seed ++ List.replicate (n - 0) (0 : Int)
        = List.replicate n 0 from by simp [isFamily],
    show ((0 : Nat) : Int) = (0 : Int) from rfl] at hsetup
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hsetup
  -- the bridge into the subject
  have hbr := hbridge_raw n seed (isFamily n seed) ch
  have hO0 := hseg_O0_raw n seed (isFamily n seed) 1 [] 11 ch
  have hlenapp : stepFn (σHOutT n seed (isFamily n seed) 1 false [] 11)
      (.retV (hISliceH n) (hLenTestK 1)) ch
      = .ok (.retV (.int ((n : Nat) : Int) .int)
          (.strictK .lessCmp [.int 1 .int] [] ([] :: envHO) hOuterCmpCont),
        σHOutT n seed (isFamily n seed) 1 false [] 11, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl n))
  have hOB := hseg_OB_raw n seed (isFamily n seed) 1 [] 11 ch
  -- the subject loop from pass 0 (trivial frame)
  have hFS0 : FrameSim (ρ11 (2 * 0)) 11 (11 + 2 * 0) []
      (σHOut n seed (sortPrefix (isFamily n seed) (0 + 1))
        ((0 + 1 : Nat) : Int) false)
      (σHOut n seed (isFamily n seed) 1 false) := by
    show FrameSim (ρ11 0) 11 11 []
      (σHOut n seed (sortPrefix (isFamily n seed) 1) ((1 : Nat) : Int) false)
      (σHOut n seed (isFamily n seed) 1 false)
    rw [sortPrefix_one]
    exact frameSim_zero11 n seed (isFamily n seed) 1 false
  obtain ⟨k1, σA', d, fr', ivF, hk1, hsubj, hFSd⟩ := hs_outer_loop
    (isFamily n seed) n seed (isFamily_length n seed).symm
    (isFamily_range n seed) hn (n - (0 + 1)) 0
    (σHOut n seed (isFamily n seed) 1 false) [] rfl hFS0 ch
  rw [show ((0 + 1 : Nat) : Int) = (1 : Int) from rfl] at hsubj
  -- the remainder, transferred through the surviving frame simulation
  obtain ⟨k2, σR, hk2, hrem, hreadR⟩ := hremainder_runs n seed hn ivF ch
  obtain ⟨σf, hrunT, hFSf⟩ := transfer_seg11 hFSd hrem
    (renCfg_hanchor d) (renCfg_stop11 d)
  have hread := hFSf.lookup_some (l := .base ⟨2⟩) (c := ucell 1) hreadR
  have hren : renameLoc (ρ11 d) (.base ⟨2⟩) = .base ⟨2⟩ := by
    simp [renameLoc, ρ11]
  rw [hren] at hread
  -- the chain
  have h1 := stepFnIter_chain hA1 (stepFnIter_one hmk)
  have h2 := stepFnIter_chain h1 hA2
  have h3 := stepFnIter_chain h2 hd0
  have h4 := stepFnIter_chain h3 hsetup
  have h5 := stepFnIter_chain h4 hbr
  have h6 := stepFnIter_chain h5 hO0
  have h7 := stepFnIter_chain h6 (stepFnIter_one hlenapp)
  have h8 := stepFnIter_chain h7 hOB
  have h9 := stepFnIter_chain h8 hsubj
  have h10 := stepFnIter_chain h9 hrunT
  refine ⟨10 + 1 + 42 + 25 + 57 * (n - 0) + 40 + 25 + 1 + 1 + k1 + k2,
    σf, ?_, h10, hread⟩
  have hmuls : (92 * n + 160) * (n - (0 + 1)) ≤ (92 * n + 160) * n :=
    Nat.mul_le_mul_left _ (by omega)
  omega


end GoLean.Examples.InsertionSort
