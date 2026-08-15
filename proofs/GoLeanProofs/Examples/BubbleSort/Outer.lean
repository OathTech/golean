import GoLeanProofs.Examples.BubbleSort.Frame

/-!
# BubbleSort — the outer induction (both exits, over the true placement)

The subject's outer loop over the true (garbage-laden) placement: each
pass is transferred from the tight placement (`transfer_seg16`), the
retired `swapped`/`i`/`$forFirst` triple is rebased into the frame
(`rebaseSim16`), and BOTH ways out — the counter exit `end ≤ 1` and
the early return on a swap-free pass — land on the same post-call
anchor `.next bAfterCallK` with the backing list equal to
`sortSpec l0` (the pure invariant `BubbleInv` discharges each exit).
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-- **The subject outer loop**: from the outer exit-test delivery at
`end = e`, the run reaches the post-call anchor with the backing FULLY
SORTED — `sortSpec l0`, the unique sorted permutation of the pass-0
list — delivering the surviving frame simulation (existential shift
`d'`, frame `fr'`, parked `end` value `endF`). -/
theorem bOuter_loop (n seed : Nat) (l0 : List Int)
    (hn : n < 2 ^ 63) (hl0 : l0.length = n)
    (hr0 : ∀ x ∈ l0, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ μ e (l : List Int) (σA : ExecState) (d : Nat) (fr : Heap),
      μ = e - 1 → e ≤ n → l.length = n →
      BubbleInv l0 l e → (∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) →
      FrameSim (ρ16 d) 16 (16 + d) fr
        (σBOut n seed l ((e : Nat) : Int) false) σA →
      ∀ ch : Choices,
      ∃ (k : Nat) (σA' : ExecState) (d' : Nat) (fr' : Heap) (endF : Int),
        k ≤ (105 * n + 116) * μ + 8 ∧
        stepFnIter k σA
          (.retV (.bool (decide (1 < ((e : Nat) : Int)))) bOuterCmpK) ch
          = .ok (.next bAfterCallK, σA', ch)
        ∧ FrameSim (ρ16 d') 16 (16 + d') fr'
            (σBOut n seed (GoLean.Examples.InsertionSort.sortSpec l0)
              endF false) σA' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro e l σA d fr hμ he hln hI hrl hFS ch
    subst hμ
    rcases Nat.lt_or_ge e 2 with h1 | h2
    · -- the counter exit: end ≤ 1, the whole list is already sorted
      rw [show (decide ((1 : Int) < ((e : Nat) : Int))) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (1 < e)))]
      have hX := bO_exit_raw n seed l ((e : Nat) : Int) [] 16 ch
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFS hX
        (renCfg_bcmp d false) (renCfg_banchor d)
      have hsorted : l = GoLean.Examples.InsertionSort.sortSpec l0 :=
        bubbleInv_conclude hI (bubbleInv_finalExit hI (by omega))
      rw [hsorted] at hFS'
      exact ⟨8, σA', d, fr, ((e : Nat) : Int), by omega, hrunA, hFS'⟩
    · -- one pass
      rw [show (decide ((1 : Int) < ((e : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast (by omega : 1 < e))]
      by_cases hsw : passB l (e - 1) = true
      · -- the pass swapped: rebase and recurse at end = e - 1
        obtain ⟨kp, hkp, hpass⟩ := bPass_swapped n seed l e hn hln h2
          (by omega) hrl hsw ch
        obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFS hpass
          (renCfg_bcmp d true) (renCfg_bcmp d _)
        have hFS2 := rebaseSim16 hFS'
        have hI' : BubbleInv l0 (passL l (e - 1)) (e - 1) :=
          bubbleInv_pass hI h2 (by omega)
        have hrl' : ∀ x ∈ passL l (e - 1), 0 ≤ x ∧ x < 2 ^ 64 :=
          fun x hx => hrl x (passL_mem (by omega) hx)
        obtain ⟨k, σA'', d', fr', endF, hk, hrun, hFSf⟩ := ih (e - 2)
          (by omega) (e - 1) (passL l (e - 1)) σA' (d + 3) _ (by omega)
          (by omega) (by rw [passL_length]; exact hln) hI' hrl' hFS2 ch
        refine ⟨kp + k, σA'', d', fr', endF, ?_,
          stepFnIter_chain hrunA hrun, hFSf⟩
        have hkpn : kp ≤ 105 * n + 116 := by
          have : 105 * e ≤ 105 * n := Nat.mul_le_mul_left _ he
          omega
        have hmul : (105 * n + 116) * (e - 2) + (105 * n + 116)
            = (105 * n + 116) * (e - 1) := by
          rw [← Nat.mul_succ]
          congr 1
          omega
        omega
      · -- the swap-free pass: the EARLY RETURN, the list is sorted
        have hsw' : passB l (e - 1) = false := Bool.eq_false_iff.mpr hsw
        obtain ⟨kp, hkp, hpass⟩ := bPass_early n seed l e hn hln h2
          (by omega) hrl hsw' ch
        obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFS hpass
          (renCfg_bcmp d true) (renCfg_banchor d)
        have hFS2 := rebaseSim16 hFS'
        have hsorted : l = GoLean.Examples.InsertionSort.sortSpec l0 :=
          bubbleInv_conclude hI (bubbleInv_earlyExit hI h2 (by omega) hsw')
        rw [hsorted] at hFS2
        refine ⟨kp, σA', d + 3, _, ((e : Nat) : Int), ?_, hrunA, hFS2⟩
        have : 105 * e ≤ 105 * n := Nat.mul_le_mul_left _ he
        have hμ1 : 1 ≤ e - 1 := by omega
        have : (105 * n + 116) * 1 ≤ (105 * n + 116) * (e - 1) :=
          Nat.mul_le_mul_left _ hμ1
        omega

end GoLean.Examples.BubbleSort
