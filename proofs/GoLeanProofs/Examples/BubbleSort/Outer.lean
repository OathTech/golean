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
  -- WP arc s1.5b: the per-example `strongRecOn` scaffold replaced by
  -- ONE `FuelMeasure.stepFnIter_iterate_bail_rel` instantiation. This
  -- is the FRAME-INTERLEAVED case the s1 park record graded as not
  -- fitting the deterministic schema: the successor state is
  -- existential through `transfer_seg16`/`rebaseSim16`, so the whole
  -- loop state (current list, shift `d`, frame `fr`, the FrameSim
  -- itself) enters as the relational descriptor `S`; the pass cost is
  -- existentially bounded and enters through the measure `B`.
  -- Statement unchanged.
  intro μ e l σA d fr hμ he hln hI hrl hFS ch
  have key := stepFnIter_iterate_bail_rel (n := μ)
    (S := fun j σj => ∃ (lj : List Int) (dj : Nat) (frj : Heap),
      lj.length = n ∧ BubbleInv l0 lj (e - j)
      ∧ (∀ x ∈ lj, 0 ≤ x ∧ x < 2 ^ 64)
      ∧ FrameSim (ρ16 dj) 16 (16 + dj) frj
          (σBOut n seed lj ((e - j : Nat) : Int) false) σj)
    (C := fun j => .retV (.bool (decide (1 < ((e - j : Nat) : Int))))
      bOuterCmpK)
    (B := fun j => (105 * n + 116) * (μ - j) + 8)
    (Q := fun cf Tf => cf = .next bAfterCallK
      ∧ ∃ (d' : Nat) (fr' : Heap) (endF : Int),
        FrameSim (ρ16 d') 16 (16 + d') fr'
          (σBOut n seed (GoLean.Examples.InsertionSort.sortSpec l0)
            endF false) Tf)
    (hstep := fun j hj σj hS ch' => by
      obtain ⟨lj, dj, frj, hlnj, hIj, hrlj, hFSj⟩ := hS
      have h2 : 2 ≤ e - j := by omega
      rw [show (decide ((1 : Int) < ((e - j : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast (by omega : 1 < e - j))]
      by_cases hsw : passB lj (e - j - 1) = true
      · -- the pass swapped: rebase, one iterate at end = e - j - 1
        right
        obtain ⟨kp, hkp, hpass⟩ := bPass_swapped n seed lj (e - j) hn
          hlnj h2 (by omega) hrlj hsw ch'
        obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFSj hpass
          (renCfg_bcmp dj true) (renCfg_bcmp dj _)
        have hFS2 := rebaseSim16 hFS'
        have hI' : BubbleInv l0 (passL lj (e - j - 1)) (e - j - 1) :=
          bubbleInv_pass hIj h2 (by omega)
        have hrl' : ∀ x ∈ passL lj (e - j - 1), 0 ≤ x ∧ x < 2 ^ 64 :=
          fun x hx => hrlj x (passL_mem (by omega) hx)
        refine ⟨σA', kp,
          ⟨passL lj (e - j - 1), dj + 3, _,
            (by rw [passL_length]; exact hlnj), hI', hrl', hFS2⟩,
          ?_, ?_⟩
        · have hkpn : kp ≤ 105 * n + 116 := by
            have : 105 * (e - j) ≤ 105 * n := Nat.mul_le_mul_left _
              (by omega)
            omega
          have hni : μ - j = (μ - (j + 1)) + 1 := by omega
          have hB : (105 * n + 116) * ((μ - (j + 1)) + 1)
              = (105 * n + 116) * (μ - (j + 1)) + (105 * n + 116) :=
            Nat.mul_succ _ _
          rw [hni]
          omega
        · exact hrunA
      · -- the swap-free pass: the EARLY RETURN — the bail exit
        left
        have hsw' : passB lj (e - j - 1) = false :=
          Bool.eq_false_iff.mpr hsw
        obtain ⟨kp, hkp, hpass⟩ := bPass_early n seed lj (e - j) hn
          hlnj h2 (by omega) hrlj hsw' ch'
        obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFSj hpass
          (renCfg_bcmp dj true) (renCfg_banchor dj)
        have hFS2 := rebaseSim16 hFS'
        have hsorted : lj = GoLean.Examples.InsertionSort.sortSpec l0 :=
          bubbleInv_conclude hIj
            (bubbleInv_earlyExit hIj h2 (by omega) hsw')
        rw [hsorted] at hFS2
        refine ⟨.next bAfterCallK, σA',
          ⟨rfl, dj + 3, _, ((e - j : Nat) : Int), hFS2⟩, kp, ?_, hrunA⟩
        have : 105 * (e - j) ≤ 105 * n := Nat.mul_le_mul_left _
          (by omega)
        have hge : 105 * n + 116 ≤ (105 * n + 116) * (μ - j) :=
          Nat.le_mul_of_pos_right _ (by omega)
        omega)
    (hexit := fun σj hS ch' => by
      obtain ⟨lj, dj, frj, hlnj, hIj, hrlj, hFSj⟩ := hS
      rw [show (decide ((1 : Int) < ((e - μ : Nat) : Int))) = false from
        decide_eq_false (by exact_mod_cast (by omega : ¬ (1 < e - μ)))]
      have hX := bO_exit_raw n seed lj ((e - μ : Nat) : Int) [] 16 ch'
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFSj hX
        (renCfg_bcmp dj false) (renCfg_banchor dj)
      have hsorted : lj = GoLean.Examples.InsertionSort.sortSpec l0 :=
        bubbleInv_conclude hIj (bubbleInv_finalExit hIj (by omega))
      rw [hsorted] at hFS'
      exact ⟨.next bAfterCallK, σA',
        ⟨rfl, dj, frj, ((e - μ : Nat) : Int), hFS'⟩, 8, by omega,
        hrunA⟩)
  obtain ⟨cf, Tf, ⟨rfl, d', fr', endF, hFSf⟩, k, hk, hrun⟩ :=
    key 0 (by omega) σA ⟨l, d, fr, hln, hI, hrl, hFS⟩ ch
  exact ⟨k, Tf, d', fr', endF, hk, hrun, hFSf⟩

end GoLean.Examples.BubbleSort
