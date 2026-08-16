import GoLeanProofs.Examples.SelectionSort.Post

/-!
# SelectionSort — Run (the full harness composition)

Phase A (canonical = true placement) → the subject outer loop over the
TRUE placement (`outer_loop`, the pass-rebase induction) → the post
phase, proven canonically and transferred through the surviving frame
simulation in ONE `transfer_seg16` application. The conclusion pins
the two result cells of the true terminal state — everything the root
needs for the headline readout.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.Frame
open GoLean.Examples.SortShared

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- **The harness run, end to end**: within
`(67·n + 145)·n + 174·n + 318` steps the run reaches the driver
terminal; the true terminal state holds the padded family in `$res0`
and a padded SORTED, count-preserving list in `$res1`. -/
theorem selsortH_runs (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState) (lf : List Int),
      k ≤ (67 * n + 145) * n + 174 * n + 318 ∧
      stepFnIter k (σS (hp0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4)
        sHC₀ ch
        = .ok (.next .stop, σf, ch)
      ∧ lf.length = n ∧ Sorted lf
      ∧ (∀ v : Int, lf.count v = (selFam n seed).count v)
      ∧ Heap.lookup σf.heap (.base ⟨2⟩)
          = some (sArr8 (selPad8 (selFam n seed)))
      ∧ Heap.lookup σf.heap (.base ⟨3⟩) = some (sArr8 (selPad8 lf)) := by
  -- phase A
  have hA := sA_runs n seed hcap hseed ch
  -- the first outer dispatch
  have hO0 := o_A0_raw n seed (selFam n seed) 0 [] 16 ch
  have hlen0 := stepFnIter_one
    (o_len_step n seed (selFam n seed) 0 [] 16 ch)
  have hOB := o_OB_raw n seed (selFam n seed) 0 [] 16 ch
  have h1 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hA
    hO0) hlen0) hOB
  -- the subject loop over the true placement (trivial frame at entry)
  have hFS0 : FrameSim (ρ16 (3 * 0)) 16 (16 + 3 * 0) []
      (σOut n seed (selFam n seed) ((0 : Nat) : Int) false)
      (σOut n seed (selFam n seed) 0 false) :=
    frameSim_zero16 n seed (selFam n seed) 0 false
  obtain ⟨k1, σA', d, fr', lf, hk1, hrun1, hlf1, hlf2, hlf3, hlf4,
    hFSf⟩ := outer_loop n seed (selFam n seed) hcap (n - 0) 0
    (selFam n seed) (σOut n seed (selFam n seed) 0 false) [] rfl
    (by omega) (lcgFamily_length lcgA lcgB n seed)
    (lcgFamily_range lcgA lcgB n seed) (fun v => rfl)
    (prefixSorted_zero _) (prefixLE_zero _) hFS0 ch
  rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl] at hrun1
  have h2 := stepFnIter_chain h1 hrun1
  -- the post phase, canonical, transferred once
  have hpost := post_runs n seed lf ((n : Nat) : Int) hlf1 hcap hlf2 ch
  obtain ⟨σf, hrunT, hFSend⟩ := transfer_seg16 hFSf hpost
    (renCfg_anchor16 d) (renCfg_stop16 d)
  have h3 := stepFnIter_chain h2 hrunT
  -- the result-cell lookups through the final frame simulation
  have hren2 : renameLoc (ρ16 d) (.base ⟨2⟩) = .base ⟨2⟩ := by
    simp [renameLoc, ρ16, ρT]
  have hren3 : renameLoc (ρ16 d) (.base ⟨3⟩) = .base ⟨3⟩ := by
    simp [renameLoc, ρ16, ρT]
  have hlook2 := hFSend.lookup_some (l := .base ⟨2⟩)
    (c := sArr8 (selPad8 (selFam n seed))) rfl
  rw [hren2, renCell_arr16] at hlook2
  have hlook3 := hFSend.lookup_some (l := .base ⟨3⟩)
    (c := sArr8 (selPad8 lf)) rfl
  rw [hren3, renCell_arr16] at hlook3
  refine ⟨121 * n + 195 + 25 + 1 + 1 + k1 + (53 * n + 88), σf, lf, ?_,
    h3, hlf1, hlf4, hlf3, hlook2, hlook3⟩
  have hmul : (67 * n + 145) * (n - 0) ≤ (67 * n + 145) * n :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end GoLean.Examples.SelectionSort
