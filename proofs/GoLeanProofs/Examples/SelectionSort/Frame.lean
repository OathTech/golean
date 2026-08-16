import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Frame.Threshold
import GoLeanProofs.Examples.SelectionSort.Subject

/-!
# SelectionSort — Frame (the per-pass rebase layer and the outer loop)

The machine re-allocates `m`/`j`/`$forFirst` on EVERY outer pass
(fresh addresses at 16+3p/17+3p/18+3p; the dead triple stays in the
heap). Each pass is proven ONCE at the tight canonical placement
(`SelectionSort/Subject.lean`) and transferred to the true
(garbage-laden) placement by the executable frame theorem; between
passes the retired triple is REBASED into the frame (`rebaseSim3` —
the InsertionSort `rebaseSim11` pattern at threshold 16, retire 3).

`outer_loop` is the subject induction over the true run: invariant
`PrefixSorted l i ∧ PrefixLE l i ∧ counts preserved`, concluding at
the post-subject anchor with a SORTED, count-preserving backing and
the surviving frame simulation.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.Frame
open GoLean.Examples.SortShared

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The shift at threshold 16 — now the KIT's threshold layer
(WP arc s1 lift 4: `Frame/Threshold.lean` carries `ρT`/`bumpAt`/
`retiredFrame`/`frameSim_seed`/`rebaseSimT`/`transfer_segT`, lifted
from this file's GAP-WITNESS block and its four siblings; what remains
here is exactly the per-example residue the ledger predicted — the
fixed-cell enumeration and the program's `bodies` fact). -/

/-- The per-pass shift (the kit's `ρT` at threshold 16; kept as a
definitional wrapper so every downstream statement is unchanged). -/
def ρ16 (d : Nat) : Nat → Nat := ρT 16 d

theorem base_ne16 {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := base_ne_of_ne h

/-! ## Rename facts for the cells -/

theorem renCell_arr16 (ρ : Nat → Nat) (l : List Int) :
    renameCell ρ (sArr8 l) = sArr8 l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_back16 (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (sBack n l) = sBack n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_handle16 (d n : Nat) :
    renameCell (ρ16 d) (sHandleCell n) = sHandleCell n := by
  simp [renameCell, renameValue, renameLoc, ρ16, ρT]

/-- The function table carries no address literals, so every `ρ` fixes
the bodies. -/
theorem bodies_ρ16 (ρ : Nat → Nat) :
    ∀ f ∈ (σS [] 0).functions.toList, renameStmt ρ f.body = f.body :=
  renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
    (by decide : funcListSup selsortLowered.funcs.toList ≤ 0)

/-! ## Lookup-shape facts at the two canonical states -/

theorem lookup_σOut_ge {n seed : Nat} {l : List Int} {iv : Int}
    {ffv : Bool} {a : Nat} (ha : 16 ≤ a) :
    Heap.lookup (σOut n seed l iv ffv).heap (.base ⟨a⟩) = none := by
  simp [σOut, σOutT, hpSubj, σS, Heap.lookup,
    beq_false_of_ne (base_ne16 (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (5 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (6 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (7 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (8 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (9 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (10 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (11 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (12 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (13 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (14 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (15 : Nat) ≠ a by omega))]

theorem lookup_σIn_ge {n seed : Nat} {l : List Int} {iv mv jv : Int}
    {ffIv : Bool} {a : Nat} (ha : 19 ≤ a) :
    Heap.lookup (σIn n seed l iv mv jv ffIv).heap (.base ⟨a⟩) = none := by
  simp [σIn, σOutT, hpSubj, σS, Heap.lookup,
    beq_false_of_ne (base_ne16 (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (5 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (6 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (7 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (8 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (9 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (10 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (11 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (12 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (13 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (14 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (15 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (16 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (17 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne16 (show (18 : Nat) ≠ a by omega))]

theorem lookup_σOut_field (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σOut n seed l iv ffv).heap (.field b tid f) = none := rfl

theorem lookup_σOut_index (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σOut n seed l iv ffv).heap (.index b i) = none := rfl

theorem lookup_σIn_field (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σIn n seed l iv mv jv ffIv).heap (.field b tid f)
      = none := rfl

theorem lookup_σIn_index (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σIn n seed l iv mv jv ffIv).heap (.index b i)
      = none := rfl

/-! ## The trivial frame at the loop entry (kit `frameSim_seed`) -/

theorem frameSim_zero16 (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρ16 0) 16 16 [] (σOut n seed l iv ffv)
      (σOut n seed l iv ffv) :=
  frameSim_seed rfl (bodies_ρ16 (ρT 16 0))

/-! ## The frame REBASE (retire the pass triple; kit `rebaseSimT`) -/

/-- The pass's retired `m`/`j`/`$forFirst` cells (canonical 16/17/18)
move INTO the frame at their true addresses, the shift widens by 3,
and the canonical state drops back to the 16-cell shape. The true
state `σA` is untouched — pure re-description. (The frame spelling is
now the kit's `retiredFrame`; the proof is the ONE kit application
plus this example's fixed-cell enumeration.) -/
theorem rebaseSim3 {d : Nat} {fr : Heap} {n seed : Nat}
    {l : List Int} {iv mv jv : Int} {σA : ExecState}
    (h : FrameSim (ρ16 d) 16 (16 + d) fr (σIn n seed l iv mv jv false)
      σA) :
    FrameSim (ρ16 (d + 3)) 16 (16 + (d + 3))
      (fr ++ retiredFrame (16 + d) [sint mv, sint jv, sbool false])
      (σOut n seed l iv false) σA := by
  refine rebaseSimT (retired := [sint mv, sint jv, sbool false]) h
    rfl rfl rfl rfl rfl rfl ?_ ?_
    (fun a ha => lookup_σIn_ge (by simpa using ha))
    (fun a ha => lookup_σOut_ge ha)
    ⟨fun b tid f => lookup_σIn_field n seed l iv mv jv false b tid f,
     fun b i => lookup_σIn_index n seed l iv mv jv false b i⟩
    ⟨fun b tid f => lookup_σOut_field n seed l iv false b tid f,
     fun b i => lookup_σOut_index n seed l iv false b i⟩
    (bodies_ρ16 _)
  · -- the fixed front: agreement + threshold-fixedness, cell by cell
    intro a ha
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4
        ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11
        ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_arr16 _ _⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_arr16 _ _⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handle16 d' n⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_back16 _ n l⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handle16 d' n⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_arr16 _ _⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handle16 d' n⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
  · -- the retired triple sits at 16/17/18
    intro j hj
    match j, hj with
    | 0, _ => exact ⟨rfl, fun d' => rfl⟩
    | 1, _ => exact ⟨rfl, fun d' => rfl⟩
    | 2, _ => exact ⟨rfl, fun d' => rfl⟩

/-! ## Transfer plumbing -/

theorem renCfg_cmp16 (d : Nat) (b : Bool) :
    renameConfig (ρ16 d) (.retV (.bool b) outerCmpK)
      = .retV (.bool b) outerCmpK := by
  with_unfolding_all rfl

theorem renCfg_anchor16 (d : Nat) :
    renameConfig (ρ16 d) (.next sAfterCallK) = .next sAfterCallK := by
  with_unfolding_all rfl

theorem renCfg_stop16 (d : Nat) :
    renameConfig (ρ16 d) (.next .stop) = .next .stop := rfl

/-- A canonical segment between shift-fixed configurations transfers to
the true placement (threshold-16 instance). -/
theorem transfer_seg16 {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρ16 d) 16 (16 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρ16 d) c = c) (hc' : renameConfig (ρ16 d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρ16 d) 16 (16 + d) fr σC' σA' :=
  transfer_segT hFS hrun hc hc'

/-! ## The subject outer induction over the TRUE run -/

/-- **The subject outer loop**: from the outer test delivery at `i`
over the true (garbage-laden) placement, the run reaches the
post-subject anchor with the backing SORTED and count-preserving,
delivering the surviving frame simulation. -/
theorem outer_loop (n seed : Nat) (l0 : List Int) (hcap : n ≤ 8) :
    ∀ μ i l (σA : ExecState) (fr : Heap), μ = n - i → i ≤ n →
    l.length = n → (∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) →
    (∀ v : Int, l.count v = l0.count v) →
    PrefixSorted l i → PrefixLE l i →
    FrameSim (ρ16 (3 * i)) 16 (16 + 3 * i) fr
      (σOut n seed l ((i : Nat) : Int) false) σA →
    ∀ ch : Choices, ∃ (k : Nat) (σA' : ExecState) (d : Nat) (fr' : Heap)
      (lf : List Int),
      k ≤ (67 * n + 145) * μ + 8 ∧
      stepFnIter k σA
        (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
          outerCmpK) ch
        = .ok (.next sAfterCallK, σA', ch)
      ∧ lf.length = n ∧ (∀ x ∈ lf, 0 ≤ x ∧ x < 2 ^ 64)
      ∧ (∀ v : Int, lf.count v = l0.count v) ∧ Sorted lf
      ∧ FrameSim (ρ16 d) 16 (16 + d) fr'
          (σOut n seed lf ((n : Nat) : Int) false) σA' := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro i l σA fr hμ hin hlen hr hcnt hps hple hFS ch
    subst hμ
    rcases Nat.lt_or_ge i n with hlt | hge
    · -- one more pass
      rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true
        from decide_eq_true (by exact_mod_cast hlt)]
      obtain ⟨K, hK, hpass⟩ := pass_seg n seed l i hlen hcap hlt hr ch
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFS hpass
        (renCfg_cmp16 (3 * i) true) (renCfg_cmp16 (3 * i) _)
      have hFS2 := rebaseSim3 hFS'
      -- the pure invariant advances across the swap
      have hadv := swap_advance (l := l) (n := n) hlen hlt hps hple
      have hlen' : (swapList l i (minIdx l i (n - 1 - i))).length = n := by
        rw [swapList_length, hlen]
      have hmn : minIdx l i (n - 1 - i) < n := by
        have := minIdx_le l i (n - 1 - i)
        omega
      have hr' := range_swapList (l := l) (i := i)
        (m := minIdx l i (n - 1 - i)) (by omega) (by omega) hr
      have hcnt' : ∀ v : Int,
          (swapList l i (minIdx l i (n - 1 - i))).count v
            = l0.count v := by
        intro v
        rw [count_swapList v (by omega) (by omega), hcnt v]
      -- (n - i - 1) vs (n - 1 - i): the same index
      have hidx : n - i - 1 = n - 1 - i := by omega
      obtain ⟨k, σA'', d, fr', lf, hk, hrun, hlf1, hlf2, hlf3, hlf4,
        hFSf⟩ := ih (n - (i + 1)) (by omega) (i + 1)
        (swapList l i (minIdx l i (n - 1 - i))) σA'
        (fr ++ retiredFrame (16 + 3 * i)
          [sint ((minIdx l i (n - 1 - i) : Nat) : Int),
           sint ((n : Nat) : Int), sbool false]) rfl (by omega)
        hlen' hr' hcnt' hadv.1 hadv.2
        (by
          have h3 : 3 * i + 3 = 3 * (i + 1) := by omega
          rw [← h3]
          rw [hidx] at hFS'
          exact rebaseSim3 hFS') ch
      refine ⟨K + k, σA'', d, fr', lf, ?_, stepFnIter_chain hrunA hrun,
        hlf1, hlf2, hlf3, hlf4, hFSf⟩
      have hmul : (67 * n + 145) * (n - (i + 1)) + (67 * n + 145)
          = (67 * n + 145) * (n - i) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · -- the outer exit
      have hie : i = n := by omega
      subst hie
      rw [show (decide (((i : Nat) : Int) < ((i : Nat) : Int))) = false
        from decide_eq_false (by omega)]
      have hX := o_exit_raw i seed l ((i : Nat) : Int) [] 16 ch
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg16 hFS hX
        (renCfg_cmp16 (3 * i) false) (renCfg_anchor16 (3 * i))
      have hsort : Sorted l := sorted_of_prefixSorted (by
        rw [hlen]; exact hps)
      exact ⟨8, σA', 3 * i, fr, l, by omega, hrunA, hlen, hr, hcnt,
        hsort, hFS'⟩

end GoLean.Examples.SelectionSort
