import GoLeanProofs.Examples.BubbleSort.Subject
import GoLeanProofs.Frame.Threshold

/-!
# BubbleSort — the per-pass frame layer (threshold 16, retire 3)

The machine allocates a FRESH `swapped`/`i`/`$forFirst` triple on every
outer pass (`nextAddr` grows by 3 per pass; the dead cells stay in the
heap), so fixed-address raw segments cannot describe the outer loop at
a single placement. This is InsertionSort's `ρ11`/`rebaseSim11` layer
(itself the canonical `ρsh`/`rebaseSim`), re-derived at the bubble
prefix: SIXTEEN fixed cells (0–15), pass-local region from 16, THREE
retired cells per pass.

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST
-- (bubble)): this is the FIFTH hand-instantiation of the identical
-- shift/rebase construction (canonical ρsh @ 4/2, isort harness
-- ρ11 @ 11/2, isort count layer ρ21 @ 21, selsort ρ16 @ 16/3, bubble
-- ρ16 @ 16/3); the kit wants it once, parameterized by threshold and
-- retire list. [Site count corrected 2026-08-16 by the post-autonomy
-- audit: this said "third", counting only isort's first two copies.]
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-- The per-pass shift (the kit's `ρT` at threshold 16 — WP arc s1
lift 4: the shift/rebase layer now lives in `Frame/Threshold.lean`;
this wrapper keeps every downstream statement unchanged). -/
def ρ16 (d : Nat) : Nat → Nat := ρT 16 d

theorem base_neB {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := base_ne_of_ne h

/-! ## Rename-invariance of the fixed cells -/

theorem renCell_arr8B (ρ : Nat → Nat) (l : List Int) :
    renameCell ρ (bArr8 l) = bArr8 l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_backB (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (bBack n l) = bBack n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_handleB (d n : Nat) :
    renameCell (ρ16 d) (bHandle n) = bHandle n := by
  simp [renameCell, renameValue, renameLoc, ρ16, ρT]

/-- The function table carries no address literals, so every `ρ` fixes
the bodies. -/
theorem bodies_ρ16 (ρ : Nat → Nat) :
    ∀ f ∈ (σBOut 0 0 [] 0 false).functions.toList,
      renameStmt ρ f.body = f.body :=
  renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
    (by decide : funcListSup bubbleLowered.funcs.toList ≤ 0)

/-! ## Empty-region lookups -/

theorem lookup_σBOut_ge {n seed : Nat} {l : List Int} {endv : Int}
    {ffv : Bool} {a : Nat} (ha : 16 ≤ a) :
    Heap.lookup (σBOut n seed l endv ffv).heap (.base ⟨a⟩) = none := by
  simp [σBOut, σBOutT, σB, bHeapSubj, bHeapCp, bHeapSu, bHeap0,
    Heap.lookup,
    beq_false_of_ne (base_neB (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (5 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (6 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (7 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (8 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (9 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (10 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (11 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (12 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (13 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (14 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (15 : Nat) ≠ a by omega))]

theorem lookup_σBIn_ge {n seed : Nat} {l : List Int} {endv iv : Int}
    {swv ffIv : Bool} {a : Nat} (ha : 19 ≤ a) :
    Heap.lookup (σBIn n seed l endv iv swv ffIv).heap (.base ⟨a⟩)
      = none := by
  simp [σBIn, σBOutT, σB, bHeapSubj, bHeapCp, bHeapSu, bHeap0,
    Heap.lookup,
    beq_false_of_ne (base_neB (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (5 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (6 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (7 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (8 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (9 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (10 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (11 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (12 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (13 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (14 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (15 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (16 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (17 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_neB (show (18 : Nat) ≠ a by omega))]

theorem lookup_σBOut_field (n seed : Nat) (l : List Int) (endv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σBOut n seed l endv ffv).heap (.field b tid f)
      = none := rfl

theorem lookup_σBOut_index (n seed : Nat) (l : List Int) (endv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σBOut n seed l endv ffv).heap (.index b i) = none := rfl

theorem lookup_σBIn_field (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σBIn n seed l endv iv swv ffIv).heap (.field b tid f)
      = none := rfl

theorem lookup_σBIn_index (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σBIn n seed l endv iv swv ffIv).heap (.index b i)
      = none := rfl

/-! ## The trivial-frame simulation at the subject entry -/

theorem frameSim_zero16 (n seed : Nat) (l : List Int) (endv : Int)
    (ffv : Bool) :
    FrameSim (ρ16 0) 16 16 [] (σBOut n seed l endv ffv)
      (σBOut n seed l endv ffv) :=
  frameSim_seed rfl (bodies_ρ16 (ρT 16 0))

/-- **The frame rebase at threshold 16**: the pass's retired
`swapped`/`i`/`$forFirst` cells (canonical 16/17/18) move INTO the
frame at their true addresses (the kit's `retiredFrame` spelling; one
`rebaseSimT` application plus this example's fixed-cell enumeration —
WP arc s1 lift 4). -/
theorem rebaseSim16 {d : Nat} {fr : Heap} {n seed : Nat}
    {l : List Int} {endv iv : Int} {swv : Bool} {σA : ExecState}
    (h : FrameSim (ρ16 d) 16 (16 + d) fr
      (σBIn n seed l endv iv swv false) σA) :
    FrameSim (ρ16 (d + 3)) 16 (16 + (d + 3))
      (fr ++ retiredFrame (16 + d) [bbool swv, bint iv, bbool false])
      (σBOut n seed l endv false) σA := by
  refine rebaseSimT (retired := [bbool swv, bint iv, bbool false]) h
    rfl rfl rfl rfl rfl rfl ?_ ?_
    (fun a ha => lookup_σBIn_ge (by simpa using ha))
    (fun a ha => lookup_σBOut_ge ha)
    ⟨fun b tid f => lookup_σBIn_field n seed l endv iv swv false b tid f,
     fun b i => lookup_σBIn_index n seed l endv iv swv false b i⟩
    ⟨fun b tid f => lookup_σBOut_field n seed l endv false b tid f,
     fun b i => lookup_σBOut_index n seed l endv false b i⟩
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
        cases hc; exact fun d' => renCell_arr8B _ _⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_arr8B _ _⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handleB d' n⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_backB _ n l⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handleB d' n⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_arr8B _ _⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by
        cases hc; exact fun d' => renCell_handleB d' n⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
    · exact ⟨rfl, fun c hc => by cases hc; exact fun d' => rfl⟩
  · -- the retired triple sits at 16/17/18
    intro j hj
    match j, hj with
    | 0, _ => exact ⟨rfl, fun d' => rfl⟩
    | 1, _ => exact ⟨rfl, fun d' => rfl⟩
    | 2, _ => exact ⟨rfl, fun d' => rfl⟩

/-! ## Shift-fixed configurations and the transfer -/

theorem renCfg_bcmp (d : Nat) (b : Bool) :
    renameConfig (ρ16 d) (.retV (.bool b) bOuterCmpK)
      = .retV (.bool b) bOuterCmpK := by
  with_unfolding_all rfl

theorem renCfg_banchor (d : Nat) :
    renameConfig (ρ16 d) (.next bAfterCallK) = .next bAfterCallK := by
  with_unfolding_all rfl

theorem renCfg_bstop (d : Nat) :
    renameConfig (ρ16 d) (.next .stop) = .next .stop := rfl

/-- A canonical segment between shift-fixed configurations transfers
to the true placement (threshold-16 instance). -/
theorem transfer_seg16 {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρ16 d) 16 (16 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρ16 d) c = c)
    (hc' : renameConfig (ρ16 d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρ16 d) 16 (16 + d) fr σC' σA' :=
  transfer_segT hFS hrun hc hc'

end GoLean.Examples.BubbleSort
