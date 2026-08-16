import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
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

/-! ## The shift at threshold 16

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST
-- (selsort)): everything from here
through `transfer_seg16` is the FOURTH landed copy — of FIVE — of the
shift/rebase/transfer layer (InsertionSort carries three, at
thresholds 4/11/21; bubble's `ρ16` is the fifth); the threshold and
the retired-cell count are the
only parameters that vary. The shape wanted — `Frame.shiftAt` +
`rebaseSimAt` + `transfer_segAt`, threshold- and retire-generic — is
written out in the ledger entry. -/

/-- The per-pass shift: identity on the fixed cells `0..15`, shift by
`d` on the pass-local region. -/
def ρ16 (d : Nat) : Nat → Nat := fun x => if x < 16 then x else x + d

theorem ρ16_lt {d a : Nat} (h : a < 16) : ρ16 d a = a := if_pos h
theorem ρ16_ge {d a : Nat} (h : 16 ≤ a) : ρ16 d a = a + d :=
  if_neg (by omega)

theorem shiftSpec_ρ16 (d : Nat) : ShiftSpec (ρ16 d) 16 (16 + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρ16] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρ16]
    rw [if_neg (by omega)]
    omega

theorem base_ne16 {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := by
  intro hc
  simp only [Loc.base.injEq, Addr.mk.injEq] at hc
  exact h hc

/-- Lookup distributes over heap append (local copy of the
InsertionSort helper — another example's shard is read-only).
-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (selsort)): `lookup_append`
belongs in StepKit beside `lookup_append_left/right`. -/
theorem lookup_append16 (h1 h2 : Heap) (l : Loc) :
    Heap.lookup (h1 ++ h2) l
      = match Heap.lookup h1 l with
        | some c => some c
        | none => Heap.lookup h2 l := by
  induction h1 with
  | nil => simp [Heap.lookup]
  | cons p rest ih =>
      obtain ⟨k, c⟩ := p
      simp only [List.cons_append, Heap.lookup]
      split <;> simp [ih]

/-! ## Rename facts for the cells -/

theorem renCell_arr16 (ρ : Nat → Nat) (l : List Int) :
    renameCell ρ (sArr8 l) = sArr8 l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_back16 (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (sBack n l) = sBack n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_handle16 (d n : Nat) :
    renameCell (ρ16 d) (sHandleCell n) = sHandleCell n := by
  simp [renameCell, renameValue, renameLoc, ρ16]

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

/-! ## The bump transport between consecutive shifts -/

/-- Root bump by 3 above the fixed cells. -/
def bump3 : Loc → Loc
  | .base a => .base ⟨if a.id < 16 then a.id else a.id + 3⟩
  | .field b tid f => .field (bump3 b) tid f
  | .index b i => .index (bump3 b) i

theorem renameLoc_bump3 (d : Nat) (l : Loc) :
    renameLoc (ρ16 (d + 3)) l = renameLoc (ρ16 d) (bump3 l) := by
  induction l with
  | base a =>
      have h : ρ16 (d + 3) a.id
          = ρ16 d (if a.id < 16 then a.id else a.id + 3) := by
        by_cases ha : a.id < 16
        · rw [if_pos ha, ρ16_lt ha, ρ16_lt ha]
        · rw [if_neg ha, ρ16_ge (d := d + 3) (a := a.id) (by omega),
            ρ16_ge (d := d) (a := a.id + 3) (by omega)]
          omega
      simp only [renameLoc, bump3, h]
  | field b tid f ih => simp only [renameLoc, bump3, ih]
  | index b i ih => simp only [renameLoc, bump3, ih]

/-! ## The trivial frame at the loop entry -/

theorem frameSim_zero16 (n seed : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρ16 0) 16 16 [] (σOut n seed l iv ffv)
      (σOut n seed l iv ffv) := by
  refine ⟨shiftSpec_ρ16 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 16,
    ?_, ?_, fun a => rfl, bodies_ρ16 (ρ16 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 => rfl
        | 1 => rfl
        | 2 =>
            show Heap.lookup (σOut n seed l iv ffv).heap (.base ⟨ρ16 0 2⟩)
              = some (renameCell (ρ16 0) (sArr8 zeros8))
            rw [renCell_arr16]
            rfl
        | 3 =>
            show Heap.lookup (σOut n seed l iv ffv).heap (.base ⟨ρ16 0 3⟩)
              = some (renameCell (ρ16 0) (sArr8 zeros8))
            rw [renCell_arr16]
            rfl
        | 4 =>
            show Heap.lookup (σOut n seed l iv ffv).heap (.base ⟨ρ16 0 4⟩)
              = some (renameCell (ρ16 0) (sHandleCell n))
            rw [renCell_handle16]
            rfl
        | 5 =>
            show Heap.lookup (σOut n seed l iv ffv).heap (.base ⟨ρ16 0 5⟩)
              = some (renameCell (ρ16 0) (sBack n l))
            rw [renCell_back16]
            rfl
        | 6 =>
            show Heap.lookup (σOut n seed l iv ffv).heap (.base ⟨ρ16 0 6⟩)
              = some (renameCell (ρ16 0) (sHandleCell n))
            rw [renCell_handle16]
            rfl
        | 7 => rfl
        | 8 => rfl
        | 9 => rfl
        | 10 =>
            show Heap.lookup (σOut n seed l iv ffv).heap
                (.base ⟨ρ16 0 10⟩)
              = some (renameCell (ρ16 0) (sArr8 (selPad8 (selFam n seed))))
            rw [renCell_arr16]
            rfl
        | 11 => rfl
        | 12 => rfl
        | 13 =>
            show Heap.lookup (σOut n seed l iv ffv).heap
                (.base ⟨ρ16 0 13⟩)
              = some (renameCell (ρ16 0) (sHandleCell n))
            rw [renCell_handle16]
            rfl
        | 14 => rfl
        | 15 => rfl
        | (a + 16) =>
            show Heap.lookup (σOut n seed l iv ffv).heap
              (.base ⟨ρ16 0 (a + 16)⟩) = _
            rw [ρ16_ge (d := 0) (a := a + 16) (by omega)]
            rw [lookup_σOut_ge (a := a + 16 + 0) (by omega)]
            rfl
    | .field b tid f => rfl
    | .index b i => rfl
  · intro loc c hc
    simp [Heap.lookup] at hc

theorem fs_lookup_none16 {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (h : FrameSim ρ na₀ na fr σ σF) {l : Loc}
    (hl : Heap.lookup σ.heap l = none) :
    Heap.lookup σF.heap (renameLoc ρ l) = Heap.lookup fr (renameLoc ρ l) := by
  have h2 := h.lookup_img l
  rw [hl] at h2
  exact h2

/-! ## The frame REBASE (retire the pass triple) -/

/-- The pass's retired `m`/`j`/`$forFirst` cells (canonical 16/17/18)
move INTO the frame at their true addresses `16+d`/`17+d`/`18+d`, the
shift widens by 3, and the canonical state drops back to the 16-cell
shape. The true state `σA` is untouched — pure re-description. -/
theorem rebaseSim3 {d : Nat} {fr : Heap} {n seed : Nat}
    {l : List Int} {iv mv jv : Int} {σA : ExecState}
    (h : FrameSim (ρ16 d) 16 (16 + d) fr (σIn n seed l iv mv jv false)
      σA) :
    FrameSim (ρ16 (d + 3)) 16 (16 + (d + 3))
      (fr ++ [(.base ⟨16 + d⟩, sint mv), (.base ⟨17 + d⟩, sint jv),
        (.base ⟨18 + d⟩, sbool false)])
      (σOut n seed l iv false) σA := by
  refine ⟨shiftSpec_ρ16 (d + 3), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 16, ?_, ?_, ?_, bodies_ρ16 _⟩
  · have hne := h.next_eq
    rw [show (σIn n seed l iv mv jv false).nextAddr = 19 from rfl,
      ρ16_ge (d := d) (a := 19) (by omega)] at hne
    show σA.nextAddr = ρ16 (d + 3) 16
    rw [ρ16_ge (d := d + 3) (a := 16) (by omega)]
    omega
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < 16
        · rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4
              ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11
              ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15)
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h.lookup_some (l := .base ⟨0⟩)
              (c := su64 (n : Int)) rfl
          · exact h.lookup_some (l := .base ⟨1⟩)
              (c := su64 (seed : Int)) rfl
          · have himg := h.lookup_some (l := .base ⟨2⟩)
              (c := sArr8 zeros8) rfl
            rw [renCell_arr16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 2⟩)
              = some (renameCell (ρ16 (d + 3)) (sArr8 zeros8))
            rw [renCell_arr16]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨3⟩)
              (c := sArr8 zeros8) rfl
            rw [renCell_arr16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 3⟩)
              = some (renameCell (ρ16 (d + 3)) (sArr8 zeros8))
            rw [renCell_arr16]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨4⟩)
              (c := sHandleCell n) rfl
            rw [renCell_handle16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 4⟩)
              = some (renameCell (ρ16 (d + 3)) (sHandleCell n))
            rw [renCell_handle16]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨5⟩)
              (c := sBack n l) rfl
            rw [renCell_back16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 5⟩)
              = some (renameCell (ρ16 (d + 3)) (sBack n l))
            rw [renCell_back16]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨6⟩)
              (c := sHandleCell n) rfl
            rw [renCell_handle16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 6⟩)
              = some (renameCell (ρ16 (d + 3)) (sHandleCell n))
            rw [renCell_handle16]
            exact himg
          · exact h.lookup_some (l := .base ⟨7⟩)
              (c := su64 ((lcgStep lcgA lcgB n seed : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨8⟩)
              (c := su64 (n : Int)) rfl
          · exact h.lookup_some (l := .base ⟨9⟩) (c := sbool false) rfl
          · have himg := h.lookup_some (l := .base ⟨10⟩)
              (c := sArr8 (selPad8 (selFam n seed))) rfl
            rw [renCell_arr16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 10⟩)
              = some (renameCell (ρ16 (d + 3))
                  (sArr8 (selPad8 (selFam n seed))))
            rw [renCell_arr16]
            exact himg
          · exact h.lookup_some (l := .base ⟨11⟩)
              (c := su64 (n : Int)) rfl
          · exact h.lookup_some (l := .base ⟨12⟩) (c := sbool false) rfl
          · have himg := h.lookup_some (l := .base ⟨13⟩)
              (c := sHandleCell n) rfl
            rw [renCell_handle16] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 13⟩)
              = some (renameCell (ρ16 (d + 3)) (sHandleCell n))
            rw [renCell_handle16]
            exact himg
          · exact h.lookup_some (l := .base ⟨14⟩) (c := sint iv) rfl
          · exact h.lookup_some (l := .base ⟨15⟩) (c := sbool false) rfl
        · have himg := fs_lookup_none16 h (l := .base ⟨a + 3⟩)
            (lookup_σIn_ge (by omega))
          have hren1 : renameLoc (ρ16 d) (.base ⟨a + 3⟩)
              = .base ⟨a + 3 + d⟩ := by
            simp [renameLoc, ρ16_ge (d := d) (a := a + 3) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρ16 (d + 3)) (.base ⟨a⟩)
              = .base ⟨a + (d + 3)⟩ := by
            simp [renameLoc, ρ16_ge (d := d + 3) (a := a) (by omega)]
          rw [hren2, lookup_σOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 3)⟩)
            = Heap.lookup (fr ++ [(.base ⟨16 + d⟩, sint mv),
                (.base ⟨17 + d⟩, sint jv), (.base ⟨18 + d⟩, sbool false)])
              (.base ⟨a + (d + 3)⟩)
          rw [show a + (d + 3) = a + 3 + d from by omega, himg,
            lookup_append16]
          cases hfr : Heap.lookup fr (.base ⟨a + 3 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨16 + d⟩, sint mv),
                    (.base ⟨17 + d⟩, sint jv),
                    (.base ⟨18 + d⟩, sbool false)] (.base ⟨a + 3 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_ne16 (show 16 + d ≠ a + 3 + d
                  by omega)),
                beq_false_of_ne (base_ne16 (show 17 + d ≠ a + 3 + d
                  by omega)),
                beq_false_of_ne (base_ne16 (show 18 + d ≠ a + 3 + d
                  by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none16 h (l := bump3 (.field b tid f))
          (lookup_σIn_field n seed l iv mv jv false (bump3 b) tid f)
        rw [← renameLoc_bump3] at himg
        show Heap.lookup σA.heap (renameLoc (ρ16 (d + 3)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨16 + d⟩, sint mv),
              (.base ⟨17 + d⟩, sint jv), (.base ⟨18 + d⟩, sbool false)])
            (renameLoc (ρ16 (d + 3)) (.field b tid f))
        rw [himg, lookup_append16]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ16 (d + 3)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none16 h (l := bump3 (.index b i))
          (lookup_σIn_index n seed l iv mv jv false (bump3 b) i)
        rw [← renameLoc_bump3] at himg
        show Heap.lookup σA.heap (renameLoc (ρ16 (d + 3)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨16 + d⟩, sint mv),
              (.base ⟨17 + d⟩, sint jv), (.base ⟨18 + d⟩, sbool false)])
            (renameLoc (ρ16 (d + 3)) (.index b i))
        rw [himg, lookup_append16]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ16 (d + 3)) (.index b i)) with
        | some c => rfl
        | none => rfl
  · intro loc c hc
    rw [lookup_append16] at hc
    cases hfr : Heap.lookup fr loc with
    | some c0 =>
        rw [hfr] at hc
        have hc' : some c0 = some c := hc
        injection hc' with hcc
        exact hcc ▸ h.frame_pres loc c0 hfr
    | none =>
        rw [hfr] at hc
        have hc' : Heap.lookup [(.base ⟨16 + d⟩, sint mv),
            (.base ⟨17 + d⟩, sint jv), (.base ⟨18 + d⟩, sbool false)] loc
            = some c := hc
        by_cases h16 : (.base ⟨16 + d⟩ : Loc) = loc
        · subst h16
          have hcell : c = sint mv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨16⟩) (c := sint mv) rfl
        · by_cases h17 : (.base ⟨17 + d⟩ : Loc) = loc
          · subst h17
            have hcell : c = sint jv := by
              simp [Heap.lookup, beq_false_of_ne h16] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨17⟩) (c := sint jv) rfl
          · by_cases h18 : (.base ⟨18 + d⟩ : Loc) = loc
            · subst h18
              have hcell : c = sbool false := by
                simp [Heap.lookup, beq_false_of_ne h16,
                  beq_false_of_ne h17] at hc'
                exact hc'.symm
              subst hcell
              exact h.lookup_some (l := .base ⟨18⟩) (c := sbool false) rfl
            · exfalso
              simp [Heap.lookup, beq_false_of_ne h16,
                beq_false_of_ne h17, beq_false_of_ne h18] at hc'
  · intro a
    rw [lookup_append16]
    by_cases ha : a < 16
    · rw [ρ16_lt ha]
      have h2 := h.fr_avoid a
      rw [ρ16_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨16 + d⟩, sint mv),
          (.base ⟨17 + d⟩, sint jv), (.base ⟨18 + d⟩, sbool false)]
          (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne16 (show 16 + d ≠ a by omega)),
        beq_false_of_ne (base_ne16 (show 17 + d ≠ a by omega)),
        beq_false_of_ne (base_ne16 (show 18 + d ≠ a by omega))]
    · rw [ρ16_ge (d := d + 3) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 3)
      rw [ρ16_ge (d := d) (a := a + 3) (by omega)] at h2
      rw [show a + (d + 3) = a + 3 + d from by omega, h2]
      show Heap.lookup [(.base ⟨16 + d⟩, sint mv),
          (.base ⟨17 + d⟩, sint jv), (.base ⟨18 + d⟩, sbool false)]
          (.base ⟨a + 3 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne16 (show 16 + d ≠ a + 3 + d by omega)),
        beq_false_of_ne (base_ne16 (show 17 + d ≠ a + 3 + d by omega)),
        beq_false_of_ne (base_ne16 (show 18 + d ≠ a + 3 + d by omega))]

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
      ∧ FrameSim (ρ16 d) 16 (16 + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩

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
        (fr ++ [(.base ⟨16 + 3 * i⟩,
            sint ((minIdx l i (n - 1 - i) : Nat) : Int)),
          (.base ⟨17 + 3 * i⟩, sint ((n : Nat) : Int)),
          (.base ⟨18 + 3 * i⟩, sbool false)]) rfl (by omega)
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
