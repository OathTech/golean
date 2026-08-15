import GoLeanProofs.Examples.BubbleSort.Subject

/-!
# BubbleSort — the per-pass frame layer (threshold 16, retire 3)

The machine allocates a FRESH `swapped`/`i`/`$forFirst` triple on every
outer pass (`nextAddr` grows by 3 per pass; the dead cells stay in the
heap), so fixed-address raw segments cannot describe the outer loop at
a single placement. This is InsertionSort's `ρ11`/`rebaseSim11` layer
(itself the canonical `ρsh`/`rebaseSim`), re-derived at the bubble
prefix: SIXTEEN fixed cells (0–15), pass-local region from 16, THREE
retired cells per pass.

-- KIT-GAP WITNESS (see .tmp/kitgaps-bubble.md): this is the third
hand-instantiation of the identical shift/rebase construction
(canonical ρsh @ 4/2, isort harness ρ11 @ 11/2, bubble ρ16 @ 16/3);
the kit wants it once, parameterized by threshold and retire list.
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

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

theorem base_neB {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := by
  intro hc
  simp only [Loc.base.injEq, Addr.mk.injEq] at hc
  exact h hc

/-- Lookup distributes over heap append. -/
theorem lookup_appendB (h1 h2 : Heap) (l : Loc) :
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

/-! ## Rename-invariance of the fixed cells -/

theorem renCell_arr8B (ρ : Nat → Nat) (l : List Int) :
    renameCell ρ (bArr8 l) = bArr8 l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_backB (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (bBack n l) = bBack n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

theorem renCell_handleB (d n : Nat) :
    renameCell (ρ16 d) (bHandle n) = bHandle n := by
  simp [renameCell, renameValue, renameLoc, ρ16]

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
      (σBOut n seed l endv ffv) := by
  refine ⟨shiftSpec_ρ16 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 16,
    ?_, ?_, fun a => rfl, bodies_ρ16 (ρ16 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 => rfl
        | 1 => rfl
        | 2 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 2⟩)
              = some (renameCell (ρ16 0) (bArr8 zeros8))
            rw [renCell_arr8B]
            rfl
        | 3 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 3⟩)
              = some (renameCell (ρ16 0) (bArr8 zeros8))
            rw [renCell_arr8B]
            rfl
        | 4 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 4⟩)
              = some (renameCell (ρ16 0) (bHandle n))
            rw [renCell_handleB]
            rfl
        | 5 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 5⟩)
              = some (renameCell (ρ16 0) (bBack n l))
            rw [renCell_backB]
            rfl
        | 6 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 6⟩)
              = some (renameCell (ρ16 0) (bHandle n))
            rw [renCell_handleB]
            rfl
        | 7 => rfl
        | 8 => rfl
        | 9 => rfl
        | 10 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 10⟩)
              = some (renameCell (ρ16 0) (bArr8 (bubPre n seed)))
            rw [renCell_arr8B]
            rfl
        | 11 => rfl
        | 12 => rfl
        | 13 =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
                (.base ⟨ρ16 0 13⟩)
              = some (renameCell (ρ16 0) (bHandle n))
            rw [renCell_handleB]
            rfl
        | 14 => rfl
        | 15 => rfl
        | (a + 16) =>
            show Heap.lookup (σBOut n seed l endv ffv).heap
              (.base ⟨ρ16 0 (a + 16)⟩) = _
            rw [ρ16_ge (d := 0) (a := a + 16) (by omega)]
            rw [lookup_σBOut_ge (a := a + 16 + 0) (by omega)]
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

/-- Root bump by 3 above the fixed cells (threshold 16). -/
def bump3B : Loc → Loc
  | .base a => .base ⟨if a.id < 16 then a.id else a.id + 3⟩
  | .field b tid f => .field (bump3B b) tid f
  | .index b i => .index (bump3B b) i

theorem renameLoc_bump3B (d : Nat) (l : Loc) :
    renameLoc (ρ16 (d + 3)) l = renameLoc (ρ16 d) (bump3B l) := by
  induction l with
  | base a =>
      have h : ρ16 (d + 3) a.id
          = ρ16 d (if a.id < 16 then a.id else a.id + 3) := by
        by_cases ha : a.id < 16
        · rw [if_pos ha, ρ16_lt ha, ρ16_lt ha]
        · rw [if_neg ha, ρ16_ge (d := d + 3) (a := a.id) (by omega),
            ρ16_ge (d := d) (a := a.id + 3) (by omega)]
          omega
      simp only [renameLoc, bump3B, h]
  | field b tid f ih => simp only [renameLoc, bump3B, ih]
  | index b i ih => simp only [renameLoc, bump3B, ih]

/-- **The frame rebase at threshold 16**: the pass's retired
`swapped`/`i`/`$forFirst` cells (canonical 16/17/18) move INTO the
frame at their true addresses `16+d`/`17+d`/`18+d`. -/
theorem rebaseSim16 {d : Nat} {fr : Heap} {n seed : Nat}
    {l : List Int} {endv iv : Int} {swv : Bool} {σA : ExecState}
    (h : FrameSim (ρ16 d) 16 (16 + d) fr
      (σBIn n seed l endv iv swv false) σA) :
    FrameSim (ρ16 (d + 3)) 16 (16 + (d + 3))
      (fr ++ [(.base ⟨16 + d⟩, bbool swv), (.base ⟨17 + d⟩, bint iv),
              (.base ⟨18 + d⟩, bbool false)])
      (σBOut n seed l endv false) σA := by
  refine ⟨shiftSpec_ρ16 (d + 3), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 16, ?_, ?_, ?_, bodies_ρ16 _⟩
  · have hne := h.next_eq
    rw [show (σBIn n seed l endv iv swv false).nextAddr = 19 from rfl,
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
              (c := bu64 ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨1⟩)
              (c := bu64 ((seed : Nat) : Int)) rfl
          · have himg := h.lookup_some (l := .base ⟨2⟩)
              (c := bArr8 zeros8) rfl
            rw [renCell_arr8B] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 2⟩)
              = some (renameCell (ρ16 (d + 3)) (bArr8 zeros8))
            rw [renCell_arr8B]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨3⟩)
              (c := bArr8 zeros8) rfl
            rw [renCell_arr8B] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 3⟩)
              = some (renameCell (ρ16 (d + 3)) (bArr8 zeros8))
            rw [renCell_arr8B]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨4⟩)
              (c := bHandle n) rfl
            rw [renCell_handleB] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 4⟩)
              = some (renameCell (ρ16 (d + 3)) (bHandle n))
            rw [renCell_handleB]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨5⟩)
              (c := bBack n l) rfl
            rw [renCell_backB] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 5⟩)
              = some (renameCell (ρ16 (d + 3)) (bBack n l))
            rw [renCell_backB]
            exact himg
          · have himg := h.lookup_some (l := .base ⟨6⟩)
              (c := bHandle n) rfl
            rw [renCell_handleB] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 6⟩)
              = some (renameCell (ρ16 (d + 3)) (bHandle n))
            rw [renCell_handleB]
            exact himg
          · exact h.lookup_some (l := .base ⟨7⟩)
              (c := bu64 (bubX n seed)) rfl
          · exact h.lookup_some (l := .base ⟨8⟩)
              (c := bu64 ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨9⟩) (c := bbool false) rfl
          · have himg := h.lookup_some (l := .base ⟨10⟩)
              (c := bArr8 (bubPre n seed)) rfl
            rw [renCell_arr8B] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 10⟩)
              = some (renameCell (ρ16 (d + 3)) (bArr8 (bubPre n seed)))
            rw [renCell_arr8B]
            exact himg
          · exact h.lookup_some (l := .base ⟨11⟩)
              (c := bu64 ((n : Nat) : Int)) rfl
          · exact h.lookup_some (l := .base ⟨12⟩) (c := bbool false) rfl
          · have himg := h.lookup_some (l := .base ⟨13⟩)
              (c := bHandle n) rfl
            rw [renCell_handleB] at himg
            show Heap.lookup σA.heap (.base ⟨ρ16 (d + 3) 13⟩)
              = some (renameCell (ρ16 (d + 3)) (bHandle n))
            rw [renCell_handleB]
            exact himg
          · exact h.lookup_some (l := .base ⟨14⟩) (c := bint endv) rfl
          · exact h.lookup_some (l := .base ⟨15⟩) (c := bbool false) rfl
        · have himg := fs_lookup_none16 h (l := .base ⟨a + 3⟩)
            (lookup_σBIn_ge (by omega))
          have hren1 : renameLoc (ρ16 d) (.base ⟨a + 3⟩)
              = .base ⟨a + 3 + d⟩ := by
            simp [renameLoc, ρ16_ge (d := d) (a := a + 3) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρ16 (d + 3)) (.base ⟨a⟩)
              = .base ⟨a + (d + 3)⟩ := by
            simp [renameLoc, ρ16_ge (d := d + 3) (a := a) (by omega)]
          rw [hren2, lookup_σBOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 3)⟩)
            = Heap.lookup (fr ++ [(.base ⟨16 + d⟩, bbool swv),
                (.base ⟨17 + d⟩, bint iv), (.base ⟨18 + d⟩, bbool false)])
              (.base ⟨a + (d + 3)⟩)
          rw [show a + (d + 3) = a + 3 + d from by omega, himg,
            lookup_appendB]
          cases hfr : Heap.lookup fr (.base ⟨a + 3 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨16 + d⟩, bbool swv),
                    (.base ⟨17 + d⟩, bint iv),
                    (.base ⟨18 + d⟩, bbool false)] (.base ⟨a + 3 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_neB
                  (show 16 + d ≠ a + 3 + d by omega)),
                beq_false_of_ne (base_neB
                  (show 17 + d ≠ a + 3 + d by omega)),
                beq_false_of_ne (base_neB
                  (show 18 + d ≠ a + 3 + d by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none16 h (l := bump3B (.field b tid f))
          (lookup_σBIn_field n seed l endv iv swv false (bump3B b) tid f)
        rw [← renameLoc_bump3B] at himg
        show Heap.lookup σA.heap (renameLoc (ρ16 (d + 3)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨16 + d⟩, bbool swv),
              (.base ⟨17 + d⟩, bint iv), (.base ⟨18 + d⟩, bbool false)])
            (renameLoc (ρ16 (d + 3)) (.field b tid f))
        rw [himg, lookup_appendB]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ16 (d + 3)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none16 h (l := bump3B (.index b i))
          (lookup_σBIn_index n seed l endv iv swv false (bump3B b) i)
        rw [← renameLoc_bump3B] at himg
        show Heap.lookup σA.heap (renameLoc (ρ16 (d + 3)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨16 + d⟩, bbool swv),
              (.base ⟨17 + d⟩, bint iv), (.base ⟨18 + d⟩, bbool false)])
            (renameLoc (ρ16 (d + 3)) (.index b i))
        rw [himg, lookup_appendB]
        cases hfr : Heap.lookup fr
            (renameLoc (ρ16 (d + 3)) (.index b i)) with
        | some c => rfl
        | none => rfl
  · intro loc c hc
    rw [lookup_appendB] at hc
    cases hfr : Heap.lookup fr loc with
    | some c0 =>
        rw [hfr] at hc
        have hc' : some c0 = some c := hc
        injection hc' with hcc
        exact hcc ▸ h.frame_pres loc c0 hfr
    | none =>
        rw [hfr] at hc
        have hc' : Heap.lookup [(.base ⟨16 + d⟩, bbool swv),
            (.base ⟨17 + d⟩, bint iv), (.base ⟨18 + d⟩, bbool false)] loc
            = some c := hc
        by_cases h4 : (.base ⟨16 + d⟩ : Loc) = loc
        · subst h4
          have hcell : c = bbool swv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨16⟩) (c := bbool swv) rfl
        · by_cases h5 : (.base ⟨17 + d⟩ : Loc) = loc
          · subst h5
            have hcell : c = bint iv := by
              simp [Heap.lookup, beq_false_of_ne h4] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨17⟩) (c := bint iv) rfl
          · by_cases h6 : (.base ⟨18 + d⟩ : Loc) = loc
            · subst h6
              have hcell : c = bbool false := by
                simp [Heap.lookup, beq_false_of_ne h4,
                  beq_false_of_ne h5] at hc'
                exact hc'.symm
              subst hcell
              exact h.lookup_some (l := .base ⟨18⟩) (c := bbool false) rfl
            · exfalso
              simp [Heap.lookup, beq_false_of_ne h4, beq_false_of_ne h5,
                beq_false_of_ne h6] at hc'
  · intro a
    rw [lookup_appendB]
    by_cases ha : a < 16
    · rw [ρ16_lt ha]
      have h2 := h.fr_avoid a
      rw [ρ16_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨16 + d⟩, bbool swv),
          (.base ⟨17 + d⟩, bint iv), (.base ⟨18 + d⟩, bbool false)]
          (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_neB (show 16 + d ≠ a by omega)),
        beq_false_of_ne (base_neB (show 17 + d ≠ a by omega)),
        beq_false_of_ne (base_neB (show 18 + d ≠ a by omega))]
    · rw [ρ16_ge (d := d + 3) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 3)
      rw [ρ16_ge (d := d) (a := a + 3) (by omega)] at h2
      rw [show a + (d + 3) = a + 3 + d from by omega, h2]
      show Heap.lookup [(.base ⟨16 + d⟩, bbool swv),
          (.base ⟨17 + d⟩, bint iv), (.base ⟨18 + d⟩, bbool false)]
          (.base ⟨a + 3 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_neB (show 16 + d ≠ a + 3 + d by omega)),
        beq_false_of_ne (base_neB (show 17 + d ≠ a + 3 + d by omega)),
        beq_false_of_ne (base_neB (show 18 + d ≠ a + 3 + d by omega))]

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

end GoLean.Examples.BubbleSort
