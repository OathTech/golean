import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.InsertionSort.Canon

/-!
# InsertionSort — PassFrame

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

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The per-pass frame layer

The machine re-allocates `j`/`$forFirst` on EVERY outer pass (fresh
addresses; the dead pair stays in the heap). The outer induction
therefore relates the true run to the tight canonical states through
the executable frame theorem: `ρsh d` fixes the four active cells and
shifts the pass-local region by the accumulated garbage `d = 2m`;
after each pass `rebaseSim` retires the pass's two cells INTO the
frame. -/

open GoLean.Frame

/-- The per-pass shift: identity on the active cells `0..3`, shift by
`d` on the pass-local region. -/
def ρsh (d : Nat) : Nat → Nat := fun x => if x < 4 then x else x + d

private theorem ρsh_lt {d a : Nat} (h : a < 4) : ρsh d a = a := if_pos h
private theorem ρsh_ge {d a : Nat} (h : 4 ≤ a) : ρsh d a = a + d :=
  if_neg (by omega)

private theorem shiftSpec_ρsh (d : Nat) : ShiftSpec (ρsh d) 4 (4 + d) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [ρsh] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [ρsh]
    rw [if_neg (by omega)]
    omega

theorem renCell_arr (ρ : Nat → Nat) (n : Nat) (l : List Int) :
    renameCell ρ (arrCell n l) = arrCell n l := by
  simp [renameCell, renameValue_locFree _ _ (locSup_mapU l)]

private theorem renCell_handle (d n : Nat) :
    renameCell (ρsh d) (handleCell n) = handleCell n := by
  simp [renameCell, renameValue, renameLoc, ρsh]

theorem base_ne {x y : Nat} (h : x ≠ y) :
    (Loc.base ⟨x⟩ : Loc) ≠ .base ⟨y⟩ := by
  intro hc
  simp only [Loc.base.injEq, Addr.mk.injEq] at hc
  exact h hc

/-- Lookup distributes over heap append. -/
theorem lookup_append (h1 h2 : Heap) (l : Loc) :
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

private theorem lookup_σOut_ge {n : Nat} {l : List Int} {iv : Int}
    {ffv : Bool} {a : Nat} (ha : 4 ≤ a) :
    Heap.lookup (σOut n l iv ffv).heap (.base ⟨a⟩) = none := by
  simp [σOut, σOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega))]

private theorem lookup_σIn_ge {n : Nat} {l : List Int} {iv jv : Int}
    {ffIv : Bool} {a : Nat} (ha : 6 ≤ a) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.base ⟨a⟩) = none := by
  simp [σIn, σOutT, Heap.lookup,
    beq_false_of_ne (base_ne (show (0 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (1 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (2 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (3 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (4 : Nat) ≠ a by omega)),
    beq_false_of_ne (base_ne (show (5 : Nat) ≠ a by omega))]

private theorem lookup_σOut_field (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σOut n l iv ffv).heap (.field b tid f) = none := rfl

private theorem lookup_σOut_index (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σOut n l iv ffv).heap (.index b i) = none := rfl

private theorem lookup_σIn_field (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (tid : TypeId) (f : String) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.field b tid f) = none := rfl

private theorem lookup_σIn_index (n : Nat) (l : List Int) (iv jv : Int)
    (ffIv : Bool) (b : Loc) (i : Int) :
    Heap.lookup (σIn n l iv jv ffIv).heap (.index b i) = none := rfl

/-- The function table carries no address literals (`by decide` over
the pinned lowering), so every `ρ` fixes the bodies. -/
theorem bodies_ρsh (ρ : Nat → Nat) :
    ∀ f ∈ (σOutT 0 [] 0 false [] 0).functions.toList,
      renameStmt ρ f.body = f.body :=
  renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
    (by decide : funcListSup isortLowered.funcs.toList ≤ 0)

/-- Root bump by 2 above the active cells: the transport between
consecutive shifts (`ρsh (d+2) l = ρsh d (bump2 l)` on locations). -/
def bump2 : Loc → Loc
  | .base a => .base ⟨if a.id < 4 then a.id else a.id + 2⟩
  | .field b tid f => .field (bump2 b) tid f
  | .index b i => .index (bump2 b) i

private theorem renameLoc_bump2 (d : Nat) (l : Loc) :
    renameLoc (ρsh (d + 2)) l = renameLoc (ρsh d) (bump2 l) := by
  induction l with
  | base a =>
      have h : ρsh (d + 2) a.id = ρsh d (if a.id < 4 then a.id else a.id + 2) := by
        by_cases ha : a.id < 4
        · rw [if_pos ha, ρsh_lt ha, ρsh_lt ha]
        · rw [if_neg ha, ρsh_ge (d := d + 2) (a := a.id) (by omega),
            ρsh_ge (d := d) (a := a.id + 2) (by omega)]
          omega
      simp only [renameLoc, bump2, h]
  | field b tid f ih => simp only [renameLoc, bump2, ih]
  | index b i ih => simp only [renameLoc, bump2, ih]

/-- The trivial-frame simulation at the loop entry (`m = 0`: the true
state IS the tight state). -/
theorem frameSim_zero (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) :
    FrameSim (ρsh 0) 4 4 [] (σOut n l iv ffv) (σOut n l iv ffv) := by
  refine ⟨shiftSpec_ρsh 0, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 4,
    ?_, ?_, fun a => rfl, bodies_ρsh (ρsh 0)⟩
  · intro loc
    match loc with
    | .base ⟨a⟩ =>
        match a with
        | 0 =>
            show Heap.lookup (σOut n l iv ffv).heap (.base ⟨ρsh 0 0⟩)
              = some (renameCell (ρsh 0) (arrCell n l))
            rw [renCell_arr]
            rfl
        | 1 =>
            show Heap.lookup (σOut n l iv ffv).heap (.base ⟨ρsh 0 1⟩)
              = some (renameCell (ρsh 0) (handleCell n))
            rw [renCell_handle 0 n]
            rfl
        | 2 => rfl
        | 3 => rfl
        | (a + 4) =>
            show Heap.lookup (σOut n l iv ffv).heap (.base ⟨ρsh 0 (a + 4)⟩)
              = _
            rw [ρsh_ge (d := 0) (a := a + 4) (by omega)]
            rw [lookup_σOut_ge (a := a + 4 + 0) (by omega)]
            rfl
    | .field b tid f => rfl
    | .index b i => rfl
  · intro loc c hc
    simp [Heap.lookup] at hc

private theorem fs_lookup_none {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (h : FrameSim ρ na₀ na fr σ σF) {l : Loc}
    (hl : Heap.lookup σ.heap l = none) :
    Heap.lookup σF.heap (renameLoc ρ l) = Heap.lookup fr (renameLoc ρ l) := by
  have h2 := h.lookup_img l
  rw [hl] at h2
  exact h2

/-- **The frame REBASE** (the outer induction's between-passes step):
the pass's retired `j`/`$forFirst` cells (canonical addresses 4/5) move
INTO the frame at their true addresses `4+d`/`5+d`, the shift widens by
2, and the canonical state drops back to the tight 4-cell shape. The
true state `σA` is untouched — this is pure re-description. -/
theorem rebaseSim {d : Nat} {fr : Heap} {n : Nat} {l : List Int}
    {iv jv : Int} {σA : ExecState}
    (h : FrameSim (ρsh d) 4 (4 + d) fr (σIn n l iv jv false) σA) :
    FrameSim (ρsh (d + 2)) 4 (4 + (d + 2))
      (fr ++ [(.base ⟨4 + d⟩, intcell jv), (.base ⟨5 + d⟩, bcell false)])
      (σOut n l iv false) σA := by
  refine ⟨shiftSpec_ρsh (d + 2), h.types_eq, h.funcs_eq, h.methods_eq,
    h.methodSets_eq, ?_, Nat.le_refl 4, ?_, ?_, ?_, bodies_ρsh _⟩
  · -- next_eq
    have hne := h.next_eq
    rw [show (σIn n l iv jv false).nextAddr = 6 from rfl,
      ρsh_ge (d := d) (a := 6) (by omega)] at hne
    show σA.nextAddr = ρsh (d + 2) 4
    rw [ρsh_ge (d := d + 2) (a := 4) (by omega)]
    omega
  · -- lookup_img
    intro loc
    match loc with
    | .base ⟨a⟩ =>
        by_cases ha : a < 4
        · rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3)
            with rfl | rfl | rfl | rfl
          · have himg := h.lookup_some (l := .base ⟨0⟩) (c := arrCell n l) rfl
            rw [renCell_arr] at himg
            show Heap.lookup σA.heap (.base ⟨ρsh (d + 2) 0⟩)
              = some (renameCell (ρsh (d + 2)) (arrCell n l))
            rw [renCell_arr]
            exact himg
          · exact h.lookup_some (l := .base ⟨1⟩) (c := handleCell n) rfl
          · exact h.lookup_some (l := .base ⟨2⟩) (c := intcell iv) rfl
          · exact h.lookup_some (l := .base ⟨3⟩) (c := bcell false) rfl
        · have himg := fs_lookup_none h (l := .base ⟨a + 2⟩)
            (lookup_σIn_ge (by omega))
          have hren1 : renameLoc (ρsh d) (.base ⟨a + 2⟩)
              = .base ⟨a + 2 + d⟩ := by
            simp [renameLoc, ρsh_ge (d := d) (a := a + 2) (by omega)]
          rw [hren1] at himg
          have hren2 : renameLoc (ρsh (d + 2)) (.base ⟨a⟩)
              = .base ⟨a + (d + 2)⟩ := by
            simp [renameLoc, ρsh_ge (d := d + 2) (a := a) (by omega)]
          rw [hren2, lookup_σOut_ge (by omega)]
          show Heap.lookup σA.heap (.base ⟨a + (d + 2)⟩)
            = Heap.lookup (fr ++ [(.base ⟨4 + d⟩, intcell jv),
                (.base ⟨5 + d⟩, bcell false)]) (.base ⟨a + (d + 2)⟩)
          rw [show a + (d + 2) = a + 2 + d from by omega, himg,
            lookup_append]
          cases hfr : Heap.lookup fr (.base ⟨a + 2 + d⟩) with
          | some c => rfl
          | none =>
              show (none : Option HeapCell)
                = Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
                    (.base ⟨5 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩)
              simp [Heap.lookup,
                beq_false_of_ne (base_ne (show 4 + d ≠ a + 2 + d by omega)),
                beq_false_of_ne (base_ne (show 5 + d ≠ a + 2 + d by omega))]
    | .field b tid f =>
        have himg := fs_lookup_none h (l := bump2 (.field b tid f))
          (lookup_σIn_field n l iv jv false (bump2 b) tid f)
        rw [← renameLoc_bump2] at himg
        show Heap.lookup σA.heap (renameLoc (ρsh (d + 2)) (.field b tid f))
          = Heap.lookup (fr ++ [(.base ⟨4 + d⟩, intcell jv),
              (.base ⟨5 + d⟩, bcell false)])
            (renameLoc (ρsh (d + 2)) (.field b tid f))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρsh (d + 2)) (.field b tid f)) with
        | some c => rfl
        | none => rfl
    | .index b i =>
        have himg := fs_lookup_none h (l := bump2 (.index b i))
          (lookup_σIn_index n l iv jv false (bump2 b) i)
        rw [← renameLoc_bump2] at himg
        show Heap.lookup σA.heap (renameLoc (ρsh (d + 2)) (.index b i))
          = Heap.lookup (fr ++ [(.base ⟨4 + d⟩, intcell jv),
              (.base ⟨5 + d⟩, bcell false)])
            (renameLoc (ρsh (d + 2)) (.index b i))
        rw [himg, lookup_append]
        cases hfr : Heap.lookup fr
            (renameLoc (ρsh (d + 2)) (.index b i)) with
        | some c => rfl
        | none => rfl
  · -- frame_pres
    intro loc c hc
    rw [lookup_append] at hc
    cases hfr : Heap.lookup fr loc with
    | some c0 =>
        rw [hfr] at hc
        have hc' : some c0 = some c := hc
        injection hc' with hcc
        exact hcc ▸ h.frame_pres loc c0 hfr
    | none =>
        rw [hfr] at hc
        have hc' : Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
            (.base ⟨5 + d⟩, bcell false)] loc = some c := hc
        by_cases h4 : (.base ⟨4 + d⟩ : Loc) = loc
        · subst h4
          have hcell : c = intcell jv := by
            simp [Heap.lookup] at hc'
            exact hc'.symm
          subst hcell
          exact h.lookup_some (l := .base ⟨4⟩) (c := intcell jv) rfl
        · by_cases h5 : (.base ⟨5 + d⟩ : Loc) = loc
          · subst h5
            have hcell : c = bcell false := by
              simp [Heap.lookup, beq_false_of_ne h4] at hc'
              exact hc'.symm
            subst hcell
            exact h.lookup_some (l := .base ⟨5⟩) (c := bcell false) rfl
          · exfalso
            simp [Heap.lookup, beq_false_of_ne h4, beq_false_of_ne h5] at hc'
  · -- fr_avoid
    intro a
    rw [lookup_append]
    by_cases ha : a < 4
    · rw [ρsh_lt ha]
      have h2 := h.fr_avoid a
      rw [ρsh_lt ha] at h2
      rw [h2]
      show Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
          (.base ⟨5 + d⟩, bcell false)] (.base ⟨a⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 4 + d ≠ a by omega)),
        beq_false_of_ne (base_ne (show 5 + d ≠ a by omega))]
    · rw [ρsh_ge (d := d + 2) (a := a) (by omega)]
      have h2 := h.fr_avoid (a + 2)
      rw [ρsh_ge (d := d) (a := a + 2) (by omega)] at h2
      rw [show a + (d + 2) = a + 2 + d from by omega, h2]
      show Heap.lookup [(.base ⟨4 + d⟩, intcell jv),
          (.base ⟨5 + d⟩, bcell false)] (.base ⟨a + 2 + d⟩) = none
      simp [Heap.lookup,
        beq_false_of_ne (base_ne (show 4 + d ≠ a + 2 + d by omega)),
        beq_false_of_ne (base_ne (show 5 + d ≠ a + 2 + d by omega))]

/-! ## Transfer plumbing: the shift fixes every anchor configuration
(all mentioned addresses are the active cells 0–3) -/

theorem renCfg_cmp (d : Nat) (b : Bool) :
    renameConfig (ρsh d) (.retV (.bool b) outerCmpCont)
      = .retV (.bool b) outerCmpCont := by
  with_unfolding_all rfl

theorem renCfg_stop (d : Nat) :
    renameConfig (ρsh d) (.next .stop) = .next .stop := rfl

/-- A canonical segment between shift-fixed configurations transfers to
the true placement: same fuel, same stream, related terminal states. -/
theorem transfer_seg {d : Nat} {fr : Heap} {σC σC' σA : ExecState}
    {c c' : Config} {k : Nat} {ch : Choices}
    (hFS : FrameSim (ρsh d) 4 (4 + d) fr σC σA)
    (hrun : stepFnIter k σC c ch = .ok (c', σC', ch))
    (hc : renameConfig (ρsh d) c = c) (hc' : renameConfig (ρsh d) c' = c') :
    ∃ σA', stepFnIter k σA c ch = .ok (c', σA', ch)
      ∧ FrameSim (ρsh d) 4 (4 + d) fr σC' σA' := by
  have hsim := stepFnIter_sim k hFS c ch
  rw [hc] at hsim
  obtain ⟨rF, hrunF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σF, chF⟩ := rF
  obtain ⟨h1, h2, h3⟩ := htrip
  dsimp only at h1 h2 h3
  rw [h1, hc'] at hrunF
  rw [h3] at hrunF
  exact ⟨σF, hrunF, h2⟩


end GoLean.Examples.InsertionSort
