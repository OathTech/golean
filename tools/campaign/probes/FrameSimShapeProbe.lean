import GoLeanProofs.Frame.Relocate
import GoLeanProofs.Frame.Threshold

/-! # C2a slice-1 PROBE: the C2 INSERTION-POINT SHAPE clause —
primitive-preservation trial (probe-only; the commissioned instrument's
keystone measurements, per the U16 probe's map and D1's probe-first
order).

Trials, on a LOCAL structure copy `FrameSim2` (= FrameSim + `shape`):
  (1) the heap algebra (set-over-append, set-of-missing, renameHeap-set
      commutation) — the clause's proof toolkit;
  (2) `setBase2` — the ONE mutation primitive, all three key cases
      (in-pre, in-post, missing/append);
  (3) `frameSim2_seed` / `frameSim2_relocate` — the seeds.
If these check, the in-place edit's blast radius is: Sim.lean
(structure + setBase + alloc_snd), Threshold (seed + rebaseSimT with
new list-level premises), Relocate (relocate), 5 gallery rebase call
sites, and everything else re-elaborates. -/

namespace GoLean.Frame.ShapeTrial

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame

/-! ## (1) The heap algebra -/

def keyMem (h : Heap) (k : Loc) : Prop := (Heap.lookup h k).isSome

theorem lookup_none_iff {h : Heap} {k : Loc} :
    Heap.lookup h k = none ↔ ¬ keyMem h k := by
  unfold keyMem
  cases hl : Heap.lookup h k <;> simp [hl]

/-- `Heap.set` on an append, key found in the left part. -/
theorem set_append_left {A : Heap} (B : Heap) {k : Loc} (c : HeapCell)
    (hk : keyMem A k) :
    Heap.set (A ++ B) k c = Heap.set A k c ++ B := by
  induction A with
  | nil => unfold keyMem at hk; simp [Heap.lookup] at hk
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      by_cases hlk : l' = k
      · subst hlk
        simp [Heap.set, List.cons_append]
      · unfold keyMem at hk
        simp only [Heap.lookup] at hk
        rw [show (l' == k) = false from by simp [hlk]] at hk
        simp only [List.cons_append, Heap.set,
          show (l' == k) = false from by simp [hlk]]
        rw [ih hk]
        simp

/-- `Heap.set` on an append, key absent from the left part. -/
theorem set_append_right (A : Heap) {B : Heap} {k : Loc} (c : HeapCell)
    (hk : ¬ keyMem A k) :
    Heap.set (A ++ B) k c = A ++ Heap.set B k c := by
  induction A with
  | nil => simp
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      by_cases hlk : l' = k
      · subst hlk
        exact absurd (by unfold keyMem; simp [Heap.lookup]) hk
      · have hk' : ¬ keyMem rest k := by
          intro hmem
          exact hk (by
            unfold keyMem at hmem ⊢
            simp only [Heap.lookup, show (l' == k) = false from by simp [hlk]]
            exact hmem)
        simp only [List.cons_append, Heap.set,
          show (l' == k) = false from by simp [hlk]]
        rw [ih hk']
        simp

/-- `Heap.set` of a missing key appends. -/
theorem set_of_missing {h : Heap} {k : Loc} (c : HeapCell)
    (hk : ¬ keyMem h k) :
    Heap.set h k c = h ++ [(k, c)] := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      by_cases hlk : l' = k
      · subst hlk
        exact absurd (by unfold keyMem; simp [Heap.lookup]) hk
      · have hk' : ¬ keyMem rest k := by
          intro hmem
          exact hk (by
            unfold keyMem at hmem ⊢
            simp only [Heap.lookup, show (l' == k) = false from by simp [hlk]]
            exact hmem)
        simp only [Heap.set, show (l' == k) = false from by simp [hlk]]
        rw [ih hk']
        simp

/-- `renameHeap` commutes with `Heap.set` (injective ρ). -/
theorem renameHeap_set {ρ : Nat → Nat}
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (h : Heap) (k : Loc)
    (c : HeapCell) :
    renameHeap ρ (Heap.set h k c)
      = Heap.set (renameHeap ρ h) (renameLoc ρ k) (renameCell ρ c) := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      simp only [Heap.set, renameHeap, List.map_cons]
      rw [renameLoc_beq hinj l' k]
      cases hb : (l' == k) with
      | true =>
          simp only [if_pos rfl]
          rfl
      | false =>
          simp only [renameHeap] at ih
          simp [ih]

/-- Key membership transfers through `renameHeap` (both directions). -/
theorem keyMem_renameHeap {ρ : Nat → Nat}
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (h : Heap) (k : Loc) :
    keyMem (renameHeap ρ h) (renameLoc ρ k) ↔ keyMem h k := by
  unfold keyMem
  rw [renameHeap_lookup hinj]
  cases Heap.lookup h k <;> simp

/-! ## (2) The strengthened relation + setBase -/

/-- FrameSim + the C2 insertion-point shape clause. -/
structure FrameSim2 (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap)
    (σ σF : ExecState) : Prop extends FrameSim ρ na₀ na fr σ σF where
  shape : ∃ pre post, σ.heap = pre ++ post
    ∧ σF.heap = renameHeap ρ pre ++ fr ++ renameHeap ρ post

theorem setBase2 (h : FrameSim2 ρ na₀ na fr σ σF) (a : Nat) (c : HeapCell) :
    FrameSim2 ρ na₀ na fr
      { σ with heap := Heap.set σ.heap (.base ⟨a⟩) c }
      { σF with heap := Heap.set σF.heap (.base ⟨ρ a⟩) (renameCell ρ c) } where
  toFrameSim := h.toFrameSim.setBase a c
  shape := by
    obtain ⟨pre, post, hsplit, hF⟩ := h.shape
    have hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y := h.spec.inj
    have hrk : renameLoc ρ (.base ⟨a⟩) = (.base ⟨ρ a⟩ : Loc) := rfl
    by_cases hpre : keyMem pre (.base ⟨a⟩)
    · -- in the pre segment
      refine ⟨Heap.set pre (.base ⟨a⟩) c, post, ?_, ?_⟩
      · rw [hsplit, set_append_left post c hpre]
      · rw [hF]
        have hpreF : keyMem (renameHeap ρ pre) (.base ⟨ρ a⟩) := by
          rw [← hrk, keyMem_renameHeap hinj]; exact hpre
        rw [show renameHeap ρ pre ++ fr ++ renameHeap ρ post
            = renameHeap ρ pre ++ (fr ++ renameHeap ρ post) from by simp,
          set_append_left _ _ hpreF, renameHeap_set hinj, hrk]
        simp
    · by_cases hpost : keyMem post (.base ⟨a⟩)
      · -- in the post segment
        refine ⟨pre, Heap.set post (.base ⟨a⟩) c, ?_, ?_⟩
        · rw [hsplit, set_append_right pre c hpre]
        · rw [hF]
          have hpreF : ¬ keyMem (renameHeap ρ pre) (.base ⟨ρ a⟩) := by
            rw [← hrk, keyMem_renameHeap hinj]; exact hpre
          have hfrF : ¬ keyMem fr (.base ⟨ρ a⟩) := by
            unfold keyMem
            rw [h.fr_avoid a]
            simp
          rw [show renameHeap ρ pre ++ fr ++ renameHeap ρ post
              = renameHeap ρ pre ++ (fr ++ renameHeap ρ post) from by simp,
            set_append_right _ _ hpreF, set_append_right _ _ hfrF,
            renameHeap_set hinj, hrk]
          simp
      · -- missing: both sides append at the very end
        refine ⟨pre, Heap.set post (.base ⟨a⟩) c, ?_, ?_⟩
        · rw [hsplit, set_append_right pre c hpre]
        · rw [hF]
          have hpostF : ¬ keyMem (renameHeap ρ post) (.base ⟨ρ a⟩) := by
            rw [← hrk, keyMem_renameHeap hinj]; exact hpost
          have hpreF : ¬ keyMem (renameHeap ρ pre) (.base ⟨ρ a⟩) := by
            rw [← hrk, keyMem_renameHeap hinj]; exact hpre
          have hfrF : ¬ keyMem fr (.base ⟨ρ a⟩) := by
            unfold keyMem
            rw [h.fr_avoid a]
            simp
          rw [show renameHeap ρ pre ++ fr ++ renameHeap ρ post
              = renameHeap ρ pre ++ (fr ++ renameHeap ρ post) from by simp,
            set_append_right _ _ hpreF, set_append_right _ _ hfrF,
            set_of_missing _ hpostF, set_of_missing _ hpost]
          simp [renameHeap, hrk]

/-! ## (3) The seeds -/

theorem renameHeap_ρT_zero (T : Nat) (h : Heap) :
    renameHeap (ρT T 0) h = h := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨l, c⟩ := p
      simp only [renameHeap, List.map_cons] at ih ⊢
      rw [show renameLoc (ρT T 0) l = l from renameLoc_ρT_zero T l,
        show renameCell (ρT T 0) c = c from renameCell_ρT_zero T c]
      simp only [List.cons.injEq, true_and]
      exact ih

theorem frameSim2_seed {T : Nat} {σ : ExecState}
    (hnext : σ.nextAddr = T)
    (hbodies : ∀ f ∈ σ.functions.toList,
      renameStmt (ρT T 0) f.body = f.body) :
    FrameSim2 (ρT T 0) T T [] σ σ where
  toFrameSim := frameSim_seed hnext hbodies
  shape := ⟨σ.heap, [], by simp, by
    rw [renameHeap_ρT_zero]
    simp [renameHeap]⟩

theorem frameSim2_relocate {ρ : Nat → Nat} {na₀ na : Nat}
    (hs : ShiftSpec ρ na₀ na) {σ : ExecState}
    (halloc : na₀ ≤ σ.nextAddr)
    (hbodies : ∀ f ∈ σ.functions.toList, renameStmt ρ f.body = f.body) :
    FrameSim2 ρ na₀ na [] σ (renameState ρ σ) where
  toFrameSim := frameSim_relocate hs halloc hbodies
  shape := ⟨σ.heap, [], by simp, by simp [renameState, renameHeap]⟩

end GoLean.Frame.ShapeTrial
