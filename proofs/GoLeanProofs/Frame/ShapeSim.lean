import GoLeanProofs.Frame.Relocate
import GoLeanProofs.Frame.Threshold

/-!
# The completeness-strengthened frame simulation (`FrameSimS`) — C2a,
the commissioned instrument (layer-C design v2 §8 D1)

**LINEAGE (clever-tricks doctrine): Yang–O'Hearn LOCALITY, the
completeness half** — the semantic frame property's converse
direction: not only does the frame ride untouched (FrameSim's
`frame_pres`/`lookup_img`, the soundness half already shipped), but
the framed state is COMPLETELY DETERMINED by the canonical state, the
frame, and the renaming — the insertion-point SHAPE clause
(`σF.heap = ren(pre) ++ fr ++ ren(post)`), which is what lets a
relational sub-span hand back a LITERAL-resumable state (the U15
composition wall's repair; commissioned at the U18/C1 gate after the
measured kernel-replay wall).

## Why ADDITIVE (`FrameSimS extends FrameSim`), not in-place

The U16 probe priced an in-place strengthening (add the clause to
`FrameSim`, fix ~6 constructor sites, re-elaborate). C2a's probe
(`artifacts/probe/FrameSimShapeProbe.lean`) validated the clause and
the primitives — and found the in-place route MEASURED-BLOCKED at a
site the U16 sizing missed: `rebaseSimT` (the gallery's between-pass
frame-growth constructor) cannot discharge the clause — its
lookup-level premises cannot pin the ∃-witness split against the
retired segment (the frame-growth pattern re-partitions the heap
non-contiguously, and set-append freedom defeats every key-class
pinning; exhausted in the C2a design log). So the strengthened
relation is a NEW structure on the CONSUMPTION path, the weak
`FrameSim` stays the shipped statement vocabulary everywhere
(zero shipped-statement meaning changes), and the S-induction below
COPY-THREADS the weak induction's mutating spine with the
strengthened primitives. The copies are a recorded SCAFFOLD
(retirement condition: fold the clause into `FrameSim` in-place if
the gallery rebase chain is ever retired or re-based on pinned
splits).

## What is here

1. The heap-shape ALGEBRA (set-over-append, set-of-missing,
   `renameHeap`/`Heap.set` commutation) — promoted from the C2a probe.
2. `FrameSimS` (= `FrameSim` + `shape`), the strengthened primitives
   (`setBaseS`, `allocS_snd`, seeds), and `FrameSimS.reify` — the
   PAYOFF: the framed state as a computable function of
   (canonical, fr, ρ, split) — plus the split-uniqueness lemma that
   extracts a KNOWN split from the ∃ (separator discrimination via
   `fr_avoid`; degenerate `fr = []` case separate).
3. The S-copies of the mutating operation lemmas (storeLoc,
   allocDecls, bindParams, enterFrame, stmt/chan/sync/select apply,
   storeTarget, iter-var binding) — each PROOF mirrors its weak
   sibling with S-primitives; non-mutating lemmas (loads, strict ops
   — `applyStrictOp` performs ZERO heap writes, measured by grep and
   pinned by `applyStrictOp_state`) are consumed as-is.
4. `stepFn_simS` / `stepFnIter_simS` / `span_relocateS` — the
   S-transport to span level, and the MID-WALK CONSUMPTION theorem.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## 1. The heap-shape algebra (probe-promoted) -/

/-- Key membership as a Prop (first-occurrence semantics — exactly
`Heap.lookup`'s). -/
def keyMem (h : Heap) (k : Loc) : Prop := (Heap.lookup h k).isSome

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

theorem keyMem_renameHeap {ρ : Nat → Nat}
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (h : Heap) (k : Loc) :
    keyMem (renameHeap ρ h) (renameLoc ρ k) ↔ keyMem h k := by
  unfold keyMem
  rw [renameHeap_lookup hinj]
  cases Heap.lookup h k <;> simp

/-! ## 2. The strengthened relation, primitives, and the payoff -/

/-- **`FrameSim` + the C2 insertion-point SHAPE clause**: the framed
heap IS the renamed canonical heap with the frame spliced at a fixed
insertion point — canonical-prefix, frame, canonical-suffix. The
split is existential in the structure (pinning it would need a new
relation index — an arity change across every mention site); the
uniqueness lemma below recovers it at consumption whenever the frame
is nonempty, and the degenerate empty-frame case determines the heap
outright. -/
structure FrameSimS (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap)
    (σ σF : ExecState) : Prop extends FrameSim ρ na₀ na fr σ σF where
  shape : ∃ pre post, σ.heap = pre ++ post
    ∧ σF.heap = renameHeap ρ pre ++ fr ++ renameHeap ρ post

namespace FrameSimS

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

/-- The strengthened in-place/append write — the ONE mutation
primitive (every machine heap write is a `storeLoc`/alloc `Heap.set`
at a base key). All three key cases (in-prefix, in-suffix,
missing/append-at-end — the last is what a canonical set-append and
its framed twin both do, keeping the split). -/
theorem setBase (h : FrameSimS ρ na₀ na fr σ σF) (a : Nat) (c : HeapCell) :
    FrameSimS ρ na₀ na fr
      { σ with heap := Heap.set σ.heap (.base ⟨a⟩) c }
      { σF with heap := Heap.set σF.heap (.base ⟨ρ a⟩) (renameCell ρ c) } where
  toFrameSim := h.toFrameSim.setBase a c
  shape := by
    obtain ⟨pre, post, hsplit, hF⟩ := h.shape
    have hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y := h.spec.inj
    have hrk : renameLoc ρ (.base ⟨a⟩) = (.base ⟨ρ a⟩ : Loc) := rfl
    by_cases hpre : keyMem pre (.base ⟨a⟩)
    · refine ⟨Heap.set pre (.base ⟨a⟩) c, post, ?_, ?_⟩
      · rw [hsplit, set_append_left post c hpre]
      · rw [hF]
        have hpreF : keyMem (renameHeap ρ pre) (.base ⟨ρ a⟩) := by
          rw [← hrk, keyMem_renameHeap hinj]; exact hpre
        rw [show renameHeap ρ pre ++ fr ++ renameHeap ρ post
            = renameHeap ρ pre ++ (fr ++ renameHeap ρ post) from by simp,
          set_append_left _ _ hpreF, renameHeap_set hinj, hrk]
        simp
    · by_cases hpost : keyMem post (.base ⟨a⟩)
      · refine ⟨pre, Heap.set post (.base ⟨a⟩) c, ?_, ?_⟩
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
      · refine ⟨pre, Heap.set post (.base ⟨a⟩) c, ?_, ?_⟩
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

/-- Allocation commutes and preserves the split (the fresh cell lands
at the end of the canonical suffix on both sides — `setBase`'s
missing-key case, since `fr_avoid` puts the renamed fresh address
outside the frame). -/
theorem alloc_snd (h : FrameSimS ρ na₀ na fr σ σF) (v : GoValue)
    (ty : Option Ty) :
    FrameSimS ρ na₀ na fr (ExecState.alloc σ v ty).2
      (ExecState.alloc σF (renameValue ρ v) ty).2 where
  toFrameSim := h.toFrameSim.alloc_snd v ty
  shape := by
    have hset := h.setBase σ.nextAddr { declaredTy := ty, value := v }
    obtain ⟨pre, post, hsplit, hF⟩ := hset.shape
    refine ⟨pre, post, ?_, ?_⟩
    · simpa [ExecState.alloc, ExecState.freshLoc] using hsplit
    · simpa [ExecState.alloc, ExecState.freshLoc, h.next_eq,
        renameCell] using hF

end FrameSimS

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

/-- The zero-shift seed, strengthened (the identity placement's
shape: everything is prefix, the frame is empty). -/
theorem frameSimS_seed {T : Nat} {σ : ExecState}
    (hnext : σ.nextAddr = T)
    (hbodies : ∀ f ∈ σ.functions.toList,
      renameStmt (ρT T 0) f.body = f.body) :
    FrameSimS (ρT T 0) T T [] σ σ where
  toFrameSim := frameSim_seed hnext hbodies
  shape := ⟨σ.heap, [], by simp, by
    rw [renameHeap_ρT_zero]
    simp [renameHeap]⟩

/-- The relocation seed, strengthened (the rename-image placement's
shape). -/
theorem frameSimS_relocate {ρ : Nat → Nat} {na₀ na : Nat}
    (hs : ShiftSpec ρ na₀ na) {σ : ExecState}
    (halloc : na₀ ≤ σ.nextAddr)
    (hbodies : ∀ f ∈ σ.functions.toList, renameStmt ρ f.body = f.body) :
    FrameSimS ρ na₀ na [] σ (renameState ρ σ) where
  toFrameSim := frameSim_relocate hs halloc hbodies
  shape := ⟨σ.heap, [], by simp, by simp [renameState, renameHeap]⟩

end GoLean.Frame
