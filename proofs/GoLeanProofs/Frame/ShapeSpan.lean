import GoLeanProofs.Frame.ShapeStep
import GoLeanProofs.Frame.Transfer

/-!
# The strengthened span transport and THE MID-WALK CONSUMPTION THEOREM
(C2a's deliverable — the U15 composition wall's repair)

`span_consume`: a landed canonical span (`stepFnIter` equality — the
`*_full_span` facts every handler equation ships) consumed at ANY
`FrameSimS` placement hands back the framed post-state **as a
LITERAL**: `σF' = { σfin with heap := renameHeap ρ pre ++ fr ++
renameHeap ρ post, nextAddr := ρ σfin.nextAddr }` for a split of the
canonical post-heap. An outer literal walk can therefore RESUME from
the consumed sub-span's post-state — the exact operation the U15
verdict measured as blocked under the weak relation (lossy `FrameSim`:
no list-determination). LINEAGE: Yang–O'Hearn locality, completeness
half (`ShapeSim.lean`'s module docstring).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-- `stepFnIter_sim` at the strengthened relation (Transfer.lean:29's
verbatim copy over `stepFn_simS`). -/
theorem stepFnIter_simS {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} :
    ∀ (n : Nat) {σ σF : ExecState} (_ : FrameSimS ρ na₀ na fr σ σF)
      (c : Config) (ch : Choices),
      ExSim (TripSimS ρ na₀ na fr)
        (stepFnIter n σ c ch) (stepFnIter n σF (renameConfig ρ c) ch) := by
  intro n
  induction n with
  | zero =>
      intro σ σF hS c ch
      exact ExSim.ok ⟨rfl, hS, rfl⟩
  | succ m ih =>
      intro σ σF hS c ch
      simp only [stepFnIter]
      refine ExSim.bind (stepFn_simS hS c ch) ?_
      intro r rF hr
      obtain ⟨c', σ', ch'⟩ := r
      obtain ⟨cF', σF', chF'⟩ := rF
      obtain ⟨h1, h2, h3⟩ := hr
      dsimp only at h1 h2 h3
      subst h1 h3
      exact ih h2 c' _

/-- **THE MID-WALK CONSUMPTION THEOREM.** Consume a canonical span at
a `FrameSimS` placement: the framed run completes with the SAME
choices, the strengthened relation carries to the endpoints, and the
framed post-state is DETERMINED LITERALLY — every table equal to the
canonical post-state's, the allocator at `ρ` of the canonical's, and
the heap the three-segment splice of a canonical post-heap split.
The consumer (an outer literal chain) resumes from exactly this
state; nothing relational survives the hand-back. -/
theorem span_consume {n : Nat} {σ0 σfin σF : ExecState}
    {c c' : Machine.Config} {chIn chOut : Choices}
    {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    (hrun : stepFnIter n σ0 c chIn = .ok (c', σfin, chOut))
    (hF : FrameSimS ρ na₀ na fr σ0 σF) :
    ∃ pre post, σfin.heap = pre ++ post
      ∧ stepFnIter n σF (renameConfig ρ c) chIn
          = .ok (renameConfig ρ c',
              { σfin with
                  heap := renameHeap ρ pre ++ fr ++ renameHeap ρ post,
                  nextAddr := ρ σfin.nextAddr }, chOut)
      ∧ FrameSimS ρ na₀ na fr σfin
          { σfin with
              heap := renameHeap ρ pre ++ fr ++ renameHeap ρ post,
              nextAddr := ρ σfin.nextAddr } := by
  have hsim := stepFnIter_simS (na₀ := na₀) (na := na) n hF c chIn
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hc
  subst hch
  obtain ⟨pre, post, hsplit, hheap⟩ := hs.shape
  refine ⟨pre, post, hsplit, ?_, ?_⟩
  · rw [htF]
    congr 1
    congr 1
    -- σFfin = the literal: field-by-field from the relation
    have h1 : σFfin.types = σfin.types := hs.types_eq
    have h2 : σFfin.functions = σfin.functions := hs.funcs_eq
    have h3 : σFfin.methods = σfin.methods := hs.methods_eq
    have h4 : σFfin.methodSets = σfin.methodSets := hs.methodSets_eq
    have h5 : σFfin.nextAddr = ρ σfin.nextAddr := hs.next_eq
    cases σFfin
    cases σfin
    simp_all
  · have hlit : σFfin = { σfin with
        heap := renameHeap ρ pre ++ fr ++ renameHeap ρ post,
        nextAddr := ρ σfin.nextAddr } := by
      have h1 : σFfin.types = σfin.types := hs.types_eq
      have h2 : σFfin.functions = σfin.functions := hs.funcs_eq
      have h3 : σFfin.methods = σfin.methods := hs.methods_eq
      have h4 : σFfin.methodSets = σfin.methodSets := hs.methodSets_eq
      have h5 : σFfin.nextAddr = ρ σfin.nextAddr := hs.next_eq
      cases σFfin
      cases σfin
      simp_all
    rw [← hlit]
    exact hs

/-- The `.stop`-terminal corollary in `span_relocate`'s exact shape
(every handler equation's alloc form can consume this instead when the
literal hand-back is wanted). -/
theorem span_relocateS {n : Nat} {σ0 σfin σF : ExecState}
    {c : Machine.Config} {chIn chOut : Choices}
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    (hrun : stepFnIter n σ0 c chIn
      = .ok (.next .stop, σfin, chOut))
    (hF : FrameSimS r na₀ na fr σ0 σF) :
    ∃ pre post, σfin.heap = pre ++ post
      ∧ stepFnIter n σF (renameConfig r c) chIn
          = .ok (.next .stop,
              { σfin with
                  heap := renameHeap r pre ++ fr ++ renameHeap r post,
                  nextAddr := r σfin.nextAddr }, chOut)
      ∧ FrameSimS r na₀ na fr σfin
          { σfin with
              heap := renameHeap r pre ++ fr ++ renameHeap r post,
              nextAddr := r σfin.nextAddr } := by
  have h := span_consume hrun hF
  simpa only [show renameConfig r (Machine.Config.next .stop)
    = Machine.Config.next .stop from rfl] using h

/-- Lookup through an append, key present left. -/
theorem lookup_append_some {A : Heap} (B : Heap) {l : Loc} {c : HeapCell}
    (h : Heap.lookup A l = some c) :
    Heap.lookup (A ++ B) l = some c := by
  induction A with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      simp only [Heap.lookup, List.cons_append] at h ⊢
      cases hb : (l' == l) with
      | true => rw [hb] at h; exact h
      | false => rw [hb] at h; exact ih h

/-- Lookup through an append, key absent left. -/
theorem lookup_append_none (A : Heap) {B : Heap} {l : Loc}
    (h : Heap.lookup A l = none) :
    Heap.lookup (A ++ B) l = Heap.lookup B l := by
  induction A with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨l', c'⟩ := p
      simp only [Heap.lookup, List.cons_append] at h ⊢
      cases hb : (l' == l) with
      | true => rw [hb] at h; cases h
      | false => rw [hb] at h; exact ih h

/-- Frame EXTENSION at a growth-free placement (the seam-placement
constructor the U15 probe predicted): fresh frame cells whose keys are
off the ρ-image and off the current framed heap extend both the frame
and the framed state, PROVIDED the placement carries no canonical
growth yet (the `hshape0` premise — seeds and relocations qualify;
extensions therefore happen at placement-construction time, before
any walking). -/
theorem frameSimS_extend {ρ : Nat → Nat} {na₀ na : Nat} {fr frX : Heap}
    {σ σF : ExecState}
    (h : FrameSimS ρ na₀ na fr σ σF)
    (hshape0 : σF.heap = renameHeap ρ σ.heap ++ fr)
    (hXavoid : ∀ a : Nat, Heap.lookup frX (.base ⟨ρ a⟩) = none)
    (hXfresh : ∀ l : Loc, (Heap.lookup frX l).isSome →
      Heap.lookup σF.heap l = none) :
    FrameSimS ρ na₀ na (fr ++ frX) σ
      { σF with heap := σF.heap ++ frX } where
  spec := h.spec
  types_eq := h.types_eq
  funcs_eq := h.funcs_eq
  methods_eq := h.methods_eq
  methodSets_eq := h.methodSets_eq
  next_eq := h.next_eq
  alloc_reg := h.alloc_reg
  lookup_img := by
    intro l
    have himg := h.lookup_img l
    show Heap.lookup (σF.heap ++ frX) (renameLoc ρ l) = _
    cases hl : Heap.lookup σ.heap l with
    | some c =>
        rw [hl] at himg
        exact lookup_append_some frX himg
    | none =>
        rw [hl] at himg
        cases hfr : Heap.lookup fr (renameLoc ρ l) with
        | some c0 =>
            rw [hfr] at himg
            rw [lookup_append_some frX himg,
              lookup_append_some frX hfr]
        | none =>
            rw [hfr] at himg
            rw [lookup_append_none _ himg, lookup_append_none _ hfr]
  frame_pres := by
    intro l c hl
    show Heap.lookup (σF.heap ++ frX) l = some c
    cases hfr : Heap.lookup fr l with
    | some c0 =>
        have hc : c0 = c := by
          have := lookup_append_some frX hfr
          rw [this] at hl
          exact Option.some.inj hl
        subst hc
        exact lookup_append_some frX (h.frame_pres l c0 hfr)
    | none =>
        rw [lookup_append_none _ hfr] at hl
        have hnone : Heap.lookup σF.heap l = none :=
          hXfresh l (by rw [hl]; simp)
        rw [lookup_append_none _ hnone]
        exact hl
  fr_avoid := by
    intro a
    show Heap.lookup (fr ++ frX) _ = none
    rw [lookup_append_none _ (h.fr_avoid a)]
    exact hXavoid a
  bodies_inv := h.bodies_inv
  shape := by
    refine ⟨σ.heap, [], by simp, ?_⟩
    show σF.heap ++ frX = renameHeap ρ σ.heap ++ (fr ++ frX) ++ renameHeap ρ []
    rw [hshape0]
    simp [renameHeap]

end GoLean.Frame
