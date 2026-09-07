import GoLeanIris.Lifting

/-! Fresh parameter and result slots are distinct resources from any root
referenced by their values. Allocating a pointer slot never allocates or
duplicates ownership of its pointee. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

section
variable {GF : BundledGFunctors} [GoGS GF]

def ownsCells (base : Nat) : List HeapCell → IProp GF
  | [] => iprop(emp)
  | cell :: cells => iprop(base ↦ cell ∗ ownsCells (base + 1) cells)

theorem heap_alloc_cells (heap : Heap) (cells : List HeapCell) :
    genHeapInterp (GF := GF) (H := HeapMap) (heapToMap heap) ⊢ |==>
      (genHeapInterp (heapToMap (heap ++ cells.toArray)) ∗ ownsCells heap.size cells) := by
  induction cells generalizing heap with
  | nil =>
    simp only [List.toArray, Array.append_empty, ownsCells]
    iintro Hheap
    imodintro
    iframe
  | cons cell cells ih =>
    iintro Hheap
    imod (genHeap_alloc (v := cell) (heapToMap_fresh heap)) $$ Hheap
      with ⟨Hheap, Hcell, _⟩
    ihave Hheap : genHeapInterp (GF := GF) (H := HeapMap) (heapToMap (heap.push cell)) $$ [Hheap]
    · iapply (genHeapInterp_eqv (fun k => (heapToMap_push heap cell k).symm)) $$ Hheap
    imod ih (heap.push cell) $$ Hheap with ⟨Hheap, Hcells⟩
    imodintro
    have he : heap ++ (cell :: cells).toArray = heap.push cell ++ cells.toArray := by
      apply Array.toList_inj.mp
      simp
    rw [he]
    simp only [ownsCells, Array.size_push]
    iframe

variable {E : CoPset} {Φ : Unit → IProp GF}

/-- A single actual transition may allocate a whole argument/result vector.
The continuation receives each fresh slot once, in semantic allocation order. -/
theorem wp_alloc_cells_step {cells : List HeapCell} {c : Config} (next : Nat → Config)
    (hnv : ToVal.toVal c = (none : Option Unit))
    (hred : ∀ state, ContextEq state (GoGS.context GF) → ∀ choices,
      stepFn state c choices = .ok
        (next state.heap.size, {state with heap := state.heap ++ cells.toArray}, choices)) :
    (▷ ∀ a : Nat, ownsCells a cells -∗ WP (next a) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step hnv
  iintro %state %ns %obs %obs' %nt Hstate
  simp only [stateInterp]
  icases Hstate with ⟨Hheap, %Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], next state.heap.size, _, [],
      GateA1.Customer.Prim.step (stepFn_sound (hred state Hctx []))⟩
  inext
  iintro %next' %final %forks %hs _
  cases hs with
  | step st =>
    obtain ⟨rfl, rfl⟩ := step_unique (hred state Hctx) st
    imod heap_alloc_cells state.heap cells $$ Hheap with ⟨Hheap, Hcells⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · isplitl [Hheap]
      · iexact Hheap
      · ipureintro; exact Hctx.heap _
    · isplitl [Hcells Hcont]
      · iapply Hcont $$ %state.heap.size Hcells
      · itrivial

end
end GoLean.IrisCustomer
