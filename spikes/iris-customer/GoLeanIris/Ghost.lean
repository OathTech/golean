import GoLeanIris.Heap

/-! The whole immutable context is pinned, including method sets and display
metadata. Only the heap varies. This is an equality invariant, not a claim
that arbitrary GoCore programs or values are well typed. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

def ContextEq (state context : ExecState) : Prop :=
  state = { context with heap := state.heap }

theorem ContextEq.heap {state context : ExecState} (h : ContextEq state context)
    (heap : Heap) : ContextEq { state with heap } context := by
  unfold ContextEq at *
  cases state; cases context
  cases h
  rfl

class GoGS (GF : BundledGFunctors) extends InvGS_gen .hasLC GF where
  heap : genHeapGS Nat HeapCell GF HeapMap
  context : ExecState

attribute [reducible, instance] GoGS.heap

instance {GF : BundledGFunctors} [GoGS GF] : StateInterp ExecState Empty GF where
  stateInterp state _ _ _ := iprop(
    genHeapInterp (GF := GF) (H := HeapMap) (heapToMap state.heap) ∗
      ⌜ContextEq state (GoGS.context GF)⌝)

instance {GF : BundledGFunctors} [GoGS GF] : IrisGS_gen .hasLC Config GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

class GoGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  heap : genHeapPreS Nat HeapCell GF HeapMap

attribute [reducible, instance] GoGpreS.heap

/-- A concrete resource bundle. Rules are not stranded behind an abstract
ghost-state assumption: adequacy allocates these resources from nothing. -/
def GoResources : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (DiscreteO HeapCell)) HeapMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (DiscreteO GName)) HeapMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance : GoGpreS GoResources where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by constructor; exists 3
  heap := by
    constructor
    · constructor; exists 4
    · constructor; exists 5
    · exists 6

end GoLean.IrisCustomer
