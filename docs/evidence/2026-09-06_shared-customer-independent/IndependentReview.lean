import GoLeanIris

namespace SharedIndependent
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.IrisCustomer
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap Iris.BI

/-- A new customer use: retain an arbitrary unrelated third cell while
both handlers share the one owned result cell. -/
theorem framed_shared (b : Bool) (sentinel : HeapCell) :
    adequate .NotStuck (sharedConfig 0 1)
      (sharedState #[.value .bool (.bool b), .value .bool (.bool false), sentinel])
      (fun _ final => final.heap[1]? = some (.value .bool (.bool (!b))) ∧
        final.heap[2]? = some sentinel) := by
  apply heap_adequacy (GF := GoResources) _ _
    (fun _ => iprop(1 ↦ (.value .bool (.bool (!b))) ∗ 2 ↦ sentinel))
  · intro _ hc
    iintro Hpts
    icases BigSepM.bigSepM_delete (i := 0) (x := .value .bool (.bool b))
      (by rw [get?_heapToMap]; rfl) $$ Hpts with ⟨Harg, Hrest⟩
    icases BigSepM.bigSepM_delete (i := 1) (x := .value .bool (.bool false))
      (by rw [get?_delete_ne (by decide), get?_heapToMap]; rfl) $$ Hrest
      with ⟨Hroot, Hsentinel⟩
    iapply wp_frame (iprop(2 ↦ sentinel))
    isplitl [Harg Hroot]
    · iapply wp_shared hc 0 1 b (.bool false)
      iframe
    · iapply BigSepM.bigSepM_lookup (i := 2) (x := sentinel) ?_ $$ Hsentinel
      rw [get?_delete_ne (by decide), get?_delete_ne (by decide), get?_heapToMap]
      rfl
  · intro _ _ final _
    iintro ⟨Hheap, Hroot, Hsentinel⟩
    ihave %hr : ⌜get? (heapToMap final.heap) 1 = some (.value .bool (.bool (!b)))⌝
      $$ [Hheap Hroot]
    · icases genHeap_valid $$ [$Hheap $Hroot] with >%h
      itrivial
    icases genHeap_valid $$ [$Hheap $Hsentinel] with >%hs
    imodintro
    ipureintro
    simpa only [get?_heapToMap] using And.intro hr hs

def payload : GoValue := .interface .string (.string ⟨#[255, 0, 10, 65]⟩)
def active : Cont := .panicResumeK [⟨payload, false⟩] .stop
def marked : Cont := .panicResumeK [⟨payload, true⟩] .stop

theorem direct_handler_keeps_original_bytes : FrameRecovery active payload marked := by
  left
  with_unfolding_all rfl

theorem ordinary_call_blocks_recovery :
    recoverThroughWrappers (.frame [] [] [] [] active false) = none := by
  with_unfolding_all rfl

theorem indirect_handler_gets_nil :
    FrameRecovery (.frame [] [] [] [] active false) .nil
      (.frame [] [] [] [] active false) :=
  Or.inr ⟨ordinary_call_blocks_recovery, rfl, rfl⟩

theorem aliasing_precondition_is_exclusive {GF : BundledGFunctors} [GoGS GF]
    (root : Nat) (b : Bool) :
    (root ↦ (.value .bool (.bool b)) ∗ root ↦ (.value .bool (.bool false))) ⊢
      (False : IProp GF) := full_root_exclusive _ _ _

theorem all_choices_retain_empty_output (b : Bool) (choices : Choices) :
    runProgramPoolOutM 200 sharedProgram "Shared" #[.bool b] choices =
      .ok {values := #[.bool (!b)], output := GoString.empty} :=
  shared_program_all_choices b choices

end SharedIndependent

#eval GoLeanIrisAudit.run
