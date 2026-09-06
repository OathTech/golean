import GoLeanIris.Shared
import GoLeanIris.Readout

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap Iris.BI

def sharedInitialHeap (b : Bool) : Heap :=
  #[.value .bool (.bool b), .value .bool (.bool false)]

/-- The generic admitted driver setup provides the two actual slots, their
values and the external result pin, for every setup fuel and choice stream. -/
theorem shared_setup (b : Bool) (fuel : Nat) (ch : Choices) :
    runProgramSetupM fuel sharedProgram "Shared" #[.bool b] ch =
      .ok (sharedConfig 0 1, sharedState (sharedInitialHeap b), [.base ⟨1⟩], ch) := by
  have run := setup_layout (shared_admitted b) (f := sharedProgram.funcs[4])
    (by rfl) (.boolean rfl .nil) fuel ch
  exact run

/-- Adequacy allocates the concrete Iris model and supplies both initial
cells. No abstract ghost state or assumed final heap escapes the theorem. -/
theorem shared_adequate (b : Bool) :
    adequate .NotStuck (sharedConfig 0 1) (sharedState (sharedInitialHeap b))
      (fun _ final => final.heap[1]? = some (.value .bool (.bool (!b)))) := by
  apply heap_adequacy (GF := GoResources) _ _
    (fun _ => iprop(1 ↦ (.value .bool (.bool (!b)))))
  · intro _ hc
    iintro Hpts
    icases BigSepM.bigSepM_delete (i := 0) (x := .value .bool (.bool b))
      (by rw [get?_heapToMap]; rfl) $$ Hpts with ⟨Harg, Hrest⟩
    iapply wp_shared hc 0 1 b (.bool false)
    isplitl [Harg]
    · iexact Harg
    iapply BigSepM.bigSepM_lookup (i := 1) (x := .value .bool (.bool false)) ?_ $$ Hrest
    rw [get?_delete_ne (by decide), get?_heapToMap]
    rfl
  · intro _ _ final _
    iintro ⟨Hheap, Hroot⟩
    icases genHeap_valid $$ [$Hheap $Hroot] with >%h
    imodintro
    ipureintro
    simpa only [get?_heapToMap] using h

theorem shared_readout_adequate (b : Bool) :
    adequate .NotStuck (sharedConfig 0 1) (sharedState (sharedInitialHeap b))
      (fun _ final => loadMany final [.base ⟨1⟩] = .ok [.bool (!b)]) := {
  adequate_not_stuck := (shared_adequate b).adequate_not_stuck
  adequate_result := by
    intro ts final v hreach
    have hcell := (shared_adequate b).adequate_result ts final v hreach
    simp [loadMany, loadLoc_cell hcell, Bind.bind, Except.bind] }

theorem shared_execution_readout (b : Bool) {fuel final initial residual}
    (run : execStmtLoop fuel (sharedState (sharedInitialHeap b)) (sharedConfig 0 1) initial =
      .ok (final, residual)) : loadMany final [.base ⟨1⟩] = .ok [.bool (!b)] :=
  adequate_execStmtLoop (shared_readout_adequate b) run

end GoLean.IrisCustomer
