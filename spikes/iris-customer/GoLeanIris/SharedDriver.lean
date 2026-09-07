import GoLeanIris.SharedReadout
import GoLeanIris.Driver

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- A separate bounded termination witness for the empty initial stream.
The Boolean result is established by `wp_shared` and adequacy, not this
success projection. The sequential witness avoids whole-pool reduction. -/
theorem shared_terminates (b : Bool) :
    ∃ final residual,
      execStmtLoop 200 (sharedState (sharedInitialHeap b)) (sharedConfig 0 1) [] =
        .ok (final, residual) := by
  apply successful_iff.mp
  cases b <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem shared_no_registry_boundaries (b : Bool) :
    seqOpCount 200 (sharedState (sharedInitialHeap b)) (sharedConfig 0 1) [] = 0 := by
  cases b <;> decide +kernel

/-- Actual shipped driver result, through the same shared typed adequacy
bridge used by A2. The result comes from Iris; empty output comes from the
generic semantic pool correspondence, with no whole-pool reduction. -/
theorem shared_program_all_choices (b : Bool) (ch : Choices) :
    runProgramPoolOutM 200 sharedProgram "Shared" #[.bool b] ch =
      .ok {values := #[.bool (!b)], output := GoString.empty} := by
  obtain ⟨final, residual, run⟩ := shared_terminates b
  exact adequate_typed_program_all_choices (shared_admitted b) (shared_setup b 200)
    (shared_readout_adequate b) run ch

theorem shared_program (b : Bool) :
    runProgramPoolOutM 200 sharedProgram "Shared" #[.bool b] [] =
      .ok {values := #[.bool (!b)], output := GoString.empty} :=
  shared_program_all_choices b []

theorem shared_program_result (b : Bool) :
    ∃ out, runProgramPoolOutM 200 sharedProgram "Shared" #[.bool b] [] =
      .ok {values := #[.bool (!b)], output := out} :=
  ⟨GoString.empty, shared_program b⟩

end GoLean.IrisCustomer
