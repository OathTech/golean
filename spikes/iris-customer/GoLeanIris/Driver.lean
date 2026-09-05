import GoLeanIris.Readout
import GateA1.Examples

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic

def initialHeap : Heap := #[.value .bool (.bool false)]

set_option maxRecDepth 4096 in
theorem recovered_setup :
    runProgramSetupM 60 recoveryProgram "Recovered" #[] [] =
      .ok (recoveredConfig 0, programState initialHeap, [.base ⟨0⟩], []) := by
  with_unfolding_all rfl

def successful (r : Except Stop (ExecState × Choices)) : Bool :=
  match r with | .ok _ => true | .error _ => false

theorem successful_iff {r : Except Stop (ExecState × Choices)} :
    successful r = true ↔ ∃ state choices, r = .ok (state, choices) := by
  cases r with
  | error e => simp [successful]
  | ok result => obtain ⟨state, choices⟩ := result; simp [successful]

set_option maxRecDepth 4096 in
theorem recovered_terminates :
    ∃ final residual, execStmtLoop 60 (programState initialHeap) (recoveredConfig 0) [] =
      .ok (final, residual) := by
  apply successful_iff.mp
  decide +kernel

set_option maxRecDepth 4096 in
theorem recovered_no_registry_boundaries :
    seqOpCount 60 (programState initialHeap) (recoveredConfig 0) [] = 0 := by
  decide +kernel

/-- The result is obtained through Iris adequacy and named-result readout.
The separately checked execution witness provides termination; WP itself is
partial correctness and does not prove termination. -/
theorem recovered_program_result :
    ∃ out, runProgramPoolOutM 60 recoveryProgram "Recovered" #[] [] =
      .ok {values := #[.bool true], output := out} := by
  obtain ⟨final, residual, hr⟩ := recovered_terminates
  have ha := recovered_adequate initialHeap 0 (.bool false) rfl
  have hread : adequate .NotStuck (recoveredConfig 0) (programState initialHeap)
      (fun _ final => loadMany final [.base ⟨0⟩] = .ok [.bool true]) := {
    adequate_not_stuck := ha.adequate_not_stuck
    adequate_result := by
      intro ts final v hreach
      have hcell := ha.adequate_result ts final v hreach
      simp [loadMany, loadLoc_cell hcell, Bind.bind, Except.bind] }
  exact adequate_program_result recovered_setup hread hr recovered_no_registry_boundaries

/-- This projection checks only emitted bytes; it does not recompute the
named-result claim established through Iris above. -/
def returnedBytes : RunResult → Option (Array UInt8)
  | .ok readout => some readout.output.bytes
  | .error _ => none

set_option maxRecDepth 4096 in
theorem recovered_silent :
    returnedBytes (runProgramPoolOutM 60 recoveryProgram "Recovered" #[] []) = some #[] := by
  decide +kernel

theorem recovered_program :
    runProgramPoolOutM 60 recoveryProgram "Recovered" #[] [] =
      .ok {values := #[.bool true], output := .empty} := by
  obtain ⟨out, hr⟩ := recovered_program_result
  have hs := recovered_silent
  rw [hr] at hs
  obtain ⟨bytes⟩ := out
  have hb : bytes = #[] := Option.some.inj hs
  subst bytes
  exact hr

set_option maxRecDepth 4096 in
theorem normal_setup :
    runProgramSetupM 60 recoveryProgram "Normal" #[] [] =
      .ok (normalConfig 0, programState initialHeap, [.base ⟨0⟩], []) := by
  with_unfolding_all rfl

set_option maxRecDepth 4096 in
theorem normal_terminates :
    ∃ final residual, execStmtLoop 60 (programState initialHeap) (normalConfig 0) [] =
      .ok (final, residual) := by
  apply successful_iff.mp
  decide +kernel

set_option maxRecDepth 4096 in
theorem normal_no_registry_boundaries :
    seqOpCount 60 (programState initialHeap) (normalConfig 0) [] = 0 := by
  decide +kernel

theorem normal_program_result :
    ∃ out, runProgramPoolOutM 60 recoveryProgram "Normal" #[] [] =
      .ok {values := #[.bool true], output := out} := by
  obtain ⟨final, residual, hr⟩ := normal_terminates
  have ha := normal_adequate initialHeap 0 (.bool false) rfl
  have hread : adequate .NotStuck (normalConfig 0) (programState initialHeap)
      (fun _ final => loadMany final [.base ⟨0⟩] = .ok [.bool true]) := {
    adequate_not_stuck := ha.adequate_not_stuck
    adequate_result := by
      intro ts final v hreach
      have hcell := ha.adequate_result ts final v hreach
      simp [loadMany, loadLoc_cell hcell, Bind.bind, Except.bind] }
  exact adequate_program_result normal_setup hread hr normal_no_registry_boundaries

set_option maxRecDepth 4096 in
/-- The negative control is an explicit panic observation, not a NotStuck WP
claim. Its successful-return counterpart would be false. -/
theorem uncaught_program :
    runProgramPoolOutM 60 recoveryProgram "Uncaught" #[] [] =
      .error (.panic "customer panic", .empty) := by
  apply GateA1.panicObservation_sound
  decide +kernel

end GoLean.IrisCustomer
