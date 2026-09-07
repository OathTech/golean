import Tests.AbortObservation
import GoLean.GoCore.RecoveryObservation
import Lean

open Lean

/-- Post-import audit of the complete supporting closure, including unused
private declarations and declarations after this audit's definition. -/
def AbortObservationAudit.run : CoreM Unit := do
  let env ← getEnv
  let modules : List Name := [
    `GoLean.GoCore.AbortObservation,
    `GoLean.GoCore.RecoveryObservation,
    `GoLean.GoCore.RecoveryPoolObservation,
    `GoLean.GoCore.RecoveryProgramObservation,
    `Tests.AbortObservation,
    `Tests.AbortObservationAudit]
  for m in modules do
    unless env.header.moduleNames.contains m do
      throwError "Abort observation audit: missing module {m}"
  let exports : List Name := [
    ``GoLean.GoCore.RecoveryRuntime.runConfigWithAbort_erasure,
    ``GoLean.GoCore.RecoveryRuntime.stringPanicEntry?_some,
    ``GoLean.GoCore.RecoveryRuntime.stringPanicEntries?_some,
    ``GoLean.GoCore.RecoveryRuntime.stringPanicEntries?_typed,
    ``GoLean.GoCore.RecoveryRuntime.abortRecord?_some,
    ``GoLean.GoCore.RecoveryRuntime.runConfigWithAbort_witness,
    ``GoLean.GoCore.RecoveryRuntime.Control.abort_chain,
    ``GoLean.GoCore.RecoveryRuntime.Inv.trace_choices,
    ``GoLean.GoCore.RecoveryRuntime.Inv.observed_abort,
    ``GoLean.GoCore.RecoveryRuntime.Inv.panic_error_head,
    ``GoLean.GoCore.RecoveryRuntime.Inv.observation_complete,
    ``GoLean.GoCore.RecoveryRuntime.stepAbortRecord?_some,
    ``GoLean.GoCore.RecoveryRuntime.execPoolWithAbort_erasure,
    ``GoLean.GoCore.RecoveryRuntime.PoolAbortWitness.run,
    ``GoLean.GoCore.RecoveryRuntime.PoolAbortWitness.panic_result,
    ``GoLean.GoCore.RecoveryRuntime.PoolAbortWitness.reached,
    ``GoLean.GoCore.RecoveryRuntime.execPoolWithAbort_witness,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_erasure,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbortInts_erasure,
    ``GoLean.GoCore.RecoveryRuntime.checkedRunProgramPoolWithAbort_admitted,
    ``GoLean.GoCore.RecoveryRuntime.checkedRunProgramPoolWithAbort_sound,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_witness,
    ``GoLean.GoCore.RecoveryRuntime.Tests.complete_chain_bytes_and_flags,
    ``GoLean.GoCore.RecoveryRuntime.Tests.nonstring_tail_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.recovered_transient_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.positive_frontier_record,
    ``GoLean.GoCore.RecoveryRuntime.Tests.wrong_event_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.wrong_selected_thread_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.wrong_tombstone_text_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.wrong_renderer_text_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.supplied_tombstone_is_not_provenance,
    ``GoLean.GoCore.RecoveryRuntime.Tests.zero_fuel_has_no_record,
    ``GoLean.GoCore.RecoveryRuntime.Tests.actual_pool_transition_records_whole_chain,
    ``GoLean.GoCore.RecoveryRuntime.Tests.actual_pool_record_has_source_bound_witness,
    ``GoLean.GoCore.RecoveryRuntime.Tests.main_exit_pick_keeps_worker_alive,
    ``GoLean.GoCore.RecoveryRuntime.Tests.main_exit_pick_can_finish_without_record,
    ``GoLean.GoCore.RecoveryRuntime.Tests.generic_erasure_keeps_exact_original_choices,
    ``GoLean.GoCore.RecoveryRuntime.Tests.actual_checker_admits_nullary_subject,
    ``GoLean.GoCore.RecoveryRuntime.Tests.checked_program_records_actual_panic,
    ``GoLean.GoCore.RecoveryRuntime.Tests.checked_program_zero_fuel_is_not_terminal,
    ``GoLean.GoCore.RecoveryRuntime.Tests.broader_integer_entry_still_runs,
    ``GoLean.GoCore.RecoveryRuntime.Tests.broader_entry_does_not_gain_admission,
    ``GoLean.GoCore.RecoveryRuntime.Tests.integer_wrapper_retains_shipped_meaning]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Abort observation audit: missing theorem {n}"
  let ours := env.header.moduleNames.map fun n =>
    n.toString.startsWith "GoLean." || n.toString.startsWith "Tests."
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some i => ours[i.toNat]!
      | none => true
    unless localModule do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Abort observation audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Abort observation audit: {exports.length} required theorems present; {checked} constants checked across all imported local modules (classical trio only)"

