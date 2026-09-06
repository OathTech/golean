import Tests.RecoverySetup
import Lean

open Lean

def RecoverySetupAudit.run : CoreM Unit := do
  let env ← getEnv
  let modules : List Name := [
    `GoLean.GoCore.RecoverySetupShape, `GoLean.GoCore.RecoveryInitialization,
    `GoLean.GoCore.RecoveryResultRoots, `GoLean.GoCore.RecoverySetup,
    `GoLean.GoCore.RecoverySetupWf, `GoLean.GoCore.RecoverySetupReadout,
    `GoLean.GoCore.RecoveryCallEntry, `Tests.RecoverySetup, `Tests.RecoverySetupAudit]
  for m in modules do
    unless env.header.moduleNames.contains m do
      throwError "Recovery setup audit: missing module {m}"
  let exports : List Name := [
    ``GoLean.GoCore.RecoveryRuntime.statement_locSup,
    ``GoLean.GoCore.RecoveryRuntime.programState_wf,
    ``GoLean.GoCore.RecoveryRuntime.program_no_init,
    ``GoLean.GoCore.RecoveryRuntime.declareMany_lookup_member,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.initialContext,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.pushedDecls,
    ``GoLean.GoCore.RecoveryRuntime.ZeroValues.exists,
    ``GoLean.GoCore.RecoveryRuntime.ZeroValues.typed,
    ``GoLean.GoCore.RecoveryRuntime.ZeroValues.unique,
    ``GoLean.GoCore.RecoveryRuntime.bindParams_exact,
    ``GoLean.GoCore.RecoveryRuntime.allocDecls_exact,
    ``GoLean.GoCore.RecoveryRuntime.ResultRoots.load,
    ``GoLean.GoCore.RecoveryRuntime.pinResultLocs_typed,
    ``GoLean.GoCore.RecoveryRuntime.setup_typed,
    ``GoLean.GoCore.RecoveryRuntime.ValueTyped.locSup_le,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.heapLocSup_le,
    ``GoLean.GoCore.RecoveryRuntime.BindingsTyped.locSup_le,
    ``GoLean.GoCore.RecoveryRuntime.typedEntry_wf,
    ``GoLean.GoCore.RecoveryRuntime.setup_typed_wf,
    ``GoLean.GoCore.RecoveryRuntime.initialState_argument,
    ``GoLean.GoCore.RecoveryRuntime.initialState_result,
    ``GoLean.GoCore.RecoveryRuntime.initialState_readout,
    ``GoLean.GoCore.RecoveryRuntime.enterFrame_typed,
    ``GoLean.GoCore.RecoveryRuntime.enterFramePick_typed,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.mixed_actual_setup,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.mixed_input_readout,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.mixed_results_start_false_and_nil,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.pointer_entry_rejected,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.colliding_signature_rejected,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.native_shared_setup,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.a2_recovered_setup,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.a2_uncaught_setup,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.a2_normal_setup,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.empty_setup,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.captured_call_typed,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.captured_call_storage,
    ``GoLean.GoCore.RecoveryRuntime.SetupTests.actual_block_shadow]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Recovery setup audit: missing theorem {n}"
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
        throwError "Recovery setup audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Recovery setup audit: {exports.length} required theorems present; {checked} constants checked across all imported local modules (classical trio only)"
