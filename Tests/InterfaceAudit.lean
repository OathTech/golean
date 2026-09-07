import Tests.InterfaceContract
import Tests.BooleanRuntime
import Tests.BooleanProgram
import Tests.RecoveryTypingAudit
import Tests.RecoveryStorageAudit
import Tests.RecoverySetupAudit
import Tests.RecoveryControlAudit
import Tests.AbortObservationAudit
import GoLean.GoCore.PanicText
import Lean

/-! The command runs from a separate harness after complete imports. Origin
selection also checks unused private, generated and trailing declarations. -/
open Lean

def InterfaceAudit.run : CoreM Unit := do
  let env ← getEnv
  for m in env.header.moduleNames do
    if [`Iris, `GateA1, `GoLeanIris].contains m.getRoot ||
        [`GoLean.NativeToIR, `GoLean.CLI].contains m then
      throwError "Semantic interface: forbidden customer dependency {m}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let modules : List Name := [
    `GoLean.GoCore.Machine, `GoLean.GoCore.PanicText,
    `GoLean.GoCore.AbortObservation, `GoLean.GoCore.RecoveryPoolObservation,
    `GoLean.GoCore.RecoveryObservation, `Tests.AbortObservation, `Tests.AbortObservationAudit,
    `GoLean.GoCore.RecoveryProgramObservation,
    `GoLean.GoCore.Trace, `GoLean.GoCore.PoolTrace,
    `GoLean.GoCore.ProgramTrace, `GoLean.Interface,
    `GoLean.GoCore.AdmissionIndices, `GoLean.GoCore.AdmissionPolicy,
    `GoLean.GoCore.Admission,
    `GoLean.GoCore.BooleanTyping, `GoLean.GoCore.BooleanStore,
    `GoLean.GoCore.BooleanSetup,
    `GoLean.GoCore.BooleanInitialization,
    `GoLean.GoCore.BooleanControlTyping, `GoLean.GoCore.BooleanControl,
    `GoLean.GoCore.BooleanInvariant, `GoLean.GoCore.BooleanPreservation,
    `GoLean.GoCore.BooleanProgress, `GoLean.GoCore.BooleanSafety,
    `GoLean.GoCore.BooleanProgram, `GoLean.GoCore.BooleanPool,
    `GoLean.GoCore.RecoveryTypingCore, `GoLean.GoCore.RecoveryExpressions,
    `GoLean.GoCore.RecoveryCalls, `GoLean.GoCore.RecoveryStatements,
    `GoLean.GoCore.RecoveryGraph, `GoLean.GoCore.RecoveryDiagnostics,
    `GoLean.GoCore.RecoveryAdmission,
    `Tests.RecoveryTyping, `Tests.RecoveryDiagnosticControls,
    `Tests.RecoveryTypingFixture, `Tests.RecoveryA2Artifact, `Tests.RecoveryTypingAudit,
    `GoLean.GoCore.RecoveryStore, `GoLean.GoCore.RecoveryEnvironment,
    `GoLean.GoCore.RecoveryAllocation, `GoLean.GoCore.RecoveryOperators,
    `GoLean.GoCore.RecoveryContext, `GoLean.GoCore.RecoveryControlTyping,
    `GoLean.GoCore.RecoverySetupShape, `GoLean.GoCore.RecoveryInitialization,
    `GoLean.GoCore.RecoveryResultRoots, `GoLean.GoCore.RecoverySetup,
    `GoLean.GoCore.RecoverySetupWf, `GoLean.GoCore.RecoverySetupReadout,
    `GoLean.GoCore.RecoveryCallEntry,
    `Tests.RecoveryStorage, `Tests.RecoveryStorageAudit,
    `Tests.RecoverySetup, `Tests.RecoverySetupAudit,
    `GoLean.GoCore.RecoveryDelivery, `GoLean.GoCore.RecoveryControlData,
    `GoLean.GoCore.RecoveryControl, `GoLean.GoCore.RecoveryControlMono,
    `GoLean.GoCore.RecoveryWalk, `GoLean.GoCore.RecoveryExpressionProgress,
    `GoLean.GoCore.RecoveryControlHelpers, `GoLean.GoCore.RecoveryCallControl,
    `GoLean.GoCore.RecoveryValueBasic, `GoLean.GoCore.RecoveryValueCalls,
    `GoLean.GoCore.RecoveryStatementProgress, `GoLean.GoCore.RecoveryFrameProgress,
    `GoLean.GoCore.RecoveryPanicProgress, `GoLean.GoCore.RecoveryInvariant,
    `GoLean.GoCore.RecoverySuccessfulRuns,
    `GoLean.GoCore.RecoveryCallLayout, `GoLean.GoCore.RecoverySingleton,
    `GoLean.GoCore.RecoveryPool, `GoLean.GoCore.RecoveryChoices,
    `Tests.RecoveryInvariant, `Tests.RecoveryControlAudit,
    `Tests.InterfaceContract, `Tests.BooleanRuntime,
    `Tests.BooleanProgram, `Tests.InterfaceAudit]
  let exports : List Name := [
    ``GoLean.Semantics.iter_iff_trace, ``GoLean.Semantics.Trace.erase,
    ``GoLean.Semantics.run_ok_iff, ``GoLean.Semantics.exists_run_ok_iff,
    ``GoLean.Semantics.Pool.run_iff, ``GoLean.Semantics.Pool.Run.success_reaches,
    ``GoLean.Semantics.Pool.program_run_iff,
    ``GoLean.Semantics.Pool.exists_program_run_iff,
    ``GoLean.Semantics.Pool.observation_iff,
    ``GoLean.Semantics.Pool.fuel_is_not_observation,
    ``GoLean.Semantics.Pool.refusal_is_not_observation,
    ``GoLean.GoCore.Admission.checkBoolean_iff,
    ``GoLean.GoCore.Admission.admitted_index_bound,
    ``GoLean.GoCore.Admission.admitted_all_bodies,
    ``GoLean.GoCore.BooleanTyping.checkTypedBoolean_iff,
    ``GoLean.GoCore.RecoveryTyping.checkRecovery_iff,
    ``GoLean.GoCore.RecoveryTyping.checkRecovery_sound,
    ``GoLean.GoCore.RecoveryTyping.checkRecovery_complete,
    ``GoLean.GoCore.RecoveryTyping.admitted_all_bodies,
    ``GoLean.GoCore.RecoveryTyping.admitted_no_cycle,
    ``GoLean.GoCore.RecoveryTyping.Statement.in_profile,
    ``GoLean.GoCore.RecoveryTyping.Statement.placement,
    ``GoLean.GoCore.RecoveryRuntime.setup_typed,
    ``GoLean.GoCore.RecoveryRuntime.setup_typed_wf,
    ``GoLean.GoCore.RecoveryRuntime.enterFrame_typed,
    ``GoLean.GoCore.RecoveryRuntime.enterFramePick_typed,
    ``GoLean.GoCore.RecoveryRuntime.ResultRoots.load,
    ``GoLean.GoCore.RecoveryRuntime.pinResultLocs_typed,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.pushedDecls,
    ``GoLean.GoCore.RecoveryRuntime.initialState_argument,
    ``GoLean.GoCore.RecoveryRuntime.initialState_result,
    ``GoLean.GoCore.RecoveryRuntime.initialState_readout,
    ``GoLean.GoCore.RecoveryRuntime.typedEntry_wf,
    ``GoLean.GoCore.RecoveryRuntime.ZeroValues.unique,
    ``GoLean.GoCore.RecoveryRuntime.control_progress,
    ``GoLean.GoCore.RecoveryRuntime.control_step,
    ``GoLean.GoCore.RecoveryRuntime.control_stepFn,
    ``GoLean.GoCore.RecoveryRuntime.setup_inv,
    ``GoLean.GoCore.RecoveryRuntime.Inv.step,
    ``GoLean.GoCore.RecoveryRuntime.Inv.steps,
    ``GoLean.GoCore.RecoveryRuntime.Inv.iter,
    ``GoLean.GoCore.RecoveryRuntime.Inv.progress,
    ``GoLean.GoCore.RecoveryRuntime.Inv.reachable_progress,
    ``GoLean.GoCore.RecoveryRuntime.Inv.readout,
    ``GoLean.GoCore.RecoveryRuntime.Inv.run_readout,
    ``GoLean.GoCore.RecoveryRuntime.Inv.run_choices,
    ``GoLean.GoCore.RecoveryRuntime.Inv.reachable_silent,
    ``GoLean.GoCore.RecoveryRuntime.call_entry_control,
    ``GoLean.GoCore.RecoveryRuntime.deferred_entry_control,
    ``GoLean.GoCore.RecoveryRuntime.recover_direct,
    ``GoLean.GoCore.RecoveryRuntime.recover_indirect,
    ``GoLean.GoCore.RecoveryRuntime.ReturnCont.pushDefer,
    ``GoLean.GoCore.BooleanRuntime.setup_boolean,
    ``GoLean.GoCore.BooleanRuntime.bindParams_bool,
    ``GoLean.GoCore.BooleanRuntime.allocDecls_bool,
    ``GoLean.GoCore.BooleanRuntime.store_bool,
    ``GoLean.GoCore.BooleanRuntime.pinResultLocs_bool,
    ``GoLean.GoCore.BooleanRuntime.loadMany_bool,
    ``GoLean.GoCore.BooleanRuntime.EnvRoots.lookup,
    ``GoLean.GoCore.BooleanRuntime.setup_typed_exact,
    ``GoLean.GoCore.BooleanRuntime.bindParams_exact,
    ``GoLean.GoCore.BooleanRuntime.allocDecls_exact,
    ``GoLean.GoCore.BooleanRuntime.initialEnv_argument,
    ``GoLean.GoCore.BooleanRuntime.initialEnv_result,
    ``GoLean.GoCore.BooleanRuntime.initialState_argument,
    ``GoLean.GoCore.BooleanRuntime.initialState_result,
    ``GoLean.GoCore.BooleanRuntime.initialResults_distinct,
    ``GoLean.GoCore.BooleanRuntime.booleanEntry_wf,
    ``GoLean.GoCore.BooleanRuntime.setup_typed,
    ``GoLean.GoCore.BooleanRuntime.setup_typed_exact_inv,
    ``GoLean.GoCore.BooleanRuntime.runProgram_typed,
    ``GoLean.GoCore.BooleanRuntime.Inv.step,
    ``GoLean.GoCore.BooleanRuntime.Inv.steps,
    ``GoLean.GoCore.BooleanRuntime.Inv.reachable_progress,
    ``GoLean.GoCore.BooleanRuntime.Inv.run_choices,
    ``GoLean.GoCore.BooleanRuntime.Inv.run_readout,
    ``GoLean.GoCore.BooleanRuntime.Control.singleton_step,
    ``GoLean.GoCore.BooleanRuntime.Control.no_seq_consumption,
    ``GoLean.GoCore.BooleanRuntime.Inv.pool_eq_runConfig,
    ``GoLean.GoCore.BooleanRuntime.runProgramPool_eq_sequential,
    ``GoLean.GoCore.BooleanRuntime.runProgramPool_typed,
    ``GoLean.GoCore.BooleanRuntime.runProgramPool_no_refusal,
    ``GoLean.GoCore.BooleanRuntime.Inv.success_contract,
    ``GoLean.GoCore.BooleanRuntime.ProgramTests.argument_result,
    ``GoLean.GoCore.BooleanRuntime.ProgramTests.zero_fuel_is_exhaustion,
    ``GoLean.GoCore.BooleanRuntime.ProgramTests.nested_shadow_result,
    ``GoLean.GoCore.BooleanRuntime.ProgramTests.branch_result,
    ``GoLean.GoCore.BooleanRuntime.ProgramTests.zero_local_and_result,
    ``GoLean.GoCore.BooleanRuntime.ProgramTests.terminal_at_zero_fuel,
    ``GoLean.GoCore.BooleanRuntime.Tests.paired_setup,
    ``GoLean.GoCore.BooleanRuntime.Tests.hidden_outer_binding_rejected,
    ``GoLean.GoCore.BooleanRuntime.Tests.hidden_same_scope_binding_rejected,
    ``GoLean.GoCore.BooleanRuntime.Tests.address_bounds_do_not_type_storage,
    ``GoLean.GoCore.BooleanRuntime.Tests.native_argument_setup,
    ``GoLean.GateA1.recover_step_does_not_transport,
    ``GoLean.GateA1.fixed_stream_not_existential_path,
    ``GoLean.GateA1.address_bound_admits_ill_typed,
    ``GoLean.GateA1.both_pool_traces, ``GoLean.GateA1.print_before_panic,
    ``GoLean.GoCore.PanicText.lfPrefix_valid,
    ``GoLean.GoCore.PanicText.firstLine_bytes,
    ``GoLean.GoCore.Machine.utf8String?_bytes,
    ``GoLean.GoCore.RecoveryRuntime.runConfigWithAbort_erasure,
    ``GoLean.GoCore.RecoveryRuntime.stepAbortRecord?_some,
    ``GoLean.GoCore.RecoveryRuntime.execPoolWithAbort_erasure,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbortInts_erasure,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_witness,
    ``GoLean.GoCore.RecoveryRuntime.checkedRunProgramPoolWithAbort_sound,
    ``GoLean.GoCore.RecoveryRuntime.Inv.observation_complete,
    ``GoLean.GoCore.RecoveryRuntime.Inv.observed_abort]
  for m in modules do
    unless env.header.moduleNames.contains m do
      throwError "Semantic interface: missing module {m}"
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Semantic interface: missing theorem {n}"
  -- The text helpers keep the constructive machine-helper boundary,
  -- although the public correspondence layer admits the classical trio:
  -- the String-level first-line bridge and the renderer's own strict
  -- decoder / byte-level first-line projection / member function
  -- (landing chunk L3 — `docs/2026-09-07_land-panic-text-tape.md`).
  for n in [``GoLean.GoCore.PanicText.firstLine,
      ``GoLean.GoCore.Machine.utf8String?, ``GoLean.GoCore.Machine.stringFirstLine?,
      ``GoLean.GoCore.Machine.renderPanicHead, ``GoLean.GoCore.Machine.abortMsg] do
    for ax in (← collectAxioms n) do
      unless [``propext, ``Quot.sound].contains ax do
        throwError "Semantic interface: constructive text helper {n} depends on forbidden axiom {ax}"
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? n with
      | some i => [`GoLean, `Tests].contains env.header.moduleNames[i.toNat]!.getRoot
      | none => true
    unless selected do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Semantic interface: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Semantic interface: {exports.length} required exports; {checked} constants checked (classical trio only)"
