import Tests.BooleanInvariant
import Tests.BooleanProgram
import Lean

open Lean

/-- Invoke from a separate importer, after all declarations in this module
have been compiled. Check every local module origin, including unused and
private declarations and the current importing module. -/
def BooleanSafetyAudit.run : CoreM Unit := do
  let env ← getEnv
  let requiredModules : List Name := [
    `GoLean.GoCore.BooleanTyping, `GoLean.GoCore.BooleanStore,
    `GoLean.GoCore.BooleanControlTyping, `GoLean.GoCore.BooleanControl,
    `GoLean.GoCore.BooleanInvariant, `GoLean.GoCore.BooleanProgress,
    `GoLean.GoCore.BooleanPreservation, `GoLean.GoCore.BooleanSafety,
    `GoLean.GoCore.BooleanInitialization, `GoLean.GoCore.BooleanProgram,
    `GoLean.GoCore.BooleanPool,
    `Tests.BooleanInvariant, `Tests.BooleanProgram, `Tests.BooleanSafetyAudit]
  for m in requiredModules do
    unless env.header.moduleNames.contains m do
      throwError "Boolean runtime audit: missing module {m}"
  let exports : List Name := [
    ``GoLean.GoCore.BooleanRuntime.ControlStmt.of_static,
    ``GoLean.GoCore.BooleanRuntime.ControlStmts.of_static,
    ``GoLean.GoCore.BooleanRuntime.control_seqCont,
    ``GoLean.GoCore.BooleanRuntime.Control.initialization_environment,
    ``GoLean.GoCore.BooleanRuntime.block_setup,
    ``GoLean.GoCore.BooleanRuntime.initial_control,
    ``GoLean.GoCore.BooleanRuntime.Inv.readout,
    ``GoLean.GoCore.BooleanRuntime.Inv.progress,
    ``GoLean.GoCore.BooleanRuntime.control_advances,
    ``GoLean.GoCore.BooleanRuntime.control_stepFn,
    ``GoLean.GoCore.BooleanRuntime.control_step,
    ``GoLean.GoCore.BooleanRuntime.Inv.step,
    ``GoLean.GoCore.BooleanRuntime.Inv.steps,
    ``GoLean.GoCore.BooleanRuntime.Inv.reachable_progress,
    ``GoLean.GoCore.BooleanRuntime.Inv.iter,
    ``GoLean.GoCore.BooleanRuntime.runConfig_eq_loop,
    ``GoLean.GoCore.BooleanRuntime.Inv.run_ok_or_fuelOut,
    ``GoLean.GoCore.BooleanRuntime.Inv.run_no_refusal,
    ``GoLean.GoCore.BooleanRuntime.Inv.run_readout,
    ``GoLean.GoCore.BooleanRuntime.Inv.run_choices,
    ``GoLean.GoCore.BooleanRuntime.Inv.reachable_silent,
    ``GoLean.GoCore.BooleanRuntime.setup_typed,
    ``GoLean.GoCore.BooleanRuntime.setup_typed_exact_inv,
    ``GoLean.GoCore.BooleanRuntime.runProgram_typed,
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
    ``GoLean.GoCore.BooleanRuntime.Tests.staged_initialization_inv,
    ``GoLean.GoCore.BooleanRuntime.Tests.staged_successor,
    ``GoLean.GoCore.BooleanRuntime.Tests.staged_no_refusal,
    ``GoLean.GoCore.BooleanRuntime.Tests.foreign_initialization_rejected,
    ``GoLean.GoCore.BooleanRuntime.Tests.hidden_dangling_binding_rejected,
    ``GoLean.GoCore.BooleanRuntime.Tests.actual_scope_restoration,
    ``GoLean.GoCore.BooleanRuntime.Tests.actual_new_local_zero]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Boolean runtime audit: missing theorem {n}"
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
        throwError "Boolean runtime audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Boolean runtime audit: {exports.length} required theorems present; {checked} constants checked across all imported local modules (classical trio only)"
