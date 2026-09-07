import Tests.RecoveryTerminal
import Lean

open Lean

def RecoveryTerminalAudit.exports : List Name := [
    ``GoLean.GoCore.RecoveryRuntime.Inv.run_classified,
    ``GoLean.GoCore.RecoveryRuntime.Inv.run_refusal_named,
    ``GoLean.GoCore.RecoveryRuntime.Inv.observed_abort_member,
    ``GoLean.GoCore.RecoveryRuntime.runProgram_typed,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPool_typed,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPool_refusal_named,
    ``GoLean.GoCore.RecoveryRuntime.runProgram_refusal_named,
    ``GoLean.GoCore.RecoveryRuntime.stepAbortRecord?_member,
    ``GoLean.GoCore.RecoveryRuntime.PoolAbortWitness.string_member,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_member,
    ``GoLean.GoCore.RecoveryRuntime.Control.singleton_front,
    ``GoLean.GoCore.RecoveryRuntime.singleton_observer_string_abort,
    ``GoLean.GoCore.RecoveryRuntime.singleton_observer_string_abort_refused,
    ``GoLean.GoCore.RecoveryRuntime.Control.observer_zero,
    ``GoLean.GoCore.RecoveryRuntime.Control.observer_step,
    ``GoLean.GoCore.RecoveryRuntime.attachAbort_private,
    ``GoLean.GoCore.RecoveryRuntime.Inv.pool_observation_eq,
    ``GoLean.GoCore.RecoveryRuntime.Inv.pool_observation_complete,
    ``GoLean.GoCore.RecoveryRuntime.runConfigWithAbort_nonpanic,
    ``GoLean.GoCore.RecoveryRuntime.Inv.observer_classified,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_typed,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_panic_iff,
    ``GoLean.GoCore.RecoveryRuntime.runProgramPoolWithAbort_refusal_named,
    ``GoLean.GoCore.RecoveryRuntime.abortEventPick?_consumeAtE,
    ``GoLean.GoCore.Machine.utf8String?_bytes,
    ``GoLean.GoCore.Machine.stringFirstLine?_bytes,
    ``GoLean.GoCore.Machine.renderPanicHead_string,
    ``GoLean.GoCore.Machine.abortMsg_string,
    ``GoLean.GoCore.Machine.abortMsg_string_refused,
    ``GoLean.GoCore.Machine.stepFn_string_abort,
    ``GoLean.GoCore.Machine.stepFn_string_abort_refused,
    ``GoLean.GoCore.Machine.runConfig_string_abort,
    ``GoLean.GoCore.Machine.runConfig_string_abort_refused,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.arbitrary_bytes_refusal_named,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.equal_repanic_refusal_named,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.actual_pool_string_frontier,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.actual_pool_string_frontier_refused,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.invalid_utf8_frontier_refused,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.multiline_terminal_retains_tail_bytes,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.equal_repanic_two_members_at_frontier,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.zero_fuel_is_exhaustion,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.zero_result_admitted,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.normal_readout_is_initialized_false,
    ``GoLean.GoCore.RecoveryRuntime.TerminalTests.singleton_observer_preserves_prefix]

/-- Audit after every local module has been imported, including this audit,
unused private helpers and trailing declarations. -/
def RecoveryTerminalAudit.run : CoreM Unit := do
  let env ← getEnv
  for m in [`GoLean.GoCore.StringPanic, `GoLean.GoCore.RecoveryTerminal,
      `GoLean.GoCore.RecoveryPoolObservationTyped,
      `Tests.RecoveryTerminal, `Tests.RecoveryTerminalAudit] do
    unless env.header.moduleNames.contains m do
      throwError "Recovery terminal audit: missing module {m}"
  for n in RecoveryTerminalAudit.exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Recovery terminal audit: missing theorem {n}"
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
        throwError "Recovery terminal audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Recovery terminal audit: {RecoveryTerminalAudit.exports.length} required theorems; {checked} declarations across all imported local origins; classical trio only"

/-- Exact elaborated types, including implicit binders and premises. -/
def RecoveryTerminalAudit.claims : MetaM Json := do
  let env ← getEnv
  let rows ← RecoveryTerminalAudit.exports.mapM fun n => do
    let some info := env.find? n | throwError "missing theorem {n}"
    let moduleName := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => "current"
    let statement := toString (← withOptions
      (fun opts => opts.setBool `pp.structureInstances false) (Meta.ppExpr info.type))
    return Json.mkObj [("name", toJson n.toString), ("module", toJson moduleName),
      ("kernel_type", toJson statement), ("status", toJson "proved; independent review pending")]
  return Json.arr rows.toArray
