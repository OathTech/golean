import GoLeanIris.Driver
import GateA1
import Lean

/-! Invoked only by an external harness after all complete customer modules
are imported. Module-origin selection includes private, generated, aggregate
and trailing declarations. A1's complete adapter is swept as well. -/
open Lean

def GoLeanIrisAudit.run : CoreM Unit := do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let exports : List Name := [
    ``GoLean.IrisCustomer.get?_heapToMap,
    ``GoLean.IrisCustomer.heapToMap_set,
    ``GoLean.IrisCustomer.heapToMap_push,
    ``GoLean.IrisCustomer.wp_read_step,
    ``GoLean.IrisCustomer.wp_write_step,
    ``GoLean.IrisCustomer.wp_alloc_step,
    ``GoLean.IrisCustomer.wp_recover_assignment,
    ``GoLean.IrisCustomer.wp_normal,
    ``GoLean.IrisCustomer.wp_recovered,
    ``GoLean.IrisCustomer.heap_adequacy,
    ``GoLean.IrisCustomer.adequate_execStmtLoop,
    ``GoLean.IrisCustomer.recovered_adequate,
    ``GoLean.IrisCustomer.framed_normal_adequate,
    ``GoLean.IrisCustomer.adequate_program_result,
    ``GoLean.IrisCustomer.recovered_terminates,
    ``GoLean.IrisCustomer.recovered_program,
    ``GoLean.IrisCustomer.normal_program_result,
    ``GoLean.IrisCustomer.uncaught_program]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Iris customer: missing theorem {n}"
  let ours := env.header.moduleNames.map
    (fun n => n.getRoot == `GoLeanIris || n.getRoot == `GateA1 ||
      [`GoLean.GoCore.Trace, `GoLean.GoCore.PoolTrace,
       `GoLean.GoCore.ProgramTrace, `GoLean.Interface, `Tests.InterfaceContract].contains n)
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some i => ours[i.toNat]!
      | none => true
    unless localModule do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Iris customer: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Iris customer: {exports.length} required exports present; {checked} constants' axiom dependencies checked (classical trio only)"
