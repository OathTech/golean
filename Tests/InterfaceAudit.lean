import Tests.InterfaceContract
import Lean

/-! The command runs from a separate harness after complete imports. Origin
selection also checks unused private, generated and trailing declarations. -/
open Lean

def InterfaceAudit.run : CoreM Unit := do
  let env ← getEnv
  for m in env.header.moduleNames do
    if [`Iris, `GateA1, `GoLeanIris].contains m.getRoot then
      throwError "Semantic interface: forbidden customer dependency {m}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let modules : List Name := [
    `GoLean.GoCore.Trace, `GoLean.GoCore.PoolTrace,
    `GoLean.GoCore.ProgramTrace, `GoLean.Interface,
    `Tests.InterfaceContract, `Tests.InterfaceAudit]
  let exports : List Name := [
    ``GoLean.Semantics.iter_iff_trace, ``GoLean.Semantics.Trace.erase,
    ``GoLean.Semantics.run_ok_iff, ``GoLean.Semantics.exists_run_ok_iff,
    ``GoLean.Semantics.Pool.run_iff, ``GoLean.Semantics.Pool.Run.success_reaches,
    ``GoLean.Semantics.Pool.program_run_iff,
    ``GoLean.Semantics.Pool.exists_program_run_iff,
    ``GoLean.Semantics.Pool.observation_iff,
    ``GoLean.Semantics.Pool.fuel_is_not_observation,
    ``GoLean.Semantics.Pool.refusal_is_not_observation,
    ``GoLean.GateA1.recover_step_does_not_transport,
    ``GoLean.GateA1.fixed_stream_not_existential_path,
    ``GoLean.GateA1.address_bound_admits_ill_typed,
    ``GoLean.GateA1.both_pool_traces, ``GoLean.GateA1.print_before_panic]
  for m in modules do
    unless env.header.moduleNames.contains m do
      throwError "Semantic interface: missing module {m}"
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Semantic interface: missing theorem {n}"
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? n with
      | some i => modules.contains env.header.moduleNames[i.toNat]!
      | none => true
    unless selected do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Semantic interface: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Semantic interface: {exports.length} required exports; {checked} constants checked (classical trio only)"
