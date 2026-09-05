import GateA1.Examples
import Lean

/-! Dependency check invoked by an external harness AFTER importing every
complete spike module. Running it here would miss declarations later in this
module or the aggregate. Include private and generated constants by module of
origin, not by declaration prefix.
Lineage: CerberusHeapLang/Audit.lean's module-origin sweep. -/
open Lean

def GateA1Audit.run : CoreM Unit := do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let exports : List Name := [
    ``GoLean.GateA1.iter_iff_trace,
    ``GoLean.GateA1.run_ok_iff,
    ``GoLean.GateA1.recover_step_does_not_transport,
    ``GoLean.GateA1.fixed_stream_not_existential_path,
    ``GoLean.GateA1.Pool.run_iff,
    ``GoLean.GateA1.Pool.program_run_iff,
    ``GoLean.GateA1.Pool.exists_program_run_iff,
    ``GoLean.GateA1.Pool.observation_iff,
    ``GoLean.GateA1.both_pool_traces,
    ``GoLean.GateA1.print_before_panic,
    ``GoLean.GateA1.Customer.recover_check_runs,
    ``GoLean.GateA1.Customer.wp_recover_check]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Gate A1: missing theorem {n}"
  let ours := env.header.moduleNames.map (fun n => n.getRoot == `GateA1)
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some i => ours[i.toNat]!
      | none => true
    unless localModule do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Gate A1: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Gate A1: {exports.length} required exports present; {checked} constants' axiom dependencies checked (classical trio only)"
