import U1RD8.Simulation
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! Check every declaration belonging to the experiment and its imported
GoLean modules, including private/generated declarations. Toolchain modules
are the pinned trust base. Kernel replay is a separate command. -/
open Lean

def auditRD8 : CoreM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let ours := modules.map fun m => [`GoLean, `GoLeanIris, `RelationalCodeX, `U1RD8].contains m.getRoot
  let mut count : Nat := 0
  let mut findings : Nat := 0
  let mut totalImplementations : Nat := 0
  for (name, info) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => ours[i.toNat]!
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {name} depends on {ax}"
    if info.isUnsafe then
      logInfo m!"TRUST FINDING: unsafe declaration {name}"
      findings := findings + 1
    if let .defnInfo d := info then
      if d.safety == .partial then
        -- Lean also generates these compiler implementations for transparent,
        -- total definitions (including `certify`). They are not new opaque
        -- mathematical definitions. Report that inventory separately.
        match env.find? name.getPrefix with
        | some (.defnInfo parent) =>
          if parent.safety == .safe then
            totalImplementations := totalImplementations + 1
          else
            logInfo m!"TRUST FINDING: partial declaration {name}"
            findings := findings + 1
        | _ =>
          logInfo m!"TRUST FINDING: partial implementation without transparent total parent: {name}"
          findings := findings + 1
    if (Compiler.getImplementedBy? env name).isSome then
      logInfo m!"TRUST FINDING: implemented_by {name}"
      findings := findings + 1
    if isExtern env name then
      logInfo m!"TRUST FINDING: extern {name}"
      findings := findings + 1
    count := count + 1
  for m in modules do
    if [`GoLean, `GoLeanIris, `RelationalCodeX, `U1RD8].contains m.getRoot then
      logInfo m!"REPLAY_MODULE {m}"
  logInfo "REPLAY_MODULE U1RD8.Audit"
  logInfo m!"U1RD8 axiom audit: PASS; {count} declarations; standard axioms only"
  logInfo m!"Compiler inventory: {totalImplementations} generated partial implementations have transparent total kernel definitions"
  if findings > 0 then
    logInfo m!"Trust implementation scan: FAIL; {findings} findings above (not waived)"
  else
    logInfo "Trust implementation scan: PASS"

#eval auditRD8
#print axioms U1RD8.path_plan
#print axioms U1RD8.write_at
#print axioms U1RD8.paths
#print axioms U1RD8.traversal
#print axioms U1RD8.interpret
#print axioms U1RD8.simulation
#print axioms U1RD8.closed_guarded

/-- Claim-point report on actual proof bodies, not theorem headers. -/
def checkBody (name : Name) (needed : List Name) : CoreM Unit := do
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true)
    | throwError "No proof body: {name}"
  for dependency in needed do
    unless body.getUsedConstants.contains dependency do
      throwError "Missing proof-body dependency: {name} -> {dependency}"
  logInfo m!"PROOF_BODY {name}: {needed}"

#eval do
  checkBody ``U1RD8.closed_guarded [``U1RD8.simulation, ``RelationalCodeX.Sweep.guarded_acceptance]
  checkBody ``U1RD8.simulation [``U1RD8.traversal, ``U1RD8.interpret,
    ``GoLean.Logic.Frame.defaults, ``GoLean.GoCore.Machine.Step.unseqEnter]
  checkBody ``U1RD8.traversal [``GoLean.GoCore.Relational.Unseq.Ranked.traversal, ``U1RD8.paths]
  checkBody ``U1RD8.paths [``GoLean.GoCore.Relational.ReadOnlyExprFor.variable,
    ``GoLean.GoCore.Relational.ReadOnlyExprFor.add_int, ``GoLean.GoCore.Relational.read_root,
    ``GoLean.GoCore.Relational.Unseq.ready_produced]
  checkBody ``U1RD8.interpret [``GoLean.GoCore.Relational.Unseq.Traversal.rec,
    ``GoLean.GoCore.Relational.Unseq.scheduler_cover,
    ``GoLean.GoCore.Relational.Unseq.binder_effect,
    ``GoLean.GoCore.Relational.Unseq.completion_path, ``U1RD8.path_plan, ``U1RD8.write_at]
  checkBody ``GoLean.GoCore.Relational.Unseq.Domain.all_schedules
    [``GoLean.GoCore.Relational.Unseq.Ranked.traversal,
     ``GoLean.GoCore.Relational.Unseq.Domain.occurrence]
