import U1.Controls
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! Check every declaration belonging to the experiment and its imported
GoLean modules, including private/generated declarations. Toolchain modules
are the pinned trust base. Kernel replay is a separate command. -/
open Lean

def auditU1 : CoreM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let ours := modules.map fun m => [`GoLean, `U1].contains m.getRoot
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
    if [`GoLean, `U1].contains m.getRoot then
      logInfo m!"REPLAY_MODULE {m}"
  logInfo "REPLAY_MODULE U1.Audit"
  logInfo m!"U1 axiom audit: PASS; {count} declarations; standard axioms only"
  logInfo m!"Compiler inventory: {totalImplementations} generated partial implementations have transparent total kernel definitions"
  if findings > 0 then
    logInfo m!"Trust implementation scan: FAIL; {findings} findings above (not waived)"
  else
    logInfo "Trust implementation scan: PASS"

#eval auditU1


#print axioms GoLean.GoCore.Relational.loadLoc_agrees
#print axioms GoLean.GoCore.Relational.write_preserves_load
#print axioms GoLean.GoCore.Relational.allocations_distinct_bounds
#print axioms GoLean.GoCore.Relational.SafeUntil.eventually
#print axioms GoLean.GoCore.Relational.SafeUntil.observe
#print axioms GoLean.GoCore.Relational.SafeUntil.output
#print axioms GoLean.GoCore.Relational.SafeUntil.prefix_fact
#print axioms GoLean.GoCore.Relational.Unseq.Ranked.progress
#print axioms GoLean.GoCore.Relational.Unseq.HeapDomain.ofAllocation
#print axioms GoLean.GoCore.Relational.Unseq.HeapDomain.At.write
#print axioms GoLean.GoCore.Relational.Unseq.Domain.all_schedules
#print axioms GoLean.GoCore.Relational.Unseq.Domain.sequentialization
#print axioms GoLean.GoCore.Relational.Unseq.Domain.enter
#print axioms GoLean.GoCore.Relational.Unseq.Domain.canonical_entry
#print axioms U1.Symbolic.domain
#print axioms U1.Symbolic.from_entry
#print axioms U1.Symbolic.canonical
#print axioms U1.Controls.alias_order
#print axioms U1.Controls.output_order
#print axioms U1.Controls.allocation_bound

#print axioms U1.Controls.print_has_no_heap_effect

#print axioms GoLean.GoCore.Relational.SafeUntil.observe_prefix

#print axioms GoLean.GoCore.Relational.ReadOnlyExprFor.add_int
#print axioms GoLean.GoCore.Relational.Unseq.Ranked.traversal
#print axioms GoLean.GoCore.Relational.Unseq.scheduler_cover
#print axioms GoLean.GoCore.Relational.Unseq.binder_effect
#print axioms GoLean.GoCore.Relational.Unseq.completion_path
