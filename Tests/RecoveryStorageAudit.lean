import Tests.RecoveryStorage
import Lean

open Lean

/-- Post-import audit of the complete supporting closure, including unused
private declarations and declarations after this audit's definition. -/
def RecoveryStorageAudit.run : CoreM Unit := do
  let env ← getEnv
  let modules : List Name := [
    `GoLean.GoCore.RecoveryStore, `GoLean.GoCore.RecoveryEnvironment,
    `GoLean.GoCore.RecoveryAllocation, `GoLean.GoCore.RecoveryOperators,
    `GoLean.GoCore.RecoveryContext, `GoLean.GoCore.RecoveryControlTyping,
    `Tests.RecoveryStorage, `Tests.RecoveryStorageAudit]
  for m in modules do
    unless env.header.moduleNames.contains m do
      throwError "Recovery storage audit: missing module {m}"
  let exports : List Name := [
    ``GoLean.GoCore.RecoveryRuntime.Extends.push,
    ``GoLean.GoCore.RecoveryRuntime.AddressTyped.mono,
    ``GoLean.GoCore.RecoveryRuntime.ValueTyped.mono,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.address_bound,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.load,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.live_reference,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.alloc,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.allocated_address,
    ``GoLean.GoCore.RecoveryRuntime.HeapTyped.store,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.mono,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.push,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.declare,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.load,
    ``GoLean.GoCore.RecoveryRuntime.default_storage,
    ``GoLean.GoCore.RecoveryRuntime.allocDecls_typed,
    ``GoLean.GoCore.RecoveryRuntime.bindParams_typed,
    ``GoLean.GoCore.RecoveryRuntime.StrictTyped.apply,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.compatible,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.append,
    ``GoLean.GoCore.RecoveryRuntime.EnvTyped.included_append_right,
    ``GoLean.GoCore.RecoveryRuntime.ControlStmt.of_static,
    ``GoLean.GoCore.RecoveryRuntime.ControlStmts.of_static,
    ``GoLean.GoCore.RecoveryRuntime.ControlStmt.weaken,
    ``GoLean.GoCore.RecoveryRuntime.ControlStmts.append,
    ``GoLean.GoCore.RecoveryRuntime.Tests.dangling_pointer_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.wrong_pointee_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.hidden_dangling_binding_rejected,
    ``GoLean.GoCore.RecoveryRuntime.Tests.mixed_shadow_cannot_use_hidden_boolean,
    ``GoLean.GoCore.RecoveryRuntime.Tests.declaration_does_not_preserve_old_sort,
    ``GoLean.GoCore.RecoveryRuntime.Tests.aliases_remain_live_after_write,
    ``GoLean.GoCore.RecoveryRuntime.Tests.write_keeps_both_actual_aliases,
    ``GoLean.GoCore.RecoveryRuntime.Tests.arbitrary_payload_bytes_comparable]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Recovery storage audit: missing theorem {n}"
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
        throwError "Recovery storage audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Recovery storage audit: {exports.length} required theorems present; {checked} constants checked across all imported local modules (classical trio only)"
