import Concurrency.Synchronization
import Concurrency.Obstruction
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! Check every declaration belonging to the experiment and its imported
GoLean modules, including private/generated declarations. Toolchain modules
are the pinned trust base. Kernel replay is a separate command. -/
open Lean

def auditConcurrency : CoreM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let ours := modules.map fun m => [`GoLean, `Concurrency].contains m.getRoot
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
    if [`GoLean, `Concurrency].contains m.getRoot then
      logInfo m!"REPLAY_MODULE {m}"
  logInfo "REPLAY_MODULE Concurrency.Audit"
  logInfo m!"Concurrency axiom audit: PASS; {count} declarations; standard axioms only"
  logInfo m!"Compiler inventory: {totalImplementations} generated partial implementations have transparent total kernel definitions"
  if findings > 0 then
    logInfo m!"Trust implementation scan: FAIL; {findings} findings above (not waived)"
  else
    logInfo "Trust implementation scan: PASS"

#eval auditConcurrency

#print axioms Concurrency.effect_reuse
#print axioms Concurrency.variable_phase_pool
#print axioms Concurrency.read_after_disjoint_write
#print axioms Concurrency.variable_no_switch
#print axioms Concurrency.certify_sound
#print axioms Concurrency.accepted
#print axioms Concurrency.first_read
#print axioms Concurrency.second_read
#print axioms Concurrency.actual_driver
#print axioms Concurrency.entry_driver
#print axioms Concurrency.exact_events
#print axioms Concurrency.Sync.transfer_boundary
#print axioms Concurrency.Sync.read_before_handoff_rejected
#print axioms Concurrency.Sync.post_handoff_read
#print axioms Concurrency.Sync.accepted
#print axioms Concurrency.Sync.actual_driver
#print axioms Concurrency.Sync.equal_comparison_loses_rejection
#print axioms Concurrency.Sync.entry_driver
#print axioms GoLean.GoCore.loc_compare_eq_iff
#print axioms GoLean.GoCore.loc_compare_lt_trans
#print axioms GoLean.GoCore.loc_compare_unfold
#print axioms GoLean.GoCore.loc_comparison_unique
#print axioms GoLean.GoCore.ShadowKey.compare_orderCode
#print axioms GoLean.GoCore.Machine.shadowSet_ordered
#print axioms GoLean.GoCore.Machine.ShadowOrdered.keys_nodup
#print axioms GoLean.GoCore.Machine.shadowSet_lookup_self
#print axioms GoLean.GoCore.Machine.shadowSet_lookup_other
#print axioms GoLean.GoCore.Machine.PoolPrefix.shadow_ordered_empty
#print axioms GoLean.GoCore.Machine.PoolPrefix.preserves_lookup
#print axioms Concurrency.Sync.pre_pair_history
#print axioms Concurrency.Sync.pre_pair_rejection
