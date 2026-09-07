import Tests.RecoveryTyping
import Tests.RecoveryDiagnosticControls
import Tests.RecoveryTypingFixture
import Tests.RecoveryA2Artifact
import Lean

open Lean

/-- Run after importing this complete module. Every imported local declaration
is audited, including unused private definitions and the audit's own tail. -/
def RecoveryTypingAudit.run : CoreM Unit := do
  let env ← getEnv
  let requiredModules : List Name := [
    `GoLean.GoCore.RecoveryTypingCore, `GoLean.GoCore.RecoveryExpressions,
    `GoLean.GoCore.RecoveryCalls, `GoLean.GoCore.RecoveryStatements,
    `GoLean.GoCore.RecoveryGraph, `GoLean.GoCore.RecoveryAdmission,
    `GoLean.GoCore.RecoveryDiagnostics, `Tests.RecoveryDiagnosticControls,
    `Tests.RecoveryTyping, `Tests.RecoveryTypingFixture,
    `Tests.RecoveryA2Artifact, `Tests.RecoveryTypingAudit]
  for m in requiredModules do
    unless env.header.moduleNames.contains m do
      throwError "Recovery typing audit: missing module {m}"
  let exports : List Name := [
    ``GoLean.GoCore.RecoveryTyping.checkType_iff,
    ``GoLean.GoCore.RecoveryTyping.checkHas_iff,
    ``GoLean.GoCore.RecoveryTyping.checkNilType_iff,
    ``GoLean.GoCore.RecoveryTyping.checkNilExpr_iff,
    ``GoLean.GoCore.RecoveryTyping.checkExpr_iff,
    ``GoLean.GoCore.RecoveryTyping.checkExprAt_iff,
    ``GoLean.GoCore.RecoveryTyping.checkTarget_iff,
    ``GoLean.GoCore.RecoveryTyping.checkTargetAt_iff,
    ``GoLean.GoCore.RecoveryTyping.checkArguments_iff,
    ``GoLean.GoCore.RecoveryTyping.checkTargets_iff,
    ``GoLean.GoCore.RecoveryTyping.checkCaptures_iff,
    ``GoLean.GoCore.RecoveryTyping.checkDirectCall_iff,
    ``GoLean.GoCore.RecoveryTyping.checkClosureCall_iff,
    ``GoLean.GoCore.RecoveryTyping.checkDeferredCall_iff,
    ``GoLean.GoCore.RecoveryTyping.checkAssignment_iff,
    ``GoLean.GoCore.RecoveryTyping.checkPanicArgument_iff,
    ``GoLean.GoCore.RecoveryTyping.afterStmt_neutral,
    ``GoLean.GoCore.RecoveryTyping.checkStmt_iff,
    ``GoLean.GoCore.RecoveryTyping.checkStmts_iff,
    ``GoLean.GoCore.RecoveryTyping.callIds_iff,
    ``GoLean.GoCore.RecoveryTyping.checkCallDepth_iff,
    ``GoLean.GoCore.RecoveryTyping.CallDepth.no_cycle,
    ``GoLean.GoCore.RecoveryTyping.checkReturns_iff,
    ``GoLean.GoCore.RecoveryTyping.checkFunction_iff,
    ``GoLean.GoCore.RecoveryTyping.checkFunctions_iff,
    ``GoLean.GoCore.RecoveryTyping.checkRecovery_iff,
    ``GoLean.GoCore.RecoveryTyping.checkRecovery_sound,
    ``GoLean.GoCore.RecoveryTyping.checkRecovery_complete,
    ``GoLean.GoCore.RecoveryTyping.Statement.in_profile,
    ``GoLean.GoCore.RecoveryTyping.Statement.placement,
    ``GoLean.GoCore.RecoveryTyping.Tests.valid_boolean_panic_is_outside_profile,
    ``GoLean.GoCore.RecoveryTyping.Tests.malformed_assignment_is_scoped_failure,
    ``GoLean.GoCore.RecoveryTyping.Tests.malformed_bare_initialization_is_placement_failure,
    ``GoLean.GoCore.RecoveryTyping.Tests.diagnostic_checks_do_not_narrow,
    ``GoLean.GoCore.RecoveryTyping.admitted_all_bodies,
    ``GoLean.GoCore.RecoveryTyping.admitted_no_cycle,
    ``GoLean.GoCore.RecoveryTyping.Tests.a2_recovered,
    ``GoLean.GoCore.RecoveryTyping.Tests.a2_normal,
    ``GoLean.GoCore.RecoveryTyping.Tests.a2_uncaught,
    ``GoLean.GoCore.RecoveryTyping.Tests.shared_admitted,
    ``GoLean.GoCore.RecoveryTyping.Tests.outside_admitted,
    ``GoLean.GoCore.RecoveryTyping.Tests.reversed_control_admitted,
    ``GoLean.GoCore.RecoveryTyping.Tests.direct_control_admitted,
    ``GoLean.GoCore.RecoveryTyping.Tests.arbitrary_byte_payload_admits,
    ``GoLean.GoCore.RecoveryTyping.Tests.equal_repanic_admits,
    ``GoLean.GoCore.RecoveryTyping.Tests.malformed_uncalled_body_rejects]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Recovery typing audit: missing theorem {n}"
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
        throwError "Recovery typing audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Recovery typing audit: {exports.length} required theorems present; {checked} constants checked across all imported local modules (classical trio only)"
