import Tests.BooleanTyping
import Tests.BooleanTypingFixture
import Lean

open Lean

/-- Execute after importing the complete audit module in another file.
Every declaration in every imported local supporting module is included,
not just the required exports or constants reachable from those exports. -/
def BooleanTypingAudit.run : CoreM Unit := do
  let env ← getEnv
  let requiredModules : List Name := [
    `GoLean.GoCore.BooleanTyping, `Tests.BooleanTyping,
    `Tests.BooleanTypingFixture, `Tests.BooleanTypingAudit]
  for m in requiredModules do
    unless env.header.moduleNames.contains m do
      throwError "Boolean typing audit: missing module {m}"
  let exports : List Name := [
    ``GoLean.GoCore.BooleanTyping.checkExpr_iff,
    ``GoLean.GoCore.BooleanTyping.checkStmt_iff,
    ``GoLean.GoCore.BooleanTyping.checkStmts_iff,
    ``GoLean.GoCore.BooleanTyping.checkReturns_iff,
    ``GoLean.GoCore.BooleanTyping.checkTypedBoolean_iff,
    ``GoLean.GoCore.BooleanTyping.checkTypedBoolean_sound,
    ``GoLean.GoCore.BooleanTyping.checkTypedBoolean_complete,
    ``GoLean.GoCore.BooleanTyping.stmts_append_iff,
    ``GoLean.GoCore.BooleanTyping.Tests.old_unbound_rejected,
    ``GoLean.GoCore.BooleanTyping.Tests.argument_function_typed,
    ``GoLean.GoCore.BooleanTyping.Tests.zero_result_function_typed,
    ``GoLean.GoCore.BooleanTyping.Tests.native_shadow]
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Boolean typing audit: missing theorem {n}"
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
        throwError "Boolean typing audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Boolean typing audit: {exports.length} required theorems present; {checked} constants checked across all imported local modules (classical trio only)"
