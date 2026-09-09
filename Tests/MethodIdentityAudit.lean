import Tests.MethodIdentity
import Lean

open Lean in
def MethodIdentityAudit.run : CoreM Unit := do
  let env ← getEnv
  for required in [``GoLean.MethodIdentityTests.requirement_identity_is_semantic,
      ``GoLean.MethodIdentityTests.method_identity_is_semantic] do
    let some (.thmInfo _) := env.find? required
      | throwError "Method identity audit: missing theorem {required}"
  for required in [``GoLean.NativeDeclaration.decodeMemberId,
      ``GoLean.NativeToIR.decodeProgram, ``GoLean.MethodIdentityTests.main] do
    unless env.contains required do throwError "Method identity audit: missing {required}"
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => [ `GoLean, `Tests ].contains env.header.moduleNames[i.toNat]!.getRoot
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Method identity audit: {name} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Method identity audit: {checked} local/imported declarations checked"
