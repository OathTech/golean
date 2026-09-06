import Tests.DeclarationWire
import Tests.StrictJsonParse
import Lean

open Lean in
def auditDeclarations : CoreM Unit := do
  let env ← getEnv
  for required in [``GoLean.GoCore.Declaration.equality_exact,
      ``GoLean.GoCore.Declaration.Ty.eqb,
      ``GoLean.NativeDeclaration.decode,
      ``GoLean.NativeDeclaration.decodeBytes,
      ``GoLean.StrictJson.parse, ``GoLean.StrictJson.parseBytes,
      ``GoLean.DeclarationWireTests.main] do
    unless env.contains required do throwError "Declaration audit: missing {required}"
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => [ `GoLean, `Tests ].contains env.header.moduleNames[i.toNat]!.getRoot
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration audit: {name} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Declaration audit: {checked} imported/local declarations checked"

#eval auditDeclarations
