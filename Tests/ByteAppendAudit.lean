import Tests.ByteAppendRuntime
import Lean

open Lean in
def auditByteAppend : CoreM Unit := do
  let env ← getEnv
  for required in [``GoLean.GoCore.ByteArrayStore.normalizeListAcc_eq,
      ``GoLean.GoCore.ByteArrayStore.firstByteElement_eq_storeLoc,
      ``GoLean.GoCore.ByteArrayStore.firstByteElement_normal,
      ``GoLean.GoCore.ByteArrayStore.certifiedByteList_eq,
      ``GoLean.GoCore.ByteArrayStore.appendValuesFast_eq,
      ``GoLean.GoCore.Machine.applyStmtOp_byteAppend_exact] do
    unless env.contains required do throwError "Byte append audit: missing {required}"
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => [ `GoLean, `Tests ].contains env.header.moduleNames[i.toNat]!.getRoot
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Byte append audit: {name} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Byte append audit: {checked} imported/local declarations checked"

#eval auditByteAppend
