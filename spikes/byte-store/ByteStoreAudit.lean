import ByteStoreBench
import Lean

open Lean

run_cmd do
  let env ← getEnv
  unless env.header.moduleNames.contains `ByteStore do
    throwError "missing byte-store prototype import"
  let required := [
    ``GoLean.GoCore.ByteStorePrototype.consumeByteElement_eq,
    ``GoLean.GoCore.ByteStorePrototype.consumeByteElement_eq_storeLoc,
    ``GoLean.GoCore.ByteStorePrototype.consumeCertifiedByteElement_eq_storeLoc,
    ``GoLean.GoCore.ByteStorePrototype.normalizeByte_eq,
    ``GoLean.GoCore.ByteStorePrototype.normalizeArray_set,
    ``GoLean.GoCore.ByteStorePrototype.storeByteElement_eq_storeLoc,
    ``GoLean.GoCore.ByteStorePrototype.setByte_result,
    ``GoLean.GoCore.ByteStorePrototype.setByte_preserves,
    ``GoLean.GoCore.ByteStorePrototype.setByte_untouched,
    ``GoLean.GoCore.ByteStorePrototype.storeByteElement_result,
    ``GoLean.GoCore.ByteStorePrototype.storeByteElement_untouched_cell,
    ``GoLean.GoCore.ByteStorePrototype.storeByteElement_preserves,
    ``GoLean.GoCore.ByteStorePrototype.storeCertifiedByteElement_eq_storeLoc]
  for n in required do
    let some (.thmInfo _) := env.find? n | throwError "missing theorem {n}"
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let mut localCount := 0
  let mut checked := 0
  let mut theorems := 0
  for (n, info) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[i.toNat]!
    unless [ `ByteStore, `ByteStoreConsume, `ByteStoreBench ].contains m ||
        m.getRoot == `GoLean do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "byte-store audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
    if [ `ByteStore, `ByteStoreConsume, `ByteStoreBench ].contains m then
      localCount := localCount + 1
      if let .thmInfo _ := info then
        theorems := theorems + 1
        if n.getPrefix == `GoLean.GoCore.ByteStorePrototype ||
            n.getPrefix == `GoLean.GoCore.ByteStorePrototype.Challenges then
          logInfo m!"CLAIM {n}\n{info.type}"
  logInfo s!"PASS: {required.length} required exports; {theorems} local theorems; {localCount} local declarations; {checked} local/imported GoLean declarations audited"
