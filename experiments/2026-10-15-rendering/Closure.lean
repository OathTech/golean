import Lean
import GoLean.GoCore.Multi
import Lean.Compiler.LCNF.ToDecl
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_elab do
  let env ← getEnv
  for root in [`GoLean.GoCore.Machine.stepFn, `GoLean.GoCore.Machine.stepMulti,
      `GoLean.GoCore.Machine.runProgramM] do
    unless env.contains root do throwError "missing root {root}"
    let mut pending := [root]
    let mut seen : NameSet := {}
    let mut endpoints : NameSet := {}
    repeat
      match pending with
      | [] => break
      | n :: rest =>
        pending := rest
        let project := match env.getModuleIdxFor? n with
          | some i => env.header.moduleNames[i.toNat]!.getRoot == `GoLean
          | none => n.getRoot == `GoLean
        if seen.contains n || !project then continue
        seen := seen.insert n
        let some logical := env.find? n | throwError "missing {n}"
        if let .opaqueInfo _ := logical then endpoints := endpoints.insert n
        let some selected ← Compiler.LCNF.getDeclInfo? n | throwError "missing compiled {n}"
        if let some v := selected.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
    logInfo m!"COMPILED_CLOSURE {root}: {seen.size} project nodes; opaque {endpoints.toList}"
