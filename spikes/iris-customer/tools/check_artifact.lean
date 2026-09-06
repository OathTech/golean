import GoLean.NativeToIR
import GoLeanIris.Program
import GoLeanIris.SharedProgram

/-! Executable regression check, NOT a compiler-correctness theorem. Compare
the complete derived representation of freshly lowered native wire against
the artifact used by the kernel-checked proofs. -/
open GoLean Lean

def main (args : List String) : IO Unit := do
  let [a2Path, sharedPath] := args | throw (IO.userError "expected A2 and shared native wire paths")
  for (path, expected) in [(a2Path, IrisCustomer.recoveryProgram), (sharedPath, IrisCustomer.sharedProgram)] do
    let .ok json := Json.parse (← IO.FS.readFile path)
      | throw (IO.userError "native wire JSON parse failed")
    let .ok program := NativeToIR.decodeProgram json
      | throw (IO.userError "native wire lowering failed")
    unless reprStr program == reprStr expected do
      throw (IO.userError "fresh native GoCore differs from the proved whole program")
  IO.println "Iris customer: both complete fresh native artifacts match the proved programs"
