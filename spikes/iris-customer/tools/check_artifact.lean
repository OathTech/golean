import GoLean.NativeToIR
import GoLeanIris.Program

/-! Executable regression check, NOT a compiler-correctness theorem. Compare
the complete derived representation of freshly lowered native wire against
the artifact used by the kernel-checked proofs. -/
open GoLean Lean

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one native wire path")
  let .ok json := Json.parse (← IO.FS.readFile path)
    | throw (IO.userError "native wire JSON parse failed")
  let .ok program := NativeToIR.decodeProgram json
    | throw (IO.userError "native wire lowering failed")
  unless reprStr program == reprStr IrisCustomer.recoveryProgram do
    throw (IO.userError "fresh native GoCore differs from the proved program")
  IO.println "Iris customer: freshly emitted/lowered GoCore matches the proof artifact"
