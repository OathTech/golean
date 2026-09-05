import GoLean.NativeToIR
import Tests.GoCoreAdmissionFixture

open Lean GoLean

/-- Executable whole-artifact equality check, not a compiler theorem. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one native wire path")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let program ← IO.ofExcept (NativeToIR.decodeProgram json)
  unless reprStr program == reprStr GoCore.Admission.Tests.fixture do
    throw (IO.userError "fresh native GoCore differs from admission proof fixture")
  IO.println "Admission: complete fresh native GoCore matches the proof fixture"
