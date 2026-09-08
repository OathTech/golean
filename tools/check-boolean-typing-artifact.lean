import GoLean.NativeToIR
import Tests.BooleanTypingFixture

open Lean GoLean

/-- Executable whole-artifact equality; this does not prove compilation. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one native wire path")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let program ← IO.ofExcept (NativeToIR.decodeProgram json)
  unless reprStr program == reprStr GoCore.BooleanTyping.Tests.nativeFixture do
    throw (IO.userError "fresh native GoCore differs from Boolean typing fixture")
  IO.println "Boolean typing: complete fresh native GoCore matches the proof fixture"
