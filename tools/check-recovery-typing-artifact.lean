import GoLean.NativeToIR
import Tests.RecoveryTypingFixture
import Tests.RecoveryA2Artifact

open Lean GoLean

/-- Compare entire artifacts, including uncalled bodies and metadata.
These executable translation checks do not constitute a compiler theorem. -/
def main (args : List String) : IO Unit := do
  let [a2path, newpath, outsidepath] := args
    | throw (IO.userError "expected A2, second-fixture and excluded valid-Go wire paths")
  for (path, expected, label) in [
      (a2path, GoCore.RecoveryTyping.Tests.a2Program, "complete existing A2"),
      (newpath, GoCore.RecoveryTyping.Tests.nativeRecovery, "second shared-capture fixture")] do
    let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
    let program ← IO.ofExcept (NativeToIR.decodeProgram json)
    unless reprStr program == reprStr expected do
      throw (IO.userError s!"fresh native GoCore differs from {label}")
    IO.println s!"Recovery typing: complete fresh native GoCore matches {label}"
  let outsideJson ← IO.ofExcept (Json.parse (← IO.FS.readFile outsidepath))
  let outside ← IO.ofExcept (NativeToIR.decodeProgram outsideJson)
  match GoCore.RecoveryTyping.checkRecovery outside "panicBoolAbort" #[] with
  | .error (.statementProfile fid) =>
      unless fid.key == "panicBoolAbort" do
        throw (IO.userError s!"unexpected excluded function: {fid.key}")
      IO.println "Recovery diagnostics: fresh typechecked Go panic(true) is outside the string-payload profile"
  | other => throw (IO.userError s!"valid excluded Go received the wrong diagnostic: {reprStr other}")
