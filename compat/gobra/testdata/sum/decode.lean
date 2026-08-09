import GoLean.NativeToIR
def main : IO Unit := do
  let raw ← IO.FS.readFile "compat/gobra/testdata/sum/wire.json"
  match Lean.Json.parse raw with
  | .error e => IO.println s!"PARSE ERROR: {e}"
  | .ok json =>
    match GoLean.NativeToIR.decodeProgram json with
    | .error e => IO.println s!"DECODE ERROR: {e}"
    | .ok prog => IO.println (repr prog)
