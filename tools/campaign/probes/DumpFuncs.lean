import GoLean
open GoLean GoLean.GoCore
def main : IO Unit := do
  let txt ← IO.FS.readFile "baselines/golden/twin-chdriver.wire.json"
  let json ← match Lean.Json.parse txt with
    | .ok j => pure j | .error e => throw (IO.userError s!"parse: {e}")
  let prog ← match NativeToIR.decodeProgram json with
    | .ok p => pure p | .error e => throw (IO.userError s!"decode: {e}")
  for name in ["raft.raft.abortLeaderTransfer", "tracker.ProgressTracker.ResetVotes", "raft.raft.resetRandomizedElectionTimeout"] do
    match findFunctionIn? prog.funcs ⟨name⟩ with
    | some f =>
        IO.println s!"=== {name} args={(repr f.args).pretty 240}"
        IO.println ((repr f.body).pretty 110)
    | none => IO.println s!"=== {name} NOT FOUND"
