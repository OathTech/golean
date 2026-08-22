/- Campaign Arc 2, U2: compiled expected-shape check for the mid-run
segment probes (#eval before you prove). 350000 + 8000 < 711616, so
every window must be .ok (no terminal reached). -/
import GoLeanProofs.Specs.TwinCheckpoints

open GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin

def shape (k : Nat) : String :=
  match stepFnIter k ckpt350kState ckpt350kCfg ckpt350kCh with
  | .ok _ => "ok"
  | .error e => s!"ERROR {reprStr e}"

#eval do
  IO.println s!"seg 500  : {shape 500}"
  IO.println s!"seg 2000 : {shape 2000}"
  IO.println s!"seg 8000 : {shape 8000}"
