/- Compiled expected-shape check for the smaller mid-run segments. -/
import GoLeanProofs.Specs.TwinCheckpoints
open GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
def shape (k : Nat) : String :=
  match stepFnIter k ckpt350kState ckpt350kCfg ckpt350kCh with
  | .ok _ => "ok" | .error e => s!"ERROR {reprStr e}"
#eval do
  IO.println s!"seg 100 : {shape 100}"
  IO.println s!"seg 250 : {shape 250}"
