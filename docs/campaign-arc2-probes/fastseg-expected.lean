/- Campaign Arc 2, U4 MID-BUILD GATE, compiled pre-check (#eval before
any kernel run): the fast segment from the 350k trie checkpoint must
be .ok — a .error naming a fastEval-stub/WIRE arm is the fail-closed
extension signal, printed verbatim. -/
import GoLeanProofs.Specs.TwinCheckpointsF
import GoLeanProofs.FastEval.Step

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open GoLean.FastEval

def seg (k : Nat) : String :=
  match iterF stepFast k ckptF350kState ckptF350k.2.2.1 ckptF350k.2.2.2 with
  | .ok _ => "ok"
  | .error e => s!"ERROR {reprStr e}"

#eval do
  IO.println s!"fastseg 500  : {seg 500}"
  IO.println s!"fastseg 2000 : {seg 2000}"
  IO.println s!"fastseg 20000: {seg 20000}"
