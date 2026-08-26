/- becomeLeader machine probe: from candidate state (guard panics on
Follower). Counts steps/choices; classifies the scope decision. -/
import GoLean.GoCore.MachineEqb
import GoLeanProofs.Specs.Raft.BcFixture
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

def blC : Machine.Config :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomeLeader"⟩ [] [] [] [] .stop)

#eval show IO Unit from do
  let σ0 := uσ 7 2 1 5   -- state=1 candidate
  let ch0 : Choices := [3, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  let mut s := σ0
  let mut c := blC
  let mut ch := ch0
  let mut i : Nat := 0
  let mut done := false
  let mut chLen := ch0.length
  while i < 30000 && !done do
    match c with
    | .next .stop => done := true
    | _ =>
      match stepFn s c ch with
      | .ok (c', s', ch') =>
          if ch'.length != chLen then
            IO.println s!"step {i}: CHOICE consumed (left {ch'.length})"
            chLen := ch'.length
          c := c'; s := s'; ch := ch'; i := i + 1
      | .error e =>
          IO.println s!"ERROR at step {i}: {(repr e).pretty 120}"
          return
  if done then
    IO.println s!"COMPLETED at {i}; choices consumed {ch0.length - ch.length}"
    IO.println s!"projection post = {repr (absRaftNode s ⟨0⟩)}"
    IO.println s!"nextAddr -> {s.nextAddr}"
  else IO.println s!"NOT DONE after {i}"
