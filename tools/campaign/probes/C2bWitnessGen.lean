import GoLeanProofs.Specs.Raft.DriverNet
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk GoLean.RaftSeam.DriverNet

def wHeap : Heap :=
  [(.base ⟨0⟩, ⟨some (.pointer tyTwin), .addr (.base ⟨1⟩)⟩),
   (.base ⟨1⟩, ⟨some tyTwin, .struct tidTwin
      #[("live", .slice ⟨some (.base ⟨2⟩), 0, 2, 2⟩)]⟩),
   (.base ⟨2⟩, ⟨some (.slice .bool), .array #[.bool true, .bool false]⟩),
   (.base ⟨3⟩, ⟨some .bool, .bool true⟩),
   (.base ⟨4⟩, ⟨some tI, .int 0 .int⟩),
   (.base ⟨5⟩, ⟨some tI, .int 2 .int⟩),
   (.base ⟨6⟩, ⟨some (.map tI .bool), .map ⟨some (.base ⟨7⟩)⟩⟩),
   (.base ⟨7⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨8⟩, ⟨some tI, .int 0 .int⟩)]

def wEnv : LocalEnv :=
  [[("t", .base ⟨0⟩), ("live", .base ⟨6⟩), ("c", .base ⟨8⟩),
    ("$rfirst", .base ⟨3⟩), ("$ridx", .base ⟨4⟩), ("$rlen", .base ⟨5⟩)]]

def wσ : ExecState := { heap := wHeap, nextAddr := 9 }

partial def walkAll (n : Nat) (σ : ExecState) (c : Config) (ch : Choices) : IO Unit := do
  match c with
  | .next .stop =>
      IO.println s!"REACHED .next .stop at {n}"
      IO.println s!"na = {σ.nextAddr}"
      IO.println ((repr σ.heap).pretty 100)
  | _ =>
    if n > 500 then IO.println "fuel out" else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkAll (n+1) σ2 c2 ch2
    | .error e => IO.println s!"ERR@{n} {e.message.take 100}"

#eval walkAll 0 wσ (headCfg "$rfirst" "$ridx" "$rlen" "j" (guardedBody "j" rebThn) wEnv .stop) []
#eval walkAll 0 wσ (headCfg "$rfirst" "$ridx" "$rlen" "i" (guardedBody "i" incThn) wEnv .stop) []
