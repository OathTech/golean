import GoLeanProofs.Sym.TableExt
import GoLeanProofs.Specs.Raft.BecomeFollowerWitness
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

-- replicate the fixture (module not yet built)
def embedGoF : Nat → GoValue → SymValue
  | 0, _ => .atom 0
  | _ + 1, .unit => .unit
  | _ + 1, .bool b => .bool (.lit b)
  | _ + 1, .int v k => .int (.lit v) k
  | _ + 1, .float bits k => .float bits k
  | _ + 1, .string s => .string s
  | _ + 1, .addr l => .addr l
  | _ + 1, .nil => .nil
  | fuel + 1, .interface d v => .interface d (embedGoF fuel v)
  | fuel + 1, .struct tid fs =>
      .struct tid (fs.map (fun p => (p.1, embedGoF fuel p.2)))
  | fuel + 1, .array vs => .array (vs.map (embedGoF fuel))
  | _ + 1, .slice sv => .slice sv
  | _ + 1, .map mv => .map mv
  | fuel + 1, .mapData entries =>
      .mapData (entries.map (fun p => (embedGoF fuel p.1, embedGoF fuel p.2)))
  | _ + 1, .chan cv => .chan cv
  | fuel + 1, .chanData buf cap closed =>
      .chanData (buf.map (embedGoF fuel)) cap closed
  | fuel + 1, .funcVal fid captured =>
      .funcVal fid (captured.map (embedGoF fuel))
  | _ + 1, .syncData p => .syncData p
def embedGo (v : GoValue) : SymValue := embedGoF valueEqbFuel v
def setSymField (v : SymValue) (name : String) (nv : SymValue) : SymValue :=
  match v with
  | .struct tid fs =>
      .struct tid (fs.map (fun p => if p.1 == name then (p.1, nv) else p))
  | v => v
def twinTypes : TypeEnv := wBase.types
def symRaftVal : SymValue :=
  setSymField (setSymField (setSymField (setSymField
    (setSymField (embedGo wRaftVal) "Term" (.int (.var 0) .uint64))
    "Vote" (.int (.var 1) .uint64)) "lead" (.int (.var 2) .uint64))
    "state" (.int (.var 3) .uint64)) "leadTransferee" (.int (.var 4) .uint64)
def altS₀ : SymState :=
  { heap := [(.base ⟨0⟩, .mk (some tyRaft) symRaftVal),
             (.base ⟨1⟩, .mk (some tyRaftLog) (embedGo wLogVal)),
             (.base ⟨2⟩, .mk (some (.pointer tyRaft)) (.addr (.base ⟨0⟩)))],
    nextAddr := 3 }
def altC₀ : SymConfig :=
  .exec altBody [[("r", .base ⟨2⟩)]] (.frame [] [] [] [] .stop false)

def mainOld : IO Unit := do
  let (n, _S', _C') := symEvalWindowT twinTypes 20 altS₀ altC₀
  IO.println s!"window steps completed (budget 20): {n}"
  -- step-by-step quit diagnosis
  let mut S := altS₀
  let mut C := altC₀
  for i in [0:20] do
    match stepFnST twinTypes S C with
    | .ok (C', S') => S := S'; C := C'
    | .error q => IO.println s!"quit at step {i}: {repr q}"; break
  IO.println "done"

def ρ₀ : Valuation :=
  { ints := fun i => [7, 3, 2, 1, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

def main : IO Unit := do
  let out := (symEvalWindowT twinTypes 14 altS₀ altC₀).2.1
  let post := absRaftNode (γS ρ₀ wBase out) ⟨0⟩
  let pre := absRaftNode (γS ρ₀ wBase altS₀) ⟨0⟩
  IO.println s!"post = {repr post}"
  IO.println s!"pre  = {repr pre}"
  IO.println s!"eq: {post == pre}"
