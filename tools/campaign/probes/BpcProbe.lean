/- A4-U4 wave-1 probe: becomePreCandidate (BPC) — phase 1 (machine,
concrete, end-to-end from the drained call; steps/choices/projection
vs specBecomePreCandidate) + phase 2 (mirror windows at the U3
fixture with state CONCRETE 0 — the panic guard branches on state, so
it cannot stay symbolic). -/
import GoLean.GoCore.MachineEqb
import GoLeanProofs.Specs.Raft.BfFixture
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

/-- Machine pre-state: the U3 populated fixture at state=0. -/
def bpcσ (vote lead ldT : Int) : ExecState := uσ vote lead 0 ldT

def bpcC : Machine.Config :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)

def mainPhase1 : IO Unit := do
  let σ0 := bpcσ 7 2 5
  let mut s := σ0
  let mut c := bpcC
  let mut ch : Choices := []
  let mut i : Nat := 0
  let mut done := false
  while i < 20000 && !done do
    match c with
    | .next .stop => done := true
    | _ =>
      match stepFn s c ch with
      | .ok (c', s', ch') =>
          c := c'; s := s'; ch := ch'; i := i + 1
      | .error e =>
          IO.println s!"ERROR at step {i}: {repr e}"
          match c with
          | .exec st _ _ => IO.println s!"  at exec {((repr st).pretty 80).replace "\n" " "}"
          | .evalE e2 _ _ => IO.println s!"  at evalE {((repr e2).pretty 80).replace "\n" " "}"
          | _ => IO.println "  at other"
          return
  if done then
    IO.println s!"COMPLETED at step {i}; choices consumed: 0 (started empty)"
    IO.println s!"projection pre  = {repr (absRaftNode σ0 ⟨0⟩)}"
    IO.println s!"projection post = {repr (absRaftNode s ⟨0⟩)}"
    IO.println s!"spec            = {repr ((absRaftNode σ0 ⟨0⟩).map specBecomePreCandidate)}"
    IO.println s!"nextAddr {σ0.nextAddr} -> {s.nextAddr}"
  else IO.println s!"NOT DONE after {i} steps"

/-! Phase 2: mirror. Symbolic fixture = uS0's heap but with the raft
cell's state field CONCRETE 0 (vars 1=Vote 2=lead 4=ldT stay). -/

def bpcSymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (uRaftVal 0 0 0 0))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def bpcSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy bpcSymRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def bpcS0 : SymState := { heap := bpcSymHeap, nextAddr := 21 }

def bpcC0 : SymConfig :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)

def describeC : SymConfig → String
  | .exec st _ _ => s!"exec {((repr st).pretty 70).replace "\n" " "}"
  | .evalE e _ _ => s!"evalE {((repr e).pretty 70).replace "\n" " "}"
  | .retV _ (.callArgsK fid _ _ p _ _) => s!"retV callArgsK {fid.key} pending={p.length}"
  | .retV _ (.stmtOpK op _ _ _ _ _) => s!"retV stmtOpK {((repr op).pretty 40).replace "\n" " "}"
  | .retV _ _ => "retV other"
  | .next (.mapIterK ..) => "next mapIterK"
  | .next _ => "next other"
  | _ => "other"

def mainPhase2 : IO Unit := do
  let (n, S1, C1) := symEvalWindowTB bfTB 4000 bpcS0 bpcC0
  IO.println s!"window 1: {n} steps, lands at: {describeC C1}"
  match stepFnSTB bfTB S1 C1 with
  | .error q => IO.println s!"  quit: {repr q}"
  | .ok _ => IO.println "  (no quit?)"
  -- γ-check against phase 1 if we reached stop
  if let .next .stop := C1 then
    let ρfin : Valuation :=
      { ints := fun i => [0, 7, 2, 0, 5].getD i 0
        bools := fun _ => false, vals := fun _ => .nil
        cells := fun _ => ⟨none, .nil⟩ }
    let σ0 := bpcσ 7 2 5
    let mut ms := σ0
    let mut mc := bpcC
    let mut mch : Choices := []
    for _ in [0:n] do
      match stepFn ms mc mch with
      | .ok (c', s', ch') => mc := c'; ms := s'; mch := ch'
      | .error _ => pure ()
    let img := γS ρfin σ0 S1
    IO.println s!"γ-image heap == machine heap: {img.heap == ms.heap}"
    IO.println s!"nextAddr: γ {img.nextAddr} vs machine {ms.nextAddr}"
    if img.heap != ms.heap then
      for ((l1, c1), (l2, c2)) in img.heap.zip ms.heap do
        if l1 != l2 || c1 != c2 then
          IO.println s!"first diff at {(repr l1).pretty 40}"
          IO.println s!"  γ: {((repr c1).pretty 160).replace "\n" " "}"
          IO.println s!"  m: {((repr c2).pretty 160).replace "\n" " "}"
          break

#eval mainPhase1
#eval mainPhase2

/-! wrap-depth probe: the post-state raft cell's Vote/lead field terms -/
partial def intDepth : GoLean.Sym.SymInt → Nat
  | .norm _ a => 1 + intDepth a
  | _ => 0
def mainDepth : IO Unit := do
  let (_, S1, _) := symEvalWindowTB bfTB 4000 bpcS0 bpcC0
  match GoLean.Sym.Heap.lookup S1.heap (.base ⟨0⟩) with
  | some (.mk _ (.struct _ fs)) =>
      for (n, v) in fs do
        if n == "Vote" || n == "lead" || n == "state" || n == "leadTransferee" then
          match v with
          | .int t _ => IO.println s!"{n}: depth {intDepth t} term {((repr t).pretty 80).replace "\n" " "}"
          | _ => IO.println s!"{n}: non-int"
  | _ => IO.println "no raft cell"
#eval mainDepth
