/- A4-U4 wave-1 probe: becomeCandidate (BC) — phase 1 (machine,
concrete, end-to-end; steps/choices/projection vs specBecomeCandidate)
+ phase 2 (mirror walk with the U3 crossings at the fixture with
state CONCRETE 0; window sizes for the BcFixture chain). reset runs
the TERM-CHANGE branch (Term 0 → 1): Vote is cleared then set to
r.id, so ALL pre-symbolic scalars die — expect no side conditions. -/
import GoLean.GoCore.MachineEqb
import GoLeanProofs.Specs.Raft.BfFixture
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

def bcσ (vote lead ldT : Int) : ExecState := uσ vote lead 0 ldT

def bcCm : Machine.Config :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomeCandidate"⟩ [] [] [] [] .stop)

def mainPhase1 : IO Unit := do
  let σ0 := bcσ 7 2 5
  let ch0 : Choices := [3, 1, 0, 0]
  let mut s := σ0
  let mut c := bcCm
  let mut ch := ch0
  let mut i : Nat := 0
  let mut done := false
  let mut chLen := ch0.length
  while i < 20000 && !done do
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
          IO.println s!"ERROR at step {i}: {repr e}"
          return
  if done then
    IO.println s!"COMPLETED at step {i}; choices consumed {ch0.length - ch.length}"
    IO.println s!"projection pre  = {repr (absRaftNode σ0 ⟨0⟩)}"
    IO.println s!"projection post = {repr (absRaftNode s ⟨0⟩)}"
    IO.println s!"spec (id=1)     = {repr ((absRaftNode σ0 ⟨0⟩).map (fun n => specBecomeCandidate n 1))}"
    IO.println s!"nextAddr {σ0.nextAddr} -> {s.nextAddr}"
  else IO.println s!"NOT DONE after {i} steps"

/-! Phase 2: mirror walk (state concrete 0; vars 1/2/4). -/

def bcSymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (uRaftVal 0 0 0 0))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def bcSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy bcSymRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def bcS0 : SymState := { heap := bcSymHeap, nextAddr := 21 }
def bcC0 : SymConfig :=
  .retV (.addr (.base ⟨0⟩))
    (.callArgsK ⟨"raft.raft.becomeCandidate"⟩ [] [] [] [] .stop)

def describeC : SymConfig → String
  | .exec st _ _ => s!"exec {((repr st).pretty 70).replace "\n" " "}"
  | .evalE e _ _ => s!"evalE {((repr e).pretty 70).replace "\n" " "}"
  | .retV _ (.callArgsK fid _ _ p _ _) => s!"retV callArgsK {fid.key} pending={p.length}"
  | .retV _ (.stmtOpK op _ _ _ _ _) => s!"retV stmtOpK {((repr op).pretty 40).replace "\n" " "}"
  | .retV _ _ => "retV other"
  | .next (.mapIterK ..) => "next mapIterK"
  | .next _ => "next other"
  | _ => "other"

partial def intDepth : GoLean.Sym.SymInt → Nat
  | .norm _ a => 1 + intDepth a
  | _ => 0

def mainWalk : IO Unit := do
  let mut S := bcS0
  let mut C := bcC0
  let mut total : Nat := 0
  let mut windows : List Nat := []
  let mut crossings : List String := []
  let mut pickVar : Nat := 5
  let mut sortSeen := false
  for _ in [0:40] do
    if let .next .stop := C then break
    let (n, S1, C1) := symEvalWindowTB bfTB 4000 S C
    windows := windows ++ [n]
    total := total + n
    S := S1; C := C1
    if let .next .stop := C then break
    let cross :=
      match C with
      | .next (.mapIterK _ _ _ _ _ base produced _ _ _) =>
          if produced.size == 3 && sortSeen == false && pickVar > 8 then
            (some (uCrossStop S C), "stop")
          else if pickVar == 5 || produced.size < 3 then
            (some (uCrossPick pickVar (if pickVar == 5 then .int else .uint64) S C), s!"pick x{pickVar} base={(repr base).pretty 40}")
          else (some (uCrossStop S C), "stop")
      | .retV _ (.stmtOpK (.sortSlice _) _ _ [] _ _) => (some (uCrossSort S C), "sort")
      | _ => (none, "?")
    match cross with
    | (some (S2, C2), tag) =>
        crossings := crossings ++ [tag]
        if tag.startsWith "pick" then pickVar := pickVar + 1
        if tag == "sort" then sortSeen := true
        total := total + 1
        S := S2; C := C2
        if let .panicked m := C2 then
          IO.println s!"CROSSING PANIC: {m}"; return
    | (none, tag) =>
        IO.println s!"STUCK after {total} (windows {windows}) wanted {tag}: {describeC C}"
        match stepFnSTB bfTB S C with
        | .error q => IO.println s!"  quit: {repr q}"
        | .ok _ => IO.println "  (steps?)"
        return
  IO.println s!"mirror total: {total}"
  IO.println s!"windows: {windows}"
  IO.println s!"crossings: {crossings}"
  if let .next .stop := C then
    -- γ-check: machine run at [3,1,0,0]; keys as in the Bf story:
    -- x₅=3, x₆=uKey1 1=2, x₇=uKey2 1 0=1, x₈=3
    let ρfin : Valuation :=
      { ints := fun i => [0, 7, 2, 0, 5, 3, 2, 1, 3].getD i 0
        bools := fun _ => false, vals := fun _ => .nil
        cells := fun _ => ⟨none, .nil⟩ }
    let σ0 := bcσ 7 2 5
    let mut ms := σ0
    let mut mc := bcCm
    let mut mch : Choices := [3, 1, 0, 0]
    for _ in [0:total] do
      match stepFn ms mc mch with
      | .ok (c', s', ch') => mc := c'; ms := s'; mch := ch'
      | .error _ => pure ()
    let img := γS ρfin σ0 S
    IO.println s!"γ-image heap == machine heap: {img.heap == ms.heap}"
    IO.println s!"nextAddr: γ {img.nextAddr} vs machine {ms.nextAddr}"
    IO.println s!"machine stop: {match mc with | .next .stop => true | _ => false}"
    if img.heap != ms.heap then
      for ((l1, c1), (l2, c2)) in img.heap.zip ms.heap do
        if l1 != l2 || c1 != c2 then
          IO.println s!"first diff at {(repr l1).pretty 40}"
          IO.println s!"  γ: {((repr c1).pretty 160).replace "\n" " "}"
          IO.println s!"  m: {((repr c2).pretty 160).replace "\n" " "}"
          break
    -- wrap depths on the final raft cell
    match GoLean.Sym.Heap.lookup S.heap (.base ⟨0⟩) with
    | some (.mk _ (.struct _ fs)) =>
        for (nm, v) in fs do
          if nm == "Term" || nm == "Vote" || nm == "lead" || nm == "state" then
            match v with
            | .int t _ => IO.println s!"{nm}: depth {intDepth t} head {((repr t).pretty 60).replace "\n" " " |>.take 90}"
            | _ => IO.println s!"{nm}: non-int"
    | _ => pure ()

#eval mainPhase1
#eval mainWalk
