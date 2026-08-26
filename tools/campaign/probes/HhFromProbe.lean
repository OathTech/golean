import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.HhEquation

/-! # A4-U14 charter item 2 probe: the From-SYMBOLIC handleHeartbeat
chain. The Hh no-op fixture with cell 54 (m.From's deref cell) made
SYMBOLIC (var 5). U10's finding: the pre-window quits `.q1Branch` at
`send`'s self-addressed panic guard (step 1259 recorded). Questions:
(a) the exact quit shape (the SymBool term + the ifK arms), (b) the
window schedule after the branch crossing (expect [1259, ~39, 25]
with the spill between), (c) end-to-end γ==machine at a concrete
From ≠ 1 valuation, (d) where var 5 lands in the post state (the
response To cell — wrap depth). -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

/-- The Hh sym fixture with cell 54 symbolic. -/
def hfS0 : SymState :=
  { heap := hhS0.heap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
      if p.1 == .base ⟨54⟩ then
        (p.1, .mk (some (.int .uint64)) (.int (.var 5) .uint64))
      else p),
    nextAddr := 55 }

def hfC0 : SymConfig := hhC0

-- window 1: to the branch quit
def w1 := symEvalWindowTB bfTB 3000 hfS0 hfC0
#eval s!"window 1: {w1.1} steps"
#eval match stepFnSTB bfTB w1.2.1 w1.2.2 with
  | .ok _ => "w1 end: steps on"
  | .error q => s!"w1 quit: {toString (repr q)}"
-- the quit config: expect retV (.bool sym) (.ifK t e env k)
#eval match w1.2.2 with
  | .retV (GoLean.Sym.Value.bool sb) (.ifK t e _ _) =>
      s!"BRANCH QUIT: cond = {toString (repr sb)}\n  then-head = {(toString (repr t)).take 300}\n  else-head = {(toString (repr e)).take 300}"
  | _ => "UNEXPECTED quit config shape"

-- cross the branch (From=x₅, ρ.ints 5 = 2 ≠ 1 → which arm? print both γ)
def hfρ : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5, 2].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

#eval match w1.2.2 with
  | .retV (GoLean.Sym.Value.bool sb) _ =>
      s!"γB at ints5=2: {γB hfρ sb}  |  at ints5=1: {γB { hfρ with ints := fun i => [0,7,2,0,5,1].getD i 0 } sb}"
  | _ => "?"

-- continue: take the γ-selected arm (expect false → else) and walk on
def afterBranch : SymConfig := match w1.2.2 with
  | .retV (GoLean.Sym.Value.bool _) (.ifK t e env k) =>
      -- γB = false at ints5=2 (checked above) → else arm
      .exec e env k
  | _ => .next .stop

def w2 := symEvalWindowTB bfTB 3000 w1.2.1 afterBranch
#eval s!"window 2: {w2.1} steps"
#eval match stepFnSTB bfTB w2.2.1 w2.2.2 with
  | .ok _ => "w2 end: steps on"
  | .error q => s!"w2 quit: {toString (repr q)}"
#eval match w2.2.2 with
  | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK op _ done _ _ _) =>
      let doneStr := String.intercalate "; " (done.map (fun v => match v with
        | GoLean.Sym.Value.slice s2 => s!"slice base={toString (repr s2.base)} len={s2.len}"
        | GoLean.Sym.Value.addr l => s!"addr {toString (repr l)}"
        | _ => "other"))
      s!"w2 quit: op={(toString (repr op)).take 60} elems={(toString (repr sv.base)).take 40} done=[{doneStr}] na={w2.2.1.nextAddr}"
  | _ => "w2 quit config shape odd"

-- the spill crossing (Hh pattern: atom 0), then post-window
def hfS2 : SymState := match w2.2.2 with
  | .retV _ (.stmtOpK _ _ done _ _ _) =>
      (match done with
       | [_, GoLean.Sym.Value.addr (.base tgt)] =>
          { heap := (GoLean.Sym.Heap.set w2.2.1.heap (.base tgt)
              (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
                (.atom 0))) ++ [(.base ⟨w2.2.1.nextAddr⟩, .atom 0)],
            nextAddr := w2.2.1.nextAddr + 1 }
       | _ => w2.2.1)
  | _ => w2.2.1
def hfK2 : GoLean.Sym.Cont symDom := match w2.2.2 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop

def w3 := symEvalWindowTB bfTB 300 hfS2 (.next hfK2)
#eval s!"window 3: {w3.1} steps; stop = {match w3.2.2 with | GoLean.Sym.Config.next .stop => true | _ => false}"

-- MACHINE validation: concrete heap with From cell = 2, full run
def hfρ' (c : Nat) : Valuation :=
  { hfρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c⟩ else .nil
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) hhElemTy), hhBackingVal c⟩
      else ⟨none, .nil⟩ }

def nTot := w1.1 + 1 + w2.1 + 1 + w3.1
#eval s!"total mirror span = {w1.1} + 1 + {w2.1} + 1 + {w3.1} = {nTot} (Hh concrete was 1325)"

#eval show IO Unit from do
  for c in [0, 3, 31] do
    let σ0 := γS (hfρ' c) wBase hfS0
    match stepFnIter nTot σ0 (γC (hfρ' c) hfC0) (c :: List.replicate 20 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (hfρ' c) wBase w3.2.1
        IO.println s!"c={c}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"c={c}: machine ERROR {e.message.take 120}"

-- the To deref chain: resp msg cell 74 -> To field addr -> that cell's SymInt
#eval show IO Unit from do
  match GoLean.Sym.Heap.lookup w3.2.1.heap (.base ⟨74⟩) with
  | some (GoLean.Sym.HeapCell.mk _ (GoLean.Sym.Value.struct _ fs)) =>
      for (n, v) in fs do
        if true then
          match v with
          | GoLean.Sym.Value.addr (.base t) =>
              (match GoLean.Sym.Heap.lookup w3.2.1.heap (.base t) with
               | some (GoLean.Sym.HeapCell.mk _ (GoLean.Sym.Value.int si _)) =>
                  IO.println s!"{n} -> cell {t.id} : {toString (repr si)}"
               | _ => IO.println s!"{n} -> cell {t.id} : non-int/missing")
          | GoLean.Sym.Value.nil => IO.println s!"{n} = nil"
          | _ => IO.println s!"{n} = other shape"
  | _ => IO.println "cell 74 not a struct"
  let σ3 := γS (hfρ' 3) wBase w3.2.1
  let msgsStr : String := "msgs"
  IO.println s!"absOutbox(msgs) = {(toString (repr (absOutbox σ3 ⟨31⟩ msgsStr))).take 260}"
