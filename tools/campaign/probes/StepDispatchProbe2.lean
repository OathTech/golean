import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.HhEquation
import GoLeanProofs.Specs.Raft.StaticCellsExt

/-! # A4-U15 slice-1 validation: re-census of the stepFollower×MsgProp
DROP arm with the dispatch-complement EXTENSION (cells 16/17 + payloads
61/65). U14's census stuck at step 235 on `unbound heap location:
base 17`. Placement fix per the extension's consumer rule: caller
cells move 61/62/63 → 66/67/68 (61 is now the ErrStopped payload).
Also re-runs the two heartbeat arms + fwd arm at the NEW caller
placement to re-pin their counts at this fixture geometry. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def sdMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- Heap: re-sited uHeap + msg cells (52-55) + caller cells at
[66,69) (OFF the 61/65 payloads) + optionally the FULL static block. -/
def sdHeap (lead state : Int) (typ : Int) (withStatics : Bool) : GoCore.Heap :=
  ((uHeap 7 lead state 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), sdMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .int32), .int typ .int32⟩),
   (.base ⟨66⟩, ⟨some (.pointer (.defined ⟨"raft.raft"⟩)), .addr (.base ⟨31⟩)⟩),
   (.base ⟨67⟩, ⟨some (.pointer (.defined ⟨"raftpb.Message"⟩)), .addr (.base ⟨52⟩)⟩),
   (.base ⟨68⟩, ⟨some (.interface ⟨"error"⟩), .nil⟩)] ++
  (if withStatics then staticComplementFull else [])

def sdσ0 (lead state typ : Int) (ws : Bool) : ExecState :=
  { wBase with
      heap := sdHeap lead state typ ws
      nextAddr := (if ws then staticComplementNa else 69) }

def sdEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

def sdC0 (fid : String) : Machine.Config :=
  .exec (.call #[.var "er"] ⟨fid⟩ #[Expr.var "r", Expr.var "m"]) sdEnv .stop

def bigStream : Choices := List.replicate 60 0

/-- One-pass walker: (steps, choices, na, pop indices, static-[0,31)
derefs, verdict). Static scan widened to the whole [0,31) block. -/
partial def walkAll (n : Nat) (σ : ExecState) (c : Machine.Config)
    (ch : Choices) (pops : List Nat) (statics : List (Nat × Nat))
    (fuel : Nat) : (Nat × Nat × Nat × List Nat × List (Nat × Nat) × String) :=
  if fuel = 0 then (n, 60 - ch.length, σ.nextAddr, pops.reverse, statics.reverse, "OUT OF FUEL")
  else
    let statics' := match c with
      | .evalE (Expr.deref (Expr.locLit (.base b)) _) _ _ =>
          if b.id < 31 then (n, b.id) :: statics else statics
      | _ => statics
    match stepFn σ c ch with
    | .ok (Machine.Config.next .stop, σ2, ch2) =>
        (n+1, 60 - ch2.length, σ2.nextAddr, pops.reverse, statics'.reverse, "STOP")
    | .ok (c2, σ2, ch2) =>
        let pops' := if ch2.length < ch.length then n :: pops else pops
        walkAll (n+1) σ2 c2 ch2 pops' statics' (fuel - 1)
    | .error e => (n+1, 60 - ch.length, σ.nextAddr, pops.reverse, statics'.reverse,
        s!"ERROR {e.status}: {e.message.take 140}")

def report (tag : String) (lead state typ : Int) (ws : Bool) (fid : String) : IO Unit := do
  let σ0 := sdσ0 lead state typ ws
  let (n, ch, na, pops, statics, verdict) := walkAll 0 σ0 (sdC0 fid) bigStream [] [] 20000
  IO.println s!"[{tag}] steps={n} choices={ch} na={na} verdict={verdict}"
  IO.println s!"[{tag}] pops={toString (repr pops)} statics={toString (repr statics)}"
  if verdict == "STOP" then
    match stepFnIter n σ0 (sdC0 fid) bigStream with
    | .ok (_, σ', _) =>
        let er := (Heap.lookup σ'.heap (.base ⟨68⟩)).map (·.value)
        IO.println s!"[{tag}] er={(toString (repr er)).take 240}"
        IO.println s!"[{tag}] msgs={(toString (repr (absOutbox σ' ⟨31⟩ "msgs"))).take 160}"
        IO.println s!"[{tag}] maa={(toString (repr (absOutbox σ' ⟨31⟩ "msgsAfterAppend"))).take 160}"
        IO.println s!"[{tag}] lead={toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨31⟩ ⟨"raft.raft"⟩ "lead"))} state={toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨31⟩ ⟨"raft.raft"⟩ "state"))} ee={toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨31⟩ ⟨"raft.raft"⟩ "electionElapsed"))}"
        IO.println s!"[{tag}] absRaftLog={(toString (repr (absRaftLog σ' ⟨32⟩))).take 200}"
    | .error e => IO.println s!"[{tag}] rerun ERROR {e.message.take 100}"

-- THE VALIDATION: the drop arm (lead = 0) with the FULL block — the
-- U14 stuck at cell 17 must clear; expect er = ErrProposalDropped.
#eval report "sF/Prop-drop+FULL" 0 0 2 true "raft.stepFollower"
-- Control: drop arm with statics ABSENT — must still stick at 17.
#eval report "sF/Prop-drop-none" 0 0 2 false "raft.stepFollower"
-- Re-pins at the new caller placement (counts should match U14's):
#eval report "sF/Heartbeat" 2 0 8 false "raft.stepFollower"
#eval report "sF/Prop-fwd" 2 0 2 false "raft.stepFollower"
#eval report "sC/Heartbeat" 2 1 8 false "raft.stepCandidate"
