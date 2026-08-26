import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.HhEquation
import GoLeanProofs.Specs.Raft.StaticCells

/-! # A4-U14 charter item 3: wave-3 OPENING — stepFollower /
stepCandidate dispatch censuses (PROBE-ONLY; the composition map is
the deliverable — which landed handler equations each arm consumes).
Fixtures: the born-re-sited Hh heap + a Message with a REAL Type cell
(Type→55; MessageType values: MsgProp 2, MsgApp 3, MsgHeartbeat 8).
Arms probed: stepFollower×{MsgHeartbeat, MsgProp} and
stepCandidate×MsgHeartbeat (the two-equation composition:
becomeFollower spine + handleHeartbeat). Static [16,31) reads
scanned per arm (the complement question). -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

/-- Message with a Type cell (55) and From cell (54); Commit 53. -/
def sdMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- The heap: uHeap(7,2,state,5) re-sited + msg cells + caller cells
(r-var 61 ↦ &raft, m-var 62 ↦ &msg, er 63). `typ` picks the arm;
`state` 0 for stepFollower runs, 1 (candidate) for stepCandidate. -/
def sdHeap (lead state : Int) (typ : Int) (withStatics : Bool) : GoCore.Heap :=
  ((uHeap 7 lead state 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), sdMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .int32), .int typ .int32⟩),
   (.base ⟨61⟩, ⟨some (.pointer (.defined ⟨"raft.raft"⟩)), .addr (.base ⟨31⟩)⟩),
   (.base ⟨62⟩, ⟨some (.pointer (.defined ⟨"raftpb.Message"⟩)), .addr (.base ⟨52⟩)⟩),
   (.base ⟨63⟩, ⟨some (.interface ⟨"error"⟩), .nil⟩)] ++
  (if withStatics then staticComplement else [])

def sdσ0 (lead state typ : Int) (ws : Bool) : ExecState :=
  { wBase with
      heap := sdHeap lead state typ ws
      nextAddr := (if ws then staticComplementNa else 64) }

def sdEnv : LocalEnv := [[("r", .base ⟨61⟩), ("m", .base ⟨62⟩), ("er", .base ⟨63⟩)]]

def sdC0 (fid : String) : Machine.Config :=
  .exec (.call #[.var "er"] ⟨fid⟩ #[Expr.var "r", Expr.var "m"]) sdEnv .stop

def bigStream : Choices := List.replicate 60 0

/-- One-pass walker: (steps, choices, na, pop indices, static-[16,31)
derefs, verdict). -/
partial def walkAll (n : Nat) (σ : ExecState) (c : Machine.Config)
    (ch : Choices) (pops : List Nat) (statics : List (Nat × Nat))
    (fuel : Nat) : (Nat × Nat × Nat × List Nat × List (Nat × Nat) × String) :=
  if fuel = 0 then (n, 60 - ch.length, σ.nextAddr, pops.reverse, statics.reverse, "OUT OF FUEL")
  else
    let statics' := match c with
      | .evalE (Expr.deref (Expr.locLit (.base b)) _) _ _ =>
          if 16 ≤ b.id && b.id < 31 then (n, b.id) :: statics else statics
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
        let maaStr : String := "msgsAfterAppend"
        let msgsStr : String := "msgs"
        let raftTid : GoLean.TypeId := ⟨"raft.raft"⟩
        let leadStr : String := "lead"
        let eeStr : String := "electionElapsed"
        let er := (Heap.lookup σ'.heap (.base ⟨63⟩)).map (·.value)
        IO.println s!"[{tag}] er={(toString (repr er)).take 140}"
        IO.println s!"[{tag}] msgs={(toString (repr (absOutbox σ' ⟨31⟩ msgsStr))).take 160}"
        IO.println s!"[{tag}] maa={(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 160}"
        IO.println s!"[{tag}] lead={toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨31⟩ raftTid leadStr))} state={toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨31⟩ raftTid "state"))} ee={toString (repr (GoLean.Lens.fieldReadU64 σ' ⟨31⟩ raftTid eeStr))}"
        IO.println s!"[{tag}] absRaftLog={(toString (repr (absRaftLog σ' ⟨32⟩))).take 200}"
    | .error e => IO.println s!"[{tag}] rerun ERROR {e.message.take 100}"

-- stepFollower × MsgHeartbeat (8): expect the Hh no-op span inside
#eval report "sF/Heartbeat" 2 0 8 false "raft.stepFollower"
-- stepFollower × MsgProp (2) with lead = 2 ≠ 0: the forward arm (send m to lead)
#eval report "sF/Prop-fwd" 2 0 2 false "raft.stepFollower"
-- stepFollower × MsgProp with lead = 0: the ErrProposalDropped drop (static 17)
#eval report "sF/Prop-drop" 0 0 2 false "raft.stepFollower"
-- same, WITH the static complement (the drop arm needs the error var)
#eval report "sF/Prop-drop+S" 0 0 2 true "raft.stepFollower"
-- stepCandidate × MsgHeartbeat at state 1: becomeFollower + handleHeartbeat
#eval report "sC/Heartbeat" 2 1 8 false "raft.stepCandidate"
-- stepCandidate × MsgApp at state 1 would need the Hae log cells; recorded, not run here
-- stepFollower × MsgForgetLeader (12? check numbering) — out of this census
