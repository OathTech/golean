import GoLeanProofs

/-! # A4-U4 slice 0: the state-literalization GENERATOR

Computes the becomeFollower chain's seven window-output states and
configs (uS1/3/5/7/9/11/13, uC1/3/5/7/9/11/13) from the landed
BfFixture chain (compiled evaluation) and prints them as Lean source
literals into `artifacts/probe/gen/BfLit.lean.gen`.

The printer is FAIL-CLOSED: any constructor this chain does not
exercise panics with its name rather than printing something wrong.
Concrete GoCore payloads (Stmt/Expr/Ty/Loc/envs/ops) go through the
machine's own derived `Repr`, verified round-trippable by
`ReprSmoke.lean` (fully-qualified names, structure-instance syntax
with known expected types). The generated literals' correctness is
NOT trusted from this probe: the reworked BfFixture's window LINK
theorems (`uW*_out`, kernel `rfl`) re-check every literal against the
evaluator — they are the drift alarms on any future fixture change. -/

open GoLean GoLean.GoCore GoLean.Sym GoLean.RaftSeam

namespace BfLitGen

def W : Nat := 120

/-- Concrete payload via derived Repr, always parenthesized. -/
def pr {α : Type} [Repr α] (x : α) : String :=
  "(" ++ (repr x).pretty W ++ ")"

def pList (items : List String) : String :=
  "[" ++ String.intercalate ",\n  " items ++ "]"

def pArr (items : List String) : String :=
  "#[" ++ String.intercalate ",\n  " items ++ "]"

mutual

partial def pV : SymValue → String
  | .unit => "(GoLean.Sym.Value.unit)"
  | .bool b => s!"(GoLean.Sym.Value.bool {pr b})"
  | .int v kind => s!"(GoLean.Sym.Value.int {pr v} {pr kind})"
  | .float bits kind => s!"(GoLean.Sym.Value.float {bits} {pr kind})"
  | .string s => s!"(GoLean.Sym.Value.string {pr s})"
  | .addr loc => s!"(GoLean.Sym.Value.addr {pr loc})"
  | .nil => "(GoLean.Sym.Value.nil)"
  | .interface dyn v => s!"(GoLean.Sym.Value.interface {pr dyn} {pV v})"
  | .struct tid fields =>
      s!"(GoLean.Sym.Value.struct {pr tid} " ++
        pArr (fields.toList.map (fun (n, v) => s!"({pr n}, {pV v})")) ++ ")"
  | .array vs => s!"(GoLean.Sym.Value.array " ++ pArr (vs.toList.map pV) ++ ")"
  | .slice v => s!"(GoLean.Sym.Value.slice {pr v})"
  | .map v => s!"(GoLean.Sym.Value.map {pr v})"
  | .mapData entries =>
      s!"(GoLean.Sym.Value.mapData " ++
        pArr (entries.toList.map (fun (k, v) => s!"({pV k}, {pV v})")) ++ ")"
  | .chan v => s!"(GoLean.Sym.Value.chan {pr v})"
  | .chanData buf cap closed =>
      s!"(GoLean.Sym.Value.chanData " ++ pArr (buf.toList.map pV) ++
        s!" {cap} {closed})"
  | .funcVal fid captured =>
      s!"(GoLean.Sym.Value.funcVal {pr fid} " ++
        pList (captured.map pV) ++ ")"
  | .syncData p => s!"(GoLean.Sym.Value.syncData {pr p})"
  | .atom a => s!"(GoLean.Sym.Value.atom ({a} : Nat))"

partial def pTR : GoLean.Sym.TargetRef symDom → String
  | .chain anchor idxs steps =>
      s!"(GoLean.Sym.TargetRef.chain {pV anchor} " ++
        pList (idxs.map pV) ++ s!" {pr steps})"
  | .mapElem base key kt vt =>
      s!"(GoLean.Sym.TargetRef.mapElem {pV base} {pV key} {pr kt} {pr vt})"

partial def pPE : GoLean.Sym.PanicEntry symDom → String
  | ⟨v, r⟩ => s!"(GoLean.Sym.PanicEntry.mk {pV v} {r})"

partial def pK : GoLean.Sym.Cont symDom → String
  | .stop => "(GoLean.Sym.Cont.stop)"
  | .seq rest env k => s!"(GoLean.Sym.Cont.seq {pr rest} {pr env} {pK k})"
  | .loop cond body env k =>
      s!"(GoLean.Sym.Cont.loop {pr cond} {pr body} {pr env} {pK k})"
  | .frame targets tenv results defers k wrapper =>
      s!"(GoLean.Sym.Cont.frame {pr targets} {pr tenv} {pr results} " ++
        pList (defers.map (fun (c, args) =>
          s!"({pV c}, {pList (args.map pV)})")) ++
        s!" {pK k} {wrapper})"
  | .deferCalleeK args env k =>
      s!"(GoLean.Sym.Cont.deferCalleeK {pr args} {pr env} {pK k})"
  | .deferArgsK callee vals pending env k =>
      s!"(GoLean.Sym.Cont.deferArgsK {pV callee} {pList (vals.map pV)} " ++
        s!"{pr pending} {pr env} {pK k})"
  | .breakableK k => s!"(GoLean.Sym.Cont.breakableK {pK k})"
  | .labelK label k => s!"(GoLean.Sym.Cont.labelK {pr label} {pK k})"
  | .callValCalleeK targets args env k =>
      s!"(GoLean.Sym.Cont.callValCalleeK {pr targets} {pr args} {pr env} {pK k})"
  | .callValArgsK callee targets vals pending env k =>
      s!"(GoLean.Sym.Cont.callValArgsK {pV callee} {pr targets} " ++
        s!"{pList (vals.map pV)} {pr pending} {pr env} {pK k})"
  | .strictK op done pending env k =>
      s!"(GoLean.Sym.Cont.strictK {pr op} {pList (done.map pV)} " ++
        s!"{pr pending} {pr env} {pK k})"
  | .andK right env k => s!"(GoLean.Sym.Cont.andK {pr right} {pr env} {pK k})"
  | .orK right env k => s!"(GoLean.Sym.Cont.orK {pr right} {pr env} {pK k})"
  | .boolK k => s!"(GoLean.Sym.Cont.boolK {pK k})"
  | .ifK t e env k => s!"(GoLean.Sym.Cont.ifK {pr t} {pr e} {pr env} {pK k})"
  | .whileK cond body env k =>
      s!"(GoLean.Sym.Cont.whileK {pr cond} {pr body} {pr env} {pK k})"
  | .callArgsK fid targets vals pending env k =>
      s!"(GoLean.Sym.Cont.callArgsK {pr fid} {pr targets} " ++
        s!"{pList (vals.map pV)} {pr pending} {pr env} {pK k})"
  | .stmtOpK op ntargets done pending env k =>
      s!"(GoLean.Sym.Cont.stmtOpK {pr op} {ntargets} " ++
        s!"{pList (done.map pV)} {pr pending} {pr env} {pK k})"
  | .mapRangeK kv vv kt vt body env k =>
      s!"(GoLean.Sym.Cont.mapRangeK {pr kv} {pr vv} {pr kt} {pr vt} " ++
        s!"{pr body} {pr env} {pK k})"
  | .mapIterK kv vv kt vt body base produced start env k =>
      s!"(GoLean.Sym.Cont.mapIterK {pr kv} {pr vv} {pr kt} {pr vt} " ++
        s!"{pr body} {pr base} {pArr (produced.toList.map pV)} " ++
        s!"{pArr (start.toList.map pV)} {pr env} {pK k})"
  | .panicArgK k => s!"(GoLean.Sym.Cont.panicArgK {pK k})"
  | .panicResumeK chain k =>
      s!"(GoLean.Sym.Cont.panicResumeK {pList (chain.map pPE)} {pK k})"
  | .storeK refs vals body env k =>
      s!"(GoLean.Sym.Cont.storeK {pList (refs.map pTR)} " ++
        s!"{pList (vals.map pV)} {pr body} {pr env} {pK k})"
  | .rhsK rop refs done pending body env k =>
      s!"(GoLean.Sym.Cont.rhsK {pr rop} {pList (refs.map pTR)} " ++
        s!"{pList (done.map pV)} {pr pending} {pr body} {pr env} {pK k})"
  | .tgtOpK sh ops pending refs targets rop rhs vals body env k =>
      s!"(GoLean.Sym.Cont.tgtOpK {pr sh} {pList (ops.map pV)} {pr pending} " ++
        s!"{pList (refs.map pTR)} {pr targets} {pr rop} {pr rhs} " ++
        s!"{pList (vals.map pV)} {pr body} {pr env} {pK k})"
  | .goCalleeK args env k =>
      s!"(GoLean.Sym.Cont.goCalleeK {pr args} {pr env} {pK k})"
  | .goArgsK callee vals pending env k =>
      s!"(GoLean.Sym.Cont.goArgsK {pV callee} {pList (vals.map pV)} " ++
        s!"{pr pending} {pr env} {pK k})"
  | .syncStK op done pending env k =>
      s!"(GoLean.Sym.Cont.syncStK {pr op} {pList (done.map pV)} " ++
        s!"{pr pending} {pr env} {pK k})"
  | .chanStK _ _ _ _ _ => panic! "pK: chanStK unexpected in this chain"
  | .selectOpsK _ _ _ _ _ _ => panic! "pK: selectOpsK unexpected in this chain"

end

def pCell : GoLean.Sym.HeapCell symDom → String
  | .mk dty v => s!"(GoLean.Sym.HeapCell.mk {pr dty} {pV v})"
  | .atom a => s!"(GoLean.Sym.HeapCell.atom ({a} : Nat))"

def pState (S : SymState) : String :=
  "(GoLean.Sym.State.mk\n  " ++
    pList (S.heap.map (fun (l, c) => s!"({pr l}, {pCell c})")) ++
    s!"\n  {S.nextAddr})"

def pC : SymConfig → String
  | .exec stmt env k => s!"(GoLean.Sym.Config.exec {pr stmt} {pr env} {pK k})"
  | .evalE e env k => s!"(GoLean.Sym.Config.evalE {pr e} {pr env} {pK k})"
  | .retV v k => s!"(GoLean.Sym.Config.retV {pV v} {pK k})"
  | .next k => s!"(GoLean.Sym.Config.next {pK k})"
  | .opDone sched inner => s!"(GoLean.Sym.Config.opDone {pr sched} {pC inner})"
  | _ => panic! "pC: unexpected config shape in this chain"

def emitDef (name ty body : String) : String :=
  s!"def {name} : {ty} :=\n  {body}\n\n"

end BfLitGen



/-! ## The handleHeartbeat COMMIT-ADVANCE chain (A4-U13 slot 2):
fixture = the bf31 heap with the TWO-ENTRY stable log at committed=1
(lastIndex 2 — advance headroom) + the heartbeat message with
m.Commit = 2. Windows [1655, 25]; one spill (msgs outbox; elems 150,
target 151, backing born at 152). -/

namespace HhAdvGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def hhaLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", uEmptySlice), ("offset", uU64 3),
      ("snapshotInProgress", .bool false), ("offsetInProgress", uU64 3),
      ("logger", .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩)))]),
    ("committed", uU64 1), ("applying", uU64 1), ("applied", uU64 1),
    ("logger", .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))),
    ("maxApplyingEntsSize", uU64 1048576),
    ("applyingEntsSize", uU64 0), ("applyingEntsPaused", .bool false)]

def hhaMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def hhaExtra : List (Loc × GoCore.HeapCell) :=
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), hhaMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), staleEntry2G⟩),
   (.base ⟨58⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def hhaSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (GoLean.RaftSeam.bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨32⟩ then (p.1, .mk (some (.defined ⟨"raft.raftLog"⟩)) (embedGo hhaLogVal))
    else if p.1 == .base ⟨37⟩ then (p.1, .mk (some (.defined ⟨"raft.MemoryStorage"⟩)) (embedGo staleMsValG))
    else if p.1 == .base ⟨46⟩ then
      (p.1, .mk (some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))))
        (embedGo (.array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)])))
    else p)) ++
  hhaExtra.map (fun (p : Loc × GoCore.HeapCell) =>
    (p.1, .mk p.2.declaredTy (embedGo p.2.value)))

def hhaS0 : SymState := { heap := hhaSymHeap, nextAddr := 60 }
def hhaC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def hhaHeapC : GoCore.Heap :=
  (((GoLean.RaftSeam.uHeap 7 2 0 5).map (fun (l, c) =>
    (Frame.renameLoc shBfc' l, ⟨c.declaredTy, Frame.renameValue shBfc' c.value⟩))).map
    (fun (p : Loc × GoCore.HeapCell) =>
      if p.1 == .base ⟨32⟩ then (p.1, ⟨p.2.declaredTy, hhaLogVal⟩)
      else if p.1 == .base ⟨37⟩ then (p.1, ⟨p.2.declaredTy, staleMsValG⟩)
      else if p.1 == .base ⟨46⟩ then
        (p.1, ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
             .array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)]⟩)
      else p)) ++ hhaExtra
def hhaσ0C : ExecState := { wBase with heap := hhaHeapC, nextAddr := 60 }
def hhaC0C : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def hhaCap (c : Nat) : Nat := GoLean.SliceMem.appendRealizedCap 0 1 (c % 32)
def hhaMsgPtr : Nat := 100  -- validated by the elems-cell check below
def hhaBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨hhaMsgPtr⟩)] ++ List.replicate (hhaCap c - 1) .nil⟩
def hhaρw (c : Nat) : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨152⟩), 0, 1, hhaCap c⟩ else .nil
    cells := fun i => if i = 0
      then ⟨some (.array (hhaCap c) (.pointer (.defined ⟨"raftpb.Message"⟩))),
            hhaBackingVal c⟩
      else ⟨none, .nil⟩ }

end HhAdvGen

open BfLitGen HhAdvGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.StaleEquation\n\n" ++
    "/-! # A4-U13 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The handleHeartbeat COMMIT-ADVANCE chain's window-output\n" ++
    "states/configs as SOURCE LITERALS, generated by\n" ++
    "`artifacts/probe/HhAdvGen.lean` (fixture: the two-entry stable log\n" ++
    "at committed = 1, m.Commit = 2; value/cell atoms 0 = the msgs\n" ++
    "response spill). Correctness: the window LINK theorems in\n" ++
    "`HhAdvEquation.lean` (kernel rfl) re-check every literal — the\n" ++
    "drift alarms; regenerate on any fixture change. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  let (n1, S1, C1) := symEvalWindowTB GoLean.RaftSeam.bfTB 8000 HhAdvGen.hhaS0 HhAdvGen.hhaC0
  IO.println s!"pre-window: {n1} steps (expect 1655)"
  if n1 != 1655 then IO.println "SCHEDULE DRIFT"; return
  out := out ++ BfLitGen.emitDef "hhaS1" "SymState" (BfLitGen.pState S1)
  out := out ++ BfLitGen.emitDef "hhaC1" "SymConfig" (BfLitGen.pC C1)
  let k1 := match C1 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  (match GoLean.Sym.Heap.lookup S1.heap (.base ⟨150⟩) with
   | some (.mk _ (.array vs)) =>
      IO.println s!"elems cell 150 element0 = {(vs.toList.map BfLitGen.pV).headD "NONE"} (expect addr {HhAdvGen.hhaMsgPtr})"
   | _ => IO.println "elems cell 150 odd")
  let S2 : SymState :=
    { heap := (GoLean.Sym.Heap.set S1.heap (.base ⟨151⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 0))) ++ [(.base ⟨152⟩, .atom 0)],
      nextAddr := 153 }
  let C2 : SymConfig := .next k1
  out := out ++ BfLitGen.emitDef "hhaS2" "SymState" (BfLitGen.pState S2)
  let (n2, S3, C3) := symEvalWindowTB GoLean.RaftSeam.bfTB 200 S2 C2
  IO.println s!"post-window: {n2} steps (expect 25); stop: {match C3 with | GoLean.Sym.Config.next .stop => true | _ => false}"
  out := out ++ BfLitGen.emitDef "hhaS3" "SymState" (BfLitGen.pState S3)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/HhAdvLit.lean.gen" out
  IO.println s!"total generated size: {out.length} chars"
  for c in [0, 3, 31] do
    match stepFnIter 1681 HhAdvGen.hhaσ0C HhAdvGen.hhaC0C (c :: List.replicate 40 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (HhAdvGen.hhaρw c) HhAdvGen.hhaσ0C S3
        IO.println s!"c={c}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"c={c}: ERROR {e.message.take 100}"
  let σ3 := γS (HhAdvGen.hhaρw 3) HhAdvGen.hhaσ0C S3
  let msgsStr : String := "msgs"
  IO.println s!"absOutbox(msgs) = {toString (repr (absOutbox σ3 ⟨31⟩ msgsStr))}"
  IO.println s!"absRaftLog post = {toString (repr (absRaftLog σ3 ⟨32⟩))}"
  IO.println s!"absRaftLog pre = {toString (repr (absRaftLog (γS (HhAdvGen.hhaρw 3) HhAdvGen.hhaσ0C HhAdvGen.hhaS0) ⟨32⟩))}"
  IO.println s!"absMessage(arg) = {(toString (repr (absMessage σ3 (.addr (.base ⟨52⟩))))).take 200}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σ3 ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
