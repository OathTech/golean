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



/-! ## The handleAppendEntries STALE-family chain (A4-U12 slice 1):
symbolic-from-birth fixture = the bf31 heap (vars 1-4 in the raft
cell) with the raftLog/MemoryStorage/ents cells REPLACED by the
two-entry log (committed = 2 = lastIndex, unstable offset 3) + the
Hae Message cells VERBATIM (prev.index = 1 < committed = 2 → STALE).
Pre-window to the spill quit (expect 1307), the atom-carried crossing
(value-atom 0 = the spilled handle at temp 135; cell-atom 0 = the
backing at 136), post-window to `.next .stop` (expect 28). -/

namespace StaleGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def ifaceHarness36 : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))

def staleLogVal : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", uEmptySlice), ("offset", uU64 3),
      ("snapshotInProgress", .bool false), ("offsetInProgress", uU64 3),
      ("logger", ifaceHarness36)]),
    ("committed", uU64 2), ("applying", uU64 2), ("applied", uU64 2),
    ("logger", ifaceHarness36), ("maxApplyingEntsSize", uU64 1048576),
    ("applyingEntsSize", uU64 0), ("applyingEntsPaused", .bool false)]

def staleMsVal : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨46⟩), offset := 0, len := 2, cap := 2 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", uI64 0), ("firstIndex", uI64 0), ("lastIndex", uI64 0),
      ("entries", uI64 0), ("term", uI64 0), ("snapshot", uI64 0)])]

def staleMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)), ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def staleEntry2 : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨58⟩)), ("Index", .addr (.base ⟨59⟩)),
    ("Type", .nil), ("Data", uEmptySlice)]

def staleExtra : List (Loc × GoCore.HeapCell) :=
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), staleMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨56⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), staleEntry2⟩),
   (.base ⟨58⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

/-- The SYM fixture: bf31SymHeap (vars 1-4) with cells 32/37/46
replaced, + the message/entry cells. -/
def staleSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (GoLean.RaftSeam.bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨32⟩ then (p.1, .mk (some (.defined ⟨"raft.raftLog"⟩)) (embedGo staleLogVal))
    else if p.1 == .base ⟨37⟩ then (p.1, .mk (some (.defined ⟨"raft.MemoryStorage"⟩)) (embedGo staleMsVal))
    else if p.1 == .base ⟨46⟩ then
      (p.1, .mk (some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))))
        (embedGo (.array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)])))
    else p)) ++
  staleExtra.map (fun (p : Loc × GoCore.HeapCell) =>
    (p.1, .mk p.2.declaredTy (embedGo p.2.value)))

def staleS0 : SymState := { heap := staleSymHeap, nextAddr := 60 }

def staleC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

-- witness-shaped machine fixture (Vote 7 lead 2 state 0 ldT 5)
def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31
def staleHeapC : GoCore.Heap :=
  (((GoLean.RaftSeam.uHeap 7 2 0 5).map (fun (l, c) =>
    (Frame.renameLoc shBfc' l, ⟨c.declaredTy, Frame.renameValue shBfc' c.value⟩))).map
    (fun (p : Loc × GoCore.HeapCell) =>
      if p.1 == .base ⟨32⟩ then (p.1, ⟨p.2.declaredTy, staleLogVal⟩)
      else if p.1 == .base ⟨37⟩ then (p.1, ⟨p.2.declaredTy, staleMsVal⟩)
      else if p.1 == .base ⟨46⟩ then
        (p.1, ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
             .array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)]⟩)
      else p)) ++ staleExtra
def staleσ0C : ExecState := { wBase with heap := staleHeapC, nextAddr := 60 }
def staleC0C : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def staleCap (c : Nat) : Nat := GoLean.SliceMem.appendRealizedCap 0 1 (c % 32)
def staleMsgPtr : Nat := 93  -- validated by the elems-cell check below
def staleBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨staleMsgPtr⟩)] ++ List.replicate (staleCap c - 1) .nil⟩
def staleρw (c : Nat) : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5, 2].getD i 0
    bools := fun _ => false
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨136⟩), 0, 1, staleCap c⟩ else .nil
    cells := fun i => if i = 0
      then ⟨some (.array (staleCap c) (.pointer (.defined ⟨"raftpb.Message"⟩))),
            staleBackingVal c⟩
      else ⟨none, .nil⟩ }

end StaleGen

open BfLitGen StaleGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.Bf31\n\n" ++
    "/-! # A4-U12 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The handleAppendEntries STALE-family chain's window-output\n" ++
    "states/configs as SOURCE LITERALS, generated by\n" ++
    "`artifacts/probe/StaleGen.lean` (fixture: the bf31 heap with the\n" ++
    "two-entry log — committed = 2 = lastIndex — + the Hae Message\n" ++
    "cells; value-atom 0 = the spilled handle, cell-atom 0 = the\n" ++
    "backing — the valuation absorbs the spill choice). Correctness:\n" ++
    "the window LINK theorems in `StaleEquation.lean` (kernel rfl)\n" ++
    "re-check every literal — the drift alarms; regenerate here on any\n" ++
    "fixture change. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  -- pre-window
  let (n1, S1, C1) := symEvalWindowTB GoLean.RaftSeam.bfTB 4000 StaleGen.staleS0 StaleGen.staleC0
  IO.println s!"pre-window: {n1} steps (expect 1307)"
  if n1 != 1307 then
    IO.println "SCHEDULE DRIFT — diagnosing"
    (match stepFnSTB GoLean.RaftSeam.bfTB S1 C1 with
     | .ok _ => IO.println "quit-step: OK?!"
     | .error q => IO.println s!"quit: {toString (repr q)}")
    return
  out := out ++ BfLitGen.emitDef "staleS1" "SymState" (BfLitGen.pState S1)
  out := out ++ BfLitGen.emitDef "staleC1" "SymConfig" (BfLitGen.pC C1)
  IO.println s!"printed staleS1/staleC1: heap {S1.heap.length} cells"
  let k1 := match C1 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  -- validate the elems backing element = the response-message pointer
  (match GoLean.Sym.Heap.lookup S1.heap (.base ⟨134⟩) with
   | some (.mk _ (.array vs)) =>
      let e0 : String := (vs.toList.map BfLitGen.pV).headD "NONE"
      IO.println s!"elems cell 134 element0 = {e0} (expect addr staleMsgPtr={StaleGen.staleMsgPtr})"
   | _ => IO.println "elems cell 134 MISSING/odd")
  (match C1 with
   | .retV v (.stmtOpK _ nt done _ _ _) =>
      IO.println s!"spill operands: v={BfLitGen.pV v} done={(done.map BfLitGen.pV)} nt={nt}"
   | _ => IO.println "quit config odd")
  let S2 : SymState :=
    { heap := (GoLean.Sym.Heap.set S1.heap (.base ⟨135⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 0))) ++ [(.base ⟨136⟩, .atom 0)],
      nextAddr := 137 }
  let C2 : SymConfig := .next k1
  out := out ++ BfLitGen.emitDef "staleS2" "SymState" (BfLitGen.pState S2)
  -- post-window
  let (n2, S3, C3) := symEvalWindowTB GoLean.RaftSeam.bfTB 200 S2 C2
  IO.println s!"post-window: {n2} steps (expect 28)"
  let stop3 := match C3 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"post-window ends at stop: {stop3}"
  out := out ++ BfLitGen.emitDef "staleS3" "SymState" (BfLitGen.pState S3)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/StaleLit.lean.gen" out
  IO.println s!"total generated size: {out.length} chars"
  -- MACHINE VALIDATION at three stream heads (witness valuation)
  for c in [0, 3, 31] do
    match stepFnIter 1336 StaleGen.staleσ0C StaleGen.staleC0C (c :: List.replicate 40 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (StaleGen.staleρw c) StaleGen.staleσ0C S3
        IO.println s!"c={c}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"c={c}: machine ERROR {e.message}"
  -- γ-agreement at the PRE-window quit too (S1 against machine @1307)
  match stepFnIter 1307 StaleGen.staleσ0C StaleGen.staleC0C (List.replicate 40 0) with
  | .ok (cM, σM, _) =>
      let σγ := γS (StaleGen.staleρw 0) StaleGen.staleσ0C S1
      let cγ := γC (StaleGen.staleρw 0) C1
      let cfgEq := match cγ, cM with
        | Machine.Config.retV v1 _, Machine.Config.retV v2 _ => v1 == v2
        | _, _ => false
      IO.println s!"pre-quit: γ-heap=={σγ.heap == σM.heap} γ-na=={σγ.nextAddr == σM.nextAddr} retV=={cfgEq}"
  | .error e => IO.println s!"pre-quit ERROR {e.message}"
  -- projections at γ(S3)
  let σ3 := γS (StaleGen.staleρw 3) StaleGen.staleσ0C S3
  let msgsStr : String := "msgs"
  let raftTid : GoLean.TypeId := ⟨"raft.raft"⟩
  let voteStr : String := "Vote"
  let maaStr : String := "msgsAfterAppend"
  let ob := absOutbox σ3 ⟨31⟩ maaStr
  let obMsgs := absOutbox σ3 ⟨31⟩ msgsStr
  let alog := absRaftLog σ3 ⟨32⟩
  let alogPre := absRaftLog (γS (StaleGen.staleρw 3) StaleGen.staleσ0C StaleGen.staleS0) ⟨32⟩
  let vt := GoLean.Lens.fieldReadU64 σ3 ⟨31⟩ raftTid voteStr
  let am := absMessage σ3 (.addr (.base ⟨52⟩))
  IO.println s!"absOutbox(msgsAfterAppend) = {toString (repr ob)}"
  IO.println s!"absOutbox(msgs) = {toString (repr obMsgs)}"
  IO.println s!"absRaftLog post = {toString (repr alog)}"
  IO.println s!"absRaftLog pre(γ S0) = {toString (repr alogPre)}"
  IO.println s!"VoteRead = {toString (repr vt)}"
  IO.println s!"absMessage(arg) = {toString (repr am)}"
