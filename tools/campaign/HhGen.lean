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


/-! ## The handleHeartbeat chain (A4-U10): symbolic-from-birth fixture
= the bf31 heap (vars 1-4 in the raft cell) + the Message argument
cells (Commit deref cell 53 CONCRETE 1 — the no-op commitTo family
precondition; From deref cell 54 SYMBOLIC var 5). Pre-window to the
spill quit (expect 1299), the atom-carried crossing (value-atom 0 =
the spilled handle at temp 125; cell-atom 0 = the backing at 126),
post-window to `.next .stop` (expect 25). -/

namespace HhGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def hhMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def hhS0 : SymState :=
  { heap := GoLean.RaftSeam.bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) hhMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64))],
    nextAddr := 55 }

def hhC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

-- witness-shaped machine fixture (the U9 recipe: Vote 7 lead 2 state 0 ldT 5, From 2)
def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31
def hhMsgValC : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]
def hhHeapC : GoCore.Heap :=
  ((GoLean.RaftSeam.uHeap 7 2 0 5).map (fun (l, c) =>
    (Frame.renameLoc shBfc' l, ⟨c.declaredTy, Frame.renameValue shBfc' c.value⟩))) ++
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), hhMsgValC⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]
def hhσ0C : ExecState := { wBase with heap := hhHeapC, nextAddr := 55 }
def hhC0C : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def hhCap (c : Nat) : Nat := GoLean.SliceMem.appendRealizedCap 0 1 (c % 32)
def hhBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨74⟩)] ++ List.replicate (hhCap c - 1) .nil⟩
def hhρw (c : Nat) : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5, 2].getD i 0
    bools := fun _ => false
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c⟩ else .nil
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) (.pointer (.defined ⟨"raftpb.Message"⟩))),
            hhBackingVal c⟩
      else ⟨none, .nil⟩ }

end HhGen

open BfLitGen HhGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.Bf31\n\n" ++
    "/-! # A4-U10 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The handleHeartbeat chain's window-output states/configs as\n" ++
    "SOURCE LITERALS, generated by `artifacts/probe/HhGen.lean`\n" ++
    "(fixture: the bf31 heap + Message argument cells; value-atom 0 =\n" ++
    "the spilled handle, cell-atom 0 = the backing — the valuation\n" ++
    "absorbs the spill choice). Correctness: the window LINK theorems\n" ++
    "in `HhEquation.lean` (kernel rfl) re-check every literal — the\n" ++
    "drift alarms; regenerate here on any fixture change. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  -- pre-window
  let (n1, S1, C1) := symEvalWindowTB GoLean.RaftSeam.bfTB 2000 HhGen.hhS0 HhGen.hhC0
  IO.println s!"pre-window: {n1} steps (expect 1299)"
  if n1 != 1299 then
    IO.println "SCHEDULE DRIFT — diagnosing"
    (match stepFnSTB GoLean.RaftSeam.bfTB S1 C1 with
     | .ok _ => IO.println "quit-step: OK?!"
     | .error q => IO.println s!"quit: {toString (repr q)}")
    (match C1 with
     | .exec st _ k =>
        IO.println s!"quit config exec: {((toString (repr st)).take 300)}"
     | .evalE e _ _ =>
        IO.println s!"quit config evalE: {((toString (repr e)).take 300)}"
     | .retV v k =>
        IO.println s!"quit config retV FULL: {((BfLitGen.pV v).take 800)}"
     | .next _ => IO.println "quit config next"
     | _ => IO.println "quit config other")
    return
  out := out ++ BfLitGen.emitDef "hhS1" "SymState" (BfLitGen.pState S1)
  out := out ++ BfLitGen.emitDef "hhC1" "SymConfig" (BfLitGen.pC C1)
  IO.println s!"printed hhS1/hhC1: heap {S1.heap.length} cells"
  -- the crossing (atom-carried)
  let k1 := match C1 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let S2 : SymState :=
    { heap := (GoLean.Sym.Heap.set S1.heap (.base ⟨125⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 0))) ++ [(.base ⟨126⟩, .atom 0)],
      nextAddr := 127 }
  let C2 : SymConfig := .next k1
  out := out ++ BfLitGen.emitDef "hhS2" "SymState" (BfLitGen.pState S2)
  -- post-window
  let (n2, S3, C3) := symEvalWindowTB GoLean.RaftSeam.bfTB 100 S2 C2
  IO.println s!"post-window: {n2} steps (expect 25)"
  let stop3 := match C3 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"post-window ends at stop: {stop3}"
  out := out ++ BfLitGen.emitDef "hhS3" "SymState" (BfLitGen.pState S3)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/HhLit.lean.gen" out
  IO.println s!"total generated size: {out.length} chars"
  -- MACHINE VALIDATION at three stream heads (witness valuation)
  for c in [0, 3, 31] do
    match stepFnIter 1325 HhGen.hhσ0C HhGen.hhC0C (c :: List.replicate 40 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (HhGen.hhρw c) HhGen.hhσ0C S3
        IO.println s!"c={c}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"c={c}: machine ERROR {e.message}"
  -- γ-agreement at the PRE-window quit too (S1 against machine @1299)
  match stepFnIter 1299 HhGen.hhσ0C HhGen.hhC0C (List.replicate 40 0) with
  | .ok (cM, σM, _) =>
      let σγ := γS (HhGen.hhρw 0) HhGen.hhσ0C S1
      let cγ := γC (HhGen.hhρw 0) C1
      let cfgEq := match cγ, cM with
        | Machine.Config.retV v1 _, Machine.Config.retV v2 _ => v1 == v2
        | _, _ => false
      IO.println s!"pre-quit: γ-heap=={σγ.heap == σM.heap} γ-na=={σγ.nextAddr == σM.nextAddr} retV=={cfgEq}"
  | .error e => IO.println s!"pre-quit ERROR {e.message}"
  -- projections at γ(S3)
  let σ3 := γS (HhGen.hhρw 3) HhGen.hhσ0C S3
  let msgsStr : String := "msgs"
  let raftTid : GoLean.TypeId := ⟨"raft.raft"⟩
  let voteStr : String := "Vote"
  let ob := absOutbox σ3 ⟨31⟩ msgsStr
  let cm := (absRaftLog σ3 ⟨32⟩).map AbsLog.committed
  let vt := GoLean.Lens.fieldReadU64 σ3 ⟨31⟩ raftTid voteStr
  let am := absMessage σ3 (.addr (.base ⟨52⟩))
  IO.println s!"absOutbox = {toString (repr ob)}"
  IO.println s!"committed = {toString (repr cm)}"
  IO.println s!"VoteRead = {toString (repr vt)}"
  IO.println s!"absMessage(arg) = {toString (repr am)}"
