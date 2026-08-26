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



/-! ## The handleAppendEntries LOG-APPEND-family chain (A4-U12
slice 3): symbolic-from-birth fixture = the bf31 heap (vars 1-4) +
the la message cells (ONE entry (index 2, term 1) after matching
prev) + THE STATIC-CELL COMPLEMENT at its true addresses, na₀ = 98.
THREE windows / TWO spill crossings (probe LaProbe3: 4,828 steps,
choices at 3573 = the unstable.entries append and 4798 = the
msgsAfterAppend response append). -/

namespace LaGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def laMsgVal : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)),
    ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := some (.base ⟨57⟩), offset := 0, len := 1, cap := 1 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def laEntry1 : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨59⟩)), ("Index", .addr (.base ⟨60⟩)),
    ("Type", .nil), ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def laExtra : List (Loc × GoCore.HeapCell) :=
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), laMsgVal⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨56⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
      .array #[.addr (.base ⟨58⟩)]⟩),
   (.base ⟨58⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), laEntry1⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨60⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def laSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  GoLean.RaftSeam.bf31SymHeap ++
  laExtra.map (fun (p : Loc × GoCore.HeapCell) =>
    (p.1, .mk p.2.declaredTy (embedGo p.2.value))) ++
  GoLean.RaftSeam.staticComplementSym

def laS0 : SymState := { heap := laSymHeap, nextAddr := staticComplementNa }

def laC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

-- concrete machine fixture (Vote 7 lead 2 state 0 ldT 5)
def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31
def laHeapC : GoCore.Heap :=
  ((GoLean.RaftSeam.uHeap 7 2 0 5).map (fun (l, c) =>
    (Frame.renameLoc shBfc' l, ⟨c.declaredTy, Frame.renameValue shBfc' c.value⟩))) ++
  laExtra ++ GoLean.RaftSeam.staticComplement
def laσ0C : ExecState := { wBase with heap := laHeapC, nextAddr := staticComplementNa }
def laC0C : Machine.Config :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def laCap (c : Nat) : Nat := GoLean.SliceMem.appendRealizedCap 0 1 (c % 32)

end LaGen

def laρw (c1 c2 b2 respMsg : Nat) : GoLean.Sym.Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun i =>
      if i = 0 then .slice ⟨some (.base ⟨324⟩), 0, 1, LaGen.laCap c1⟩
      else if i = 1 then .slice ⟨some (.base ⟨b2⟩), 0, 1, LaGen.laCap c2⟩
      else .nil
    cells := fun i =>
      if i = 0 then ⟨some (.array (LaGen.laCap c1) (.pointer (.defined ⟨"raftpb.Entry"⟩))),
        .array ⟨[.addr (.base ⟨58⟩)] ++ List.replicate (LaGen.laCap c1 - 1) .nil⟩⟩
      else if i = 1 then ⟨some (.array (LaGen.laCap c2) (.pointer (.defined ⟨"raftpb.Message"⟩))),
        .array ⟨[.addr (.base ⟨respMsg⟩)] ++ List.replicate (LaGen.laCap c2 - 1) .nil⟩⟩
      else ⟨none, .nil⟩ }

open BfLitGen LaGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.Bf31\nimport GoLeanProofs.Specs.Raft.StaticCells\n\n" ++
    "/-! # A4-U12 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The handleAppendEntries LOG-APPEND-family chain's window-output\n" ++
    "states/configs as SOURCE LITERALS, generated by\n" ++
    "`artifacts/probe/LaGen.lean` (fixture: the bf31 heap + the\n" ++
    "one-entry message + THE STATIC-CELL COMPLEMENT, na₀ = 98;\n" ++
    "value/cell atoms 0 = the unstable.entries append spill, atoms 1 =\n" ++
    "the msgsAfterAppend response spill; the ONE in-window atom read\n" ++
    "(len(u.entries), choice-independent result 1) is a hand crossing\n" ++
    "over landed kit lemmas). Correctness: the window LINK theorems in\n" ++
    "`LaEquation.lean` (kernel rfl) re-check every literal — the drift\n" ++
    "alarms; regenerate here on any fixture change. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  -- WINDOW 1 (to the entries-append spill)
  let (n1, S1, C1) := symEvalWindowTB GoLean.RaftSeam.bfTB 20000 LaGen.laS0 LaGen.laC0
  IO.println s!"w1: {n1} steps (expect 3573); na={S1.nextAddr} (expect 324)"
  if n1 != 3573 then IO.println "SCHEDULE DRIFT w1"; return
  out := out ++ BfLitGen.emitDef "laS1" "SymState" (BfLitGen.pState S1)
  out := out ++ BfLitGen.emitDef "laC1" "SymConfig" (BfLitGen.pC C1)
  let k1 := match C1 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  -- CROSSING 1: target temp 323, backing born at 324 (atoms 0)
  let S2 : SymState :=
    { heap := (GoLean.Sym.Heap.set S1.heap (.base ⟨323⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))))
          (.atom 0))) ++ [(.base ⟨324⟩, .atom 0)],
      nextAddr := 325 }
  out := out ++ BfLitGen.emitDef "laS2" "SymState" (BfLitGen.pState S2)
  -- WINDOW 2a (to the lengthOf(atom) read)
  let (n2a, S2a, C2a) := symEvalWindowTB GoLean.RaftSeam.bfTB 20000 S2 (.next k1)
  IO.println s!"w2a: {n2a} steps (expect 83); na={S2a.nextAddr}"
  out := out ++ BfLitGen.emitDef "laS2a" "SymState" (BfLitGen.pState S2a)
  out := out ++ BfLitGen.emitDef "laC2a" "SymConfig" (BfLitGen.pC C2a)
  let kLen := match C2a with
    | .retV _ (.strictK _ _ _ _ k') => k'
    | _ => .stop
  -- LENGTH CROSSING: state unchanged, config → retV (int 1) kLen
  -- WINDOW 2b (to the msgsAfterAppend spill)
  let (n2b, S3, C3) := symEvalWindowTB GoLean.RaftSeam.bfTB 20000 S2a
    (.retV (.int (.lit 1) .int) kLen)
  IO.println s!"w2b: {n2b} steps (expect 1140); na={S3.nextAddr}"
  (match stepFnSTB GoLean.RaftSeam.bfTB S3 C3 with
   | .ok _ => IO.println "w2b end: steps on?!"
   | .error q => IO.println s!"w2b quit: {toString (repr q)}")
  out := out ++ BfLitGen.emitDef "laS3" "SymState" (BfLitGen.pState S3)
  out := out ++ BfLitGen.emitDef "laC3" "SymConfig" (BfLitGen.pC C3)
  let k3 := match C3 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let tgt2 : Nat := match C3 with
    | .retV _ (.stmtOpK _ _ done _ _ _) =>
        (match done with
         | [_, GoLean.Sym.Value.addr (.base a)] => a.id
         | _ => 0)
    | _ => 0
  -- spill-2 elems element = the response message cell
  let respMsg : Nat := match C3 with
    | .retV (GoLean.Sym.Value.slice sv) _ =>
        (match sv.base with
         | some b =>
            (match GoLean.Sym.Heap.lookup S3.heap b with
             | some (.mk _ (.array vs)) =>
                (match vs.toList with
                 | [GoLean.Sym.Value.addr (.base a)] => a.id
                 | _ => 0)
             | _ => 0)
         | none => 0)
    | _ => 0
  IO.println s!"spill-2: target={tgt2} respMsg={respMsg} backing born at {S3.nextAddr}"
  -- CROSSING 2 (atoms 1)
  let S4 : SymState :=
    { heap := (GoLean.Sym.Heap.set S3.heap (.base ⟨tgt2⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 1))) ++ [(.base ⟨S3.nextAddr⟩, .atom 1)],
      nextAddr := S3.nextAddr + 1 }
  out := out ++ BfLitGen.emitDef "laS4" "SymState" (BfLitGen.pState S4)
  -- WINDOW 3
  let (n3, S5, C5) := symEvalWindowTB GoLean.RaftSeam.bfTB 20000 S4 (.next k3)
  let stop5 := match C5 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"w3: {n3} steps; ends at stop: {stop5}; total = {n1 + 1 + n2a + 1 + n2b + 1 + n3} (expect 4828)"
  out := out ++ BfLitGen.emitDef "laS5" "SymState" (BfLitGen.pState S5)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/LaLit.lean.gen" out
  IO.println s!"total generated size: {out.length} chars"
  -- MACHINE VALIDATION at three (c1,c2) pairs
  let b2 := S3.nextAddr
  for (c1, c2) in [(0,0), (3,5), (31,31)] do
    match stepFnIter 4828 LaGen.laσ0C LaGen.laC0C (c1 :: c2 :: List.replicate 40 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (laρw c1 c2 b2 respMsg) LaGen.laσ0C S5
        IO.println s!"(c1,c2)=({c1},{c2}): stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"({c1},{c2}): machine ERROR {e.message.take 120}"
  -- projections at γ(S5)
  let σ5 := γS (laρw 3 5 b2 respMsg) LaGen.laσ0C S5
  let maaStr : String := "msgsAfterAppend"
  let msgsStr : String := "msgs"
  IO.println s!"absOutbox(msgsAfterAppend) = {toString (repr (absOutbox σ5 ⟨31⟩ maaStr))}"
  IO.println s!"absOutbox(msgs) = {toString (repr (absOutbox σ5 ⟨31⟩ msgsStr))}"
  IO.println s!"absRaftLog post = {toString (repr (absRaftLog σ5 ⟨32⟩))}"
  IO.println s!"view post = {toString (repr ((absRaftLog σ5 ⟨32⟩).map AbsLog.view))}"
  IO.println s!"absMessage(arg) PRE = {toString (repr (absMessage (γS (laρw 3 5 b2 respMsg) LaGen.laσ0C LaGen.laS0) (.addr (.base ⟨52⟩))))}"
  IO.println s!"absRaftLog pre = {toString (repr (absRaftLog (γS (laρw 3 5 b2 respMsg) LaGen.laσ0C LaGen.laS0) ⟨32⟩))}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σ5 ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
