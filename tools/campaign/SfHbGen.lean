import GoLeanProofs

/-! # A4-U15 slice 3: the sF×MsgHeartbeat dispatch-arm GENERATOR

The first DISPATCH-ARM equation's literals: the stepFollower ×
MsgHeartbeat arm (U14 census re-pinned at the U15 caller placement:
1,710 steps, ONE choice at 1581 = the handler's msgsAfterAppend...
msgs appendSlice spill, zero statics). Fixture: bf31SymHeap + the
Message with a REAL Type cell (55 ↦ 8) + caller cells r/m/er at
66/67/68 (the StaticCellsExt consumer rule: OFF {61,65}), na₀ 69.
Windows [1581, 128] + ONE spill crossing = 1,710. Emits counts +
crossing addresses as defs (the U13 printer improvement) + the three
boundary states + the quit config. Correctness is NOT trusted from
this probe: the window LINK theorems in `SfHbEquation.lean`
(kernel_rfl) re-check every literal — the drift alarms. -/

open GoLean GoLean.GoCore GoLean.Sym GoLean.RaftSeam

namespace BfLitGen

def W : Nat := 120

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

/-! ## The dispatch fixture (MUST match SfHbEquation.lean's defs). -/

namespace SfHbGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

/-- The Message with a REAL Type cell: hhMsgSym + Type ↦ &55. -/
def sfhbMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def sfhbS0 : SymState :=
  { heap := bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) sfhbMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 8) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def sfhbEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

def sfhbC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepFollower"⟩ #[Expr.var "r", Expr.var "m"])
    sfhbEnv .stop

/-- The validation valuation (probe values: Vote 7, lead 2, state 0,
leadTransferee 5; atom 0 = the spilled handle/backing at head c,
head element = the response-message pointer). -/
def sfρ (backing msgPtr : Nat) (c : Nat) : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨backing⟩), 0, 1, hhCap c⟩ else .nil
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) hhElemTy),
        .array ⟨[.addr (.base ⟨msgPtr⟩)] ++ List.replicate (hhCap c - 1) .nil⟩⟩
      else ⟨none, .nil⟩ }

end SfHbGen

open BfLitGen SfHbGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
  GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  -- window 1: to the spill quit (census: 1581)
  let (n1, S1, C1) := symEvalWindowTB bfTB 3000 SfHbGen.sfhbS0 SfHbGen.sfhbC0
  IO.println s!"w1: {n1} (census said 1581)"
  let (tgt, elemsBase) := match C1 with
    | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK _ _ done _ _ _) =>
        (match done with
         | [_, GoLean.Sym.Value.addr (.base t)] => (t.id, match sv.base with
            | some (.base b) => b.id | _ => 0)
         | _ => (0, 0))
    | _ => (0, 0)
  let msgPtr := match GoLean.Sym.Heap.lookup S1.heap (.base ⟨elemsBase⟩) with
    | some (.mk _ (.array vs)) => (match vs.toList with
        | (GoLean.Sym.Value.addr (.base m)) :: _ => m.id
        | _ => 0)
    | _ => 0
  IO.println s!"spill tgt={tgt} elems={elemsBase} msgPtr={msgPtr} S1 na={S1.nextAddr}"
  if tgt == 0 || msgPtr == 0 then IO.println "OPERAND EXTRACTION FAILED" else do
  let backing := S1.nextAddr
  let S2 : SymState :=
    { heap := (GoLean.Sym.Heap.set S1.heap (.base ⟨tgt⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 0))) ++ [(.base ⟨backing⟩, .atom 0)],
      nextAddr := backing + 1 }
  let k1 := match C1 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let (n2, S3, C3) := symEvalWindowTB bfTB 500 S2 (.next k1)
  let stop3 := match C3 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"w2: {n2} (census: 1710-{n1}-1 = {1710 - n1 - 1}); stop={stop3}"
  if !stop3 then IO.println s!"W2 DID NOT STOP: {(BfLitGen.pC C3).take 300}" else do
  -- EMIT
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.HhEquation\n\n" ++
    "/-! # A4-U15 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The stepFollower×MsgHeartbeat DISPATCH-ARM chain's boundary\n" ++
    "states/configs as SOURCE LITERALS, generated by\n" ++
    "`artifacts/probe/SfHbGen.lean` (the dispatch fixture: bf31SymHeap +\n" ++
    "Message with REAL Type cell 55 ↦ 8 + caller cells 66/67/68, na₀ 69;\n" ++
    "windows [sfhbW1n, sfhbW2n], ONE spill crossing). Counts/addresses\n" ++
    "are GENERATOR-EMITTED defs (the U13 improvement). Correctness: the\n" ++
    "window LINK theorems in `SfHbEquation.lean` (kernel_rfl) re-check\n" ++
    "every literal — the drift alarms. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  out := out ++ BfLitGen.emitDef "sfhbW1n" "Nat" s!"{n1}"
  out := out ++ BfLitGen.emitDef "sfhbW2n" "Nat" s!"{n2}"
  out := out ++ BfLitGen.emitDef "sfhbMsgPtr" "Nat" s!"{msgPtr}"
  out := out ++ BfLitGen.emitDef "sfhbTgt" "Nat" s!"{tgt}"
  out := out ++ BfLitGen.emitDef "sfhbElems" "Nat" s!"{elemsBase}"
  out := out ++ BfLitGen.emitDef "sfhbBacking" "Nat" s!"{backing}"
  out := out ++ BfLitGen.emitDef "sfhbS1" "SymState" (BfLitGen.pState S1)
  out := out ++ BfLitGen.emitDef "sfhbC1" "SymConfig" (BfLitGen.pC C1)
  out := out ++ BfLitGen.emitDef "sfhbS2" "SymState" (BfLitGen.pState S2)
  out := out ++ BfLitGen.emitDef "sfhbS3" "SymState" (BfLitGen.pState S3)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/SfHbLit.lean.gen" out
  IO.println s!"generated {out.length} chars"
  -- MACHINE validation: γ==machine at c = 0/3/31
  let nTot := n1 + 1 + n2
  IO.println s!"total = {nTot} (census said 1710)"
  for c in [0, 3, 31] do
    let ρc := SfHbGen.sfρ backing msgPtr c
    let σ0 := γS ρc wBase SfHbGen.sfhbS0
    match stepFnIter nTot σ0 (γC ρc SfHbGen.sfhbC0) (c :: List.replicate 20 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS ρc wBase S3
        IO.println s!"c={c}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"c={c}: ERROR {e.message.take 100}"
  -- projections at γ(S3), c = 3
  let ρ3 := SfHbGen.sfρ backing msgPtr 3
  let σ3 := γS ρ3 wBase S3
  let er := (Heap.lookup σ3.heap (.base ⟨68⟩)).map (·.value)
  IO.println s!"er = {(toString (repr er)).take 140}"
  IO.println s!"absOutbox(msgs) = {(toString (repr (absOutbox σ3 ⟨31⟩ "msgs"))).take 200}"
  IO.println s!"absOutbox(maa) = {(toString (repr (absOutbox σ3 ⟨31⟩ "msgsAfterAppend"))).take 80}"
  IO.println s!"lead = {toString (repr (GoLean.Lens.fieldReadU64 σ3 ⟨31⟩ ⟨"raft.raft"⟩ "lead"))}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σ3 ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
  IO.println s!"Term = {toString (repr (GoLean.Lens.fieldReadU64 σ3 ⟨31⟩ ⟨"raft.raft"⟩ "Term"))}"
  IO.println s!"absRaftLog pre = {(toString (repr (absRaftLog (γS ρ3 wBase SfHbGen.sfhbS0) ⟨32⟩))).take 200}"
  IO.println s!"absRaftLog post = {(toString (repr (absRaftLog σ3 ⟨32⟩))).take 200}"
  IO.println s!"absMessage(arg) pre = {(toString (repr (absMessage (γS ρ3 wBase SfHbGen.sfhbS0) (.addr (.base ⟨52⟩))))).take 260}"
