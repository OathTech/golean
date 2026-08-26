import GoLeanProofs

/-! # A4-U16: the sF×MsgProp DROP-arm GENERATOR (choice-free)

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

/-! ## The DROP-arm fixture (MUST match SfPdEquation.lean's defs):
lead = 0 CONCRETE (the no-leader family — the arm branches on it),
Type cell 55 ↦ 2 (MsgProp), the FULL static block (the mirror + the
machine both need cells 16/17 + payloads 61/65 + the U12 block),
na₀ = staticComplementNa = 98. U15 census: 254 steps, ZERO choices,
one static read (232, 17), na 98→112, er = ErrProposalDropped. -/

namespace SfPdGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def sfpdMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- bf31SymHeap with the lead field (x₂) FORCED to concrete 0 — the
drop arm's branching precondition. -/
def sfpdRaftHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨31⟩ then
      (p.1, match p.2 with
        | .mk dty (.struct tid fs) =>
            .mk dty (.struct tid (fs.map (fun (q : String × SymValue) =>
              if q.1 == "lead" then (q.1, .int (.lit 0) .uint64) else q)))
        | c => c)
    else p)

def sfpdS0 : SymState :=
  { heap := sfpdRaftHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) sfpdMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 2) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)] ++
      staticComplementSym ++ staticComplementExtSym,
    nextAddr := staticComplementNa }

def sfpdEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

def sfpdC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepFollower"⟩ #[Expr.var "r", Expr.var "m"])
    sfpdEnv .stop

def sfpdρw : Valuation :=
  { ints := fun i => [0, 7, 0, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

end SfPdGen

open BfLitGen SfPdGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
  GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let (n1, S1, C1) := symEvalWindowTB bfTB 3000 SfPdGen.sfpdS0 SfPdGen.sfpdC0
  let stop1 := match C1 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"w1: {n1} (census said 254); stop={stop1}; na={S1.nextAddr}"
  if !stop1 then IO.println s!"DID NOT STOP: {(BfLitGen.pC C1).take 400}" else do
  let header := "import GoLeanProofs.Specs.Raft.StaticCellsExt\nimport GoLeanProofs.Specs.Raft.HhEquation\n\n" ++
    "/-! # A4-U16 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The stepFollower×MsgProp DROP-arm final state as a SOURCE LITERAL,\n" ++
    "generated by `artifacts/probe/SfPdGen.lean` (lead = 0 fixture +\n" ++
    "Type 55 ↦ 2 + the FULL static block, na₀ 98; ONE window, ZERO\n" ++
    "choices). Correctness: the window LINK theorem in\n" ++
    "`SfPdEquation.lean` (kernel_rfl) re-checks the literal. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  out := out ++ BfLitGen.emitDef "sfpdW1n" "Nat" s!"{n1}"
  out := out ++ BfLitGen.emitDef "sfpdS1" "SymState" (BfLitGen.pState S1)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/SfPdLit.lean.gen" out
  IO.println s!"generated {out.length} chars"
  -- MACHINE validation at THREE valuations (Vote 7/9/1023 — x₁ rides)
  for v in [7, 9, 1023] do
    let ρc : Valuation :=
      { ints := fun i => [0, v, 0, 0, 5].getD i 0
        bools := fun _ => false
        vals := fun _ => .nil
        cells := fun _ => ⟨none, .nil⟩ }
    let σ0 := γS ρc wBase SfPdGen.sfpdS0
    match stepFnIter n1 σ0 (γC ρc SfPdGen.sfpdC0) (List.replicate 20 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS ρc wBase S1
        IO.println s!"v={v}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"v={v}: ERROR {e.message.take 100}"
  -- projections at γ(S1)
  let σ1 := γS SfPdGen.sfpdρw wBase S1
  let er := (Heap.lookup σ1.heap (.base ⟨68⟩)).map (·.value)
  IO.println s!"er = {(toString (repr er)).take 240}"
  IO.println s!"absOutbox(msgs) = {(toString (repr (absOutbox σ1 ⟨31⟩ "msgs"))).take 60}"
  IO.println s!"absOutbox(maa) = {(toString (repr (absOutbox σ1 ⟨31⟩ "msgsAfterAppend"))).take 60}"
  IO.println s!"lead = {toString (repr (GoLean.Lens.fieldReadU64 σ1 ⟨31⟩ ⟨"raft.raft"⟩ "lead"))}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σ1 ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
  IO.println s!"Term = {toString (repr (GoLean.Lens.fieldReadU64 σ1 ⟨31⟩ ⟨"raft.raft"⟩ "Term"))}"
  IO.println s!"absRaftLog pre = {(toString (repr (absRaftLog (γS SfPdGen.sfpdρw wBase SfPdGen.sfpdS0) ⟨32⟩))).take 200}"
  IO.println s!"absRaftLog post = {(toString (repr (absRaftLog σ1 ⟨32⟩))).take 200}"
  IO.println s!"absMessage(arg) pre = {(toString (repr (absMessage (γS SfPdGen.sfpdρw wBase SfPdGen.sfpdS0) (.addr (.base ⟨52⟩))))).take 300}"
  -- Vote wrap depth in the final literal (the §4c rule)
  let showV : GoLean.Sym.Value symDom → String := fun v => match v with
    | .int si k => s!"int {(repr si).pretty 10000} {(repr k).pretty 100}"
    | _ => "other"
  match GoLean.Sym.Heap.lookup S1.heap (.base ⟨31⟩) with
  | some (.mk _ (GoLean.Sym.Value.struct _ fs)) =>
      for p in fs.toList do
        if p.1 == "Vote" || p.1 == "lead" then
          IO.println s!"symfield {p.1} = {showV p.2}"
  | _ => IO.println "no raft cell"
