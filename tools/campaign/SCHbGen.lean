import GoLeanProofs

/-! # A4-U16: the sC×MsgHeartbeat DEPTH-2 dispatch-arm GENERATOR (bf spine + Hh tail; 8 windows / 7 crossings / 5 choices)

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

/-! ## The sC dispatch fixture (MUST match SCHbEquation.lean's defs):
state = x₃ SYMBOLIC (rides unless the mirror branches on it — the
walk decides, fail closed), Type 55 ↦ 8, caller cells [66,69),
na₀ 69. U14/U15 census: 4,969 steps, FIVE choices at
[983, 1167, 1196, 1225, 4879] (Intn + 3 Visit + the Hh spill). -/

namespace SCHbGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def scMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- bf31SymHeap with state (x₃) FORCED to concrete 1 — stepCandidate
computes myVoteRespType(r.state) up front (probe: symbolic x₃ quits
q1Branch at step 20), so the candidate family is state-concrete. -/
def scRaftHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨31⟩ then
      (p.1, match p.2 with
        | .mk dty (.struct tid fs) =>
            .mk dty (.struct tid (fs.map (fun (q : String × SymValue) =>
              if q.1 == "state" then (q.1, .int (.lit 1) .uint64) else q)))
        | c => c)
    else p)

def scS0 : SymState :=
  { heap := scRaftHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) scMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 8) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def scEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

def scC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepCandidate"⟩ #[Expr.var "r", Expr.var "m"])
    scEnv .stop

/-- Full-tuple validation valuation: raft scalars (Vote 7, lead 2,
STATE 1 = candidate, ldT 5), pick vars 5-8 via uρ', spill atom 0. -/
def scρ (backing msgPtr : Nat) (c₁ c₂ c₃ c₅ : Nat) : Valuation :=
  uρ' { ints := fun i => [0, 7, 2, 0, 5].getD i 0
        bools := fun _ => false
        vals := fun i => if i = 0
          then .slice ⟨some (.base ⟨backing⟩), 0, 1, hhCap c₅⟩ else .nil
        cells := fun i => if i = 0
          then ⟨some (.array (hhCap c₅) hhElemTy),
            .array ⟨[.addr (.base ⟨msgPtr⟩)] ++ List.replicate (hhCap c₅ - 1) .nil⟩⟩
          else ⟨none, .nil⟩ } c₁ c₂ c₃

end SCHbGen

open BfLitGen SCHbGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
  GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let describeQuit : SymConfig → String := fun C => match C with
    | .next (.mapIterK _ _ _ _ _ base produced _ _ _) =>
        s!"mapIter base={(toString (repr base)).take 40} produced={produced.size}"
    | .retV _ (.stmtOpK op _ _ _ _ _) => s!"stmtOp {(toString (repr op)).take 60}"
    | .retV _ (.ifK _ _ _ _) => "BRANCH (symbolic cond!)"
    | _ => "OTHER"
  -- stage walk: window, then crossing, hardcoded expected sequence
  let mut S := SCHbGen.scS0
  let mut C := SCHbGen.scC0
  let mut counts : List Nat := []
  let mut states : List (String × SymState) := []
  let mut configs : List (String × SymConfig) := []
  let mut idx := 0
  let stages := ["P5", "P6", "P7", "P8", "STOP", "SORT", "SPILL"]
  let mut spillTgt := 0
  let mut spillElems := 0
  let mut spillMsgPtr := 0
  let mut spillBacking := 0
  let mut failed := false
  for stage in stages do
    if failed then pure () else do
    let (n, S', C') := symEvalWindowTB bfTB 6000 S C
    idx := idx + 1
    counts := counts ++ [n]
    states := states ++ [(s!"scS{2*idx-1}", S')]
    configs := configs ++ [(s!"scC{2*idx-1}", C')]
    IO.println s!"w{idx}: {n} steps -> quit [{describeQuit C'}] (expect {stage}) na={S'.nextAddr}"
    match stage with
    | "P5" =>
        let (S2, C2) := uCrossPick 5 .int S' C'
        S := S2; C := C2
    | "P6" =>
        let (S2, C2) := uCrossPick 6 .uint64 S' C'
        S := S2; C := C2
    | "P7" =>
        let (S2, C2) := uCrossPick 7 .uint64 S' C'
        S := S2; C := C2
    | "P8" =>
        let (S2, C2) := uCrossPick 8 .uint64 S' C'
        S := S2; C := C2
    | "STOP" =>
        let (S2, C2) := uCrossStop S' C'
        S := S2; C := C2
    | "SORT" =>
        let (S2, C2) := uCrossSort S' C'
        S := S2; C := C2
    | _ => -- SPILL
        match C' with
        | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK _ _ done _ _ k') =>
            let (tgt, elemsBase) := (match done with
              | [_, GoLean.Sym.Value.addr (.base t)] => (t.id, match sv.base with
                 | some (.base b) => b.id | _ => 0)
              | _ => (0, 0))
            spillTgt := tgt; spillElems := elemsBase
            spillMsgPtr := (match GoLean.Sym.Heap.lookup S'.heap (.base ⟨elemsBase⟩) with
              | some (.mk _ (.array vs)) => (match vs.toList with
                  | (GoLean.Sym.Value.addr (.base m)) :: _ => m.id
                  | _ => 0)
              | _ => 0)
            spillBacking := S'.nextAddr
            let S2 : SymState :=
              { heap := (GoLean.Sym.Heap.set S'.heap (.base ⟨tgt⟩)
                  (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
                    (.atom 0))) ++ [(.base ⟨spillBacking⟩, .atom 0)],
                nextAddr := spillBacking + 1 }
            S := S2; C := .next k'
        | _ =>
            IO.println "SPILL SHAPE MISMATCH — abort"
            failed := true
    match C with
    | .panicked msg => IO.println s!"CROSSING FAILED: {msg}"; failed := true
    | _ => pure ()
  if failed then IO.println "ABORTED" else do
  -- final window
  let (n8, S8, C8) := symEvalWindowTB bfTB 6000 S C
  let stop8 := match C8 with | GoLean.Sym.Config.next .stop => true | _ => false
  counts := counts ++ [n8]
  states := states ++ [("scS15", S8)]
  IO.println s!"w8: {n8} -> stop={stop8} na={S8.nextAddr}"
  IO.println s!"windows = {counts} total+cross = {counts.foldl (·+·) 0 + 7}"
  IO.println s!"spill: tgt={spillTgt} elems={spillElems} msgPtr={spillMsgPtr} backing={spillBacking}"
  if !stop8 then IO.println s!"W8 DID NOT STOP: {(BfLitGen.pC C8).take 400}" else do
  -- MACHINE validation at three tuples
  let nTot := counts.foldl (·+·) 0 + 7
  for t in [(0,0,0,0,0), (3,1,1,0,5), (9,2,1,1,31)] do
    let (c₁, c₂, c₃, c₄, c₅) := t
    let ρc := SCHbGen.scρ spillBacking spillMsgPtr c₁ c₂ c₃ c₅
    let σ0 := γS ρc wBase SCHbGen.scS0
    let stream := [c₁, c₂, c₃, c₄, c₅] ++ List.replicate 20 0
    match stepFnIter nTot σ0 (γC ρc SCHbGen.scC0) stream with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS ρc wBase S8
        IO.println s!"t={t}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"t={t}: ERROR {e.message.take 140}"
  -- projections at the final state
  let ρ3 := SCHbGen.scρ spillBacking spillMsgPtr 3 1 1 5
  let σf := γS ρ3 wBase S8
  let er := (Heap.lookup σf.heap (.base ⟨68⟩)).map (·.value)
  IO.println s!"er = {(toString (repr er)).take 140}"
  IO.println s!"absOutbox(msgs) = {(toString (repr (absOutbox σf ⟨31⟩ "msgs"))).take 200}"
  IO.println s!"lead = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "lead"))} state = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "state"))} Term = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "Term"))}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
  IO.println s!"absRaftLog post = {(toString (repr (absRaftLog σf ⟨32⟩))).take 200}"
  -- wrap depths (the §4c rule)
  let showV : GoLean.Sym.Value symDom → String := fun v => match v with
    | .int si k => s!"int {(repr si).pretty 10000} {(repr k).pretty 60}"
    | _ => "other"
  match GoLean.Sym.Heap.lookup S8.heap (.base ⟨31⟩) with
  | some (.mk _ (GoLean.Sym.Value.struct _ fs)) =>
      for p in fs.toList do
        if p.1 == "Vote" || p.1 == "lead" || p.1 == "state" || p.1 == "Term" || p.1 == "leadTransferee" then
          IO.println s!"symfield {p.1} = {(showV p.2).take 300}"
  | _ => IO.println "no raft cell"
  -- EMIT the literal module
  let header := "import GoLeanProofs.Specs.Raft.BfSteps2\nimport GoLeanProofs.Specs.Raft.SfHbLit\nimport GoLeanProofs.Specs.Raft.HhEquation\n\n" ++
    "/-! # A4-U16 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The stepCandidate×MsgHeartbeat DEPTH-2 arm chain's boundary\n" ++
    "states/configs as SOURCE LITERALS, generated by\n" ++
    "`artifacts/probe/SCHbGen.lean` (dispatch fixture + the bf reset\n" ++
    "spine's 4 picks + range-stop + sort collapse + the Hh spill; the\n" ++
    "crossing outputs (even indices) are DEFINED via uCrossPick/Stop/\n" ++
    "Sort + the spill construction in SCHbEquation.lean — the Bf31\n" ++
    "pattern). Counts/addresses are GENERATOR-EMITTED defs. The window\n" ++
    "LINK theorems in `SCHbEquation.lean` (kernel_rfl) re-check every\n" ++
    "literal — the drift alarms. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  let mut wi := 0
  for n in counts do
    wi := wi + 1
    out := out ++ BfLitGen.emitDef s!"scW{wi}n" "Nat" s!"{n}"
  out := out ++ BfLitGen.emitDef "scMsgPtr" "Nat" s!"{spillMsgPtr}"
  out := out ++ BfLitGen.emitDef "scTgt" "Nat" s!"{spillTgt}"
  out := out ++ BfLitGen.emitDef "scElems" "Nat" s!"{spillElems}"
  out := out ++ BfLitGen.emitDef "scBacking" "Nat" s!"{spillBacking}"
  for (nm, St) in states do
    out := out ++ BfLitGen.emitDef nm "SymState" (BfLitGen.pState St)
  for (nm, Cf) in configs do
    out := out ++ BfLitGen.emitDef nm "SymConfig" (BfLitGen.pC Cf)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/SCHbLit.lean.gen" out
  IO.println s!"generated {out.length} chars"
