import GoLeanProofs

/-! # A4-U17: the sL×MsgBeat dispatch-arm GENERATOR (bcastHeartbeat)

U16 census (StepLeaderProbe, machine walk at the full-static fixture):
3,362 steps / FOUR choices at [288, 317, 346, 1854], zero static
reads, na +193, msgs = heartbeats to the peers, er = nil. This
generator walks the MIRROR at the statics-free dispatch fixture
(bf31SymHeap + Type 55 ↦ 1 = MsgBeat + caller cells [66,69), na₀ 69 —
the SfHb/SCHb placement; zero static reads censused, so no complement
block) with an ADAPTIVE staged crossing classification:
  - mapIterK quits: produced.size < 3 → Visit pick (vars 6/7/8),
    produced.size = 3 → range STOP;
  - sortSlice stmtOpK → the SORT collapse (uCrossSort);
  - appendSlice stmtOpK with a CONCRETE old slice → the SPILL
    (atoms 0 — the SfHb/SCHb construction);
  - appendSlice stmtOpK with old = .atom 0 → **THE IN-PLACE SECOND
    APPEND** (the U12 atom-re-read watch-item, fired: the second
    send re-reads the spilled msgs handle; atoms 1, no choice, no
    alloc).
Correctness is NOT trusted from this probe: the window LINK theorems
in `SlbEquation.lean` (kernel_rfl) re-check every literal. γ==machine
validated below at four 4-choice tuples INCLUDING the cap-2 boundary
c₄=30, plus the c₄=29 RE-SPILL divergence witness (the residual
family's evidence — expect a 5th consumed choice, NOT a match). -/

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

/-! ## The sL dispatch fixture: bf31SymHeap AS-IS (all four scalars
symbolic — the walk decides, fail closed), Type 55 ↦ 1 = MsgBeat,
caller cells [66,69), na₀ 69. -/

namespace SlbGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def slbMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def slbS0 : SymState :=
  { heap := bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) slbMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 1) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def slbEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

def slbC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepLeader"⟩ #[Expr.var "r", Expr.var "m"])
    slbEnv .stop

/-- Full-tuple validation valuation: raft scalars (Vote 7, lead 2,
state 2 = leader, ldT 5) SYMBOLIC via vars 1-4; Visit pick vars 6-8
via uρ; spill atoms 0 (post-spill, len 1) and IN-PLACE atoms 1
(post-second-append, len 2), both at cap `hhCap c₄`. -/
def slbρ (backing msgPtr m2Ptr : Nat) (c₁ c₂ c₄ : Nat) : Valuation :=
  uρ { ints := fun i => [0, 7, 2, 2, 5].getD i 0
       bools := fun _ => false
       vals := fun i =>
         if i = 0 then .slice ⟨some (.base ⟨backing⟩), 0, 1, hhCap c₄⟩
         else if i = 1 then .slice ⟨some (.base ⟨backing⟩), 0, 2, hhCap c₄⟩
         else .nil
       cells := fun i =>
         if i = 0 then ⟨some (.array (hhCap c₄) hhElemTy),
           .array ⟨[.addr (.base ⟨msgPtr⟩)] ++ List.replicate (hhCap c₄ - 1) .nil⟩⟩
         else if i = 1 then ⟨some (.array (hhCap c₄) hhElemTy),
           .array ⟨[.addr (.base ⟨msgPtr⟩), .addr (.base ⟨m2Ptr⟩)]
             ++ List.replicate (hhCap c₄ - 2) .nil⟩⟩
         else ⟨none, .nil⟩ }
    0 (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)

end SlbGen

open BfLitGen SlbGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
  GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let mut S := SlbGen.slbS0
  let mut C := SlbGen.slbC0
  let mut counts : List Nat := []
  let mut states : List (String × SymState) := []
  let mut configs : List (String × SymConfig) := []
  let mut idx := 0
  let mut nChoices := 0
  let mut spillTgt := 0
  let mut spillElems := 0
  let mut spillMsgPtr := 0
  let mut spillBacking := 0
  let mut ipTgt := 0
  let mut ipElems := 0
  let mut ipMsg2Ptr := 0
  let mut stageLog : List String := []
  let mut failed := false
  let mut done := false
  for _ in [0:12] do
    if failed || done then pure () else do
    let (n, S', C') := symEvalWindowTB bfTB 6000 S C
    idx := idx + 1
    counts := counts ++ [n]
    states := states ++ [(s!"slbS{2*idx-1}", S')]
    -- classify the quit
    match C' with
    | .next .stop =>
        done := true
        IO.println s!"w{idx}: {n} steps -> STOP-FINAL na={S'.nextAddr}"
    | .next (.mapIterK _ _ _ _ _ base produced _ _ _) =>
        configs := configs ++ [(s!"slbC{2*idx-1}", C')]
        if produced.size < 3 then
          let v := 6 + produced.size
          stageLog := stageLog ++ [s!"PICK{v}"]
          IO.println s!"w{idx}: {n} -> PICK var{v} (base={(toString (repr base)).take 30} produced={produced.size}) na={S'.nextAddr}"
          let (S2, C2) := uCrossPick v .uint64 S' C'
          S := S2; C := C2
          nChoices := nChoices + 1
        else
          stageLog := stageLog ++ ["STOP"]
          IO.println s!"w{idx}: {n} -> RANGE-STOP (produced={produced.size}) na={S'.nextAddr}"
          let (S2, C2) := uCrossStop S' C'
          S := S2; C := C2
    | .retV rv (.stmtOpK (.sortSlice _) _ _ _ _ _) =>
        configs := configs ++ [(s!"slbC{2*idx-1}", C')]
        stageLog := stageLog ++ ["SORT"]
        IO.println s!"w{idx}: {n} -> SORT ({(BfLitGen.pV rv).take 40}) na={S'.nextAddr}"
        let (S2, C2) := uCrossSort S' C'
        S := S2; C := C2
    | .retV (GoLean.Sym.Value.slice sv)
        (.stmtOpK (.appendSlice _) _ done' _ _ k') =>
        configs := configs ++ [(s!"slbC{2*idx-1}", C')]
        match done' with
        | [GoLean.Sym.Value.slice osv, GoLean.Sym.Value.addr (.base t)] =>
            -- concrete old slice -> the SPILL (atoms 0)
            stageLog := stageLog ++ ["SPILL"]
            spillTgt := t.id
            spillElems := (match sv.base with
              | some (.base b) => b.id | _ => 0)
            spillMsgPtr := (match GoLean.Sym.Heap.lookup S'.heap (.base ⟨spillElems⟩) with
              | some (.mk _ (.array vs)) => (match vs.toList with
                  | (GoLean.Sym.Value.addr (.base m)) :: _ => m.id
                  | _ => 0)
              | _ => 0)
            spillBacking := S'.nextAddr
            IO.println s!"w{idx}: {n} -> SPILL (oldLen={osv.len} oldCap={osv.cap} tgt={t.id} elems={spillElems} msgPtr={spillMsgPtr} backing={spillBacking}) na={S'.nextAddr}"
            let S2 : SymState :=
              { heap := (GoLean.Sym.Heap.set S'.heap (.base ⟨t.id⟩)
                  (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
                    (.atom 0))) ++ [(.base ⟨spillBacking⟩, .atom 0)],
                nextAddr := spillBacking + 1 }
            S := S2; C := .next k'
            nChoices := nChoices + 1
        | [GoLean.Sym.Value.atom 0, GoLean.Sym.Value.addr (.base t)] =>
            -- THE IN-PLACE SECOND APPEND (atoms 1; no choice, no alloc)
            stageLog := stageLog ++ ["INPLACE"]
            ipTgt := t.id
            ipElems := (match sv.base with
              | some (.base b) => b.id | _ => 0)
            ipMsg2Ptr := (match GoLean.Sym.Heap.lookup S'.heap (.base ⟨ipElems⟩) with
              | some (.mk _ (.array vs)) => (match vs.toList with
                  | (GoLean.Sym.Value.addr (.base m)) :: _ => m.id
                  | _ => 0)
              | _ => 0)
            IO.println s!"w{idx}: {n} -> INPLACE (tgt={t.id} elems={ipElems} msg2Ptr={ipMsg2Ptr}) na={S'.nextAddr}"
            let S2 : SymState :=
              { heap := GoLean.Sym.Heap.set
                  (GoLean.Sym.Heap.set S'.heap (.base ⟨spillBacking⟩) (.atom 1))
                  (.base ⟨t.id⟩)
                  (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
                    (.atom 1)),
                nextAddr := S'.nextAddr }
            S := S2; C := .next k'
        | _ =>
            IO.println s!"w{idx}: {n} -> APPEND SHAPE MISMATCH done={done'.length}"
            failed := true
    | _ =>
        IO.println s!"w{idx}: {n} -> UNCLASSIFIED QUIT: {(BfLitGen.pC C').take 400}"
        failed := true
    match C with
    | .panicked msg => IO.println s!"CROSSING FAILED: {msg}"; failed := true
    | _ => pure ()
  if failed then IO.println "ABORTED" else do
  let nWin := counts.length
  let nCross := nWin - 1
  let nTot := counts.foldl (·+·) 0 + nCross
  IO.println s!"stages = {stageLog}"
  IO.println s!"windows = {counts} crossings = {nCross} choices = {nChoices} total = {nTot}"
  IO.println s!"spill: tgt={spillTgt} elems={spillElems} msgPtr={spillMsgPtr} backing={spillBacking}"
  IO.println s!"inplace: tgt={ipTgt} elems={ipElems} msg2Ptr={ipMsg2Ptr}"
  let Sfin := (states.getLast?.map (·.2)).getD SlbGen.slbS0
  -- MACHINE validation at four 4-choice tuples (incl. cap boundary c₄=30)
  for t in [(0,0,0,0), (2,1,0,5), (1,0,0,31), (0,1,0,30)] do
    let (c₁, c₂, c₃, c₄) := t
    let ρc := SlbGen.slbρ spillBacking spillMsgPtr ipMsg2Ptr c₁ c₂ c₄
    let σ0 := γS ρc wBase SlbGen.slbS0
    let stream := [c₁, c₂, c₃, c₄] ++ List.replicate 20 0
    match stepFnIter nTot σ0 (γC ρc SlbGen.slbC0) stream with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS ρc wBase Sfin
        IO.println s!"t={t}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"t={t}: ERROR {e.message.take 140}"
  -- the RE-SPILL divergence witness (c₄ = 29 -> hhCap 1 -> a FIFTH choice)
  (do
    let ρc := SlbGen.slbρ spillBacking spillMsgPtr ipMsg2Ptr 0 0 29
    let σ0 := γS ρc wBase SlbGen.slbS0
    let stream := ([0, 0, 0, 29] : List Nat) ++ List.replicate 20 0
    match stepFnIter nTot σ0 (γC ρc SlbGen.slbC0) stream with
    | .ok (cM, _, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        IO.println s!"RE-SPILL c₄=29: stop={stop} choicesConsumed={24 - chM.length} (expect 5 — the residual family)"
    | .error e => IO.println s!"RE-SPILL c₄=29: ERROR {e.message.take 140}")
  -- projections at the final literal
  let ρ3 := SlbGen.slbρ spillBacking spillMsgPtr ipMsg2Ptr 2 1 5
  let σf := γS ρ3 wBase Sfin
  let er := (Heap.lookup σf.heap (.base ⟨68⟩)).map (·.value)
  IO.println s!"er = {(toString (repr er)).take 140}"
  IO.println s!"absOutbox(msgs) = {(toString (repr (absOutbox σf ⟨31⟩ "msgs"))).take 400}"
  IO.println s!"absOutbox(maa) = {(toString (repr (absOutbox σf ⟨31⟩ "msgsAfterAppend"))).take 120}"
  IO.println s!"absMessage(pre) = {(toString (repr (absMessage (γS ρ3 wBase SlbGen.slbS0) (.addr (.base ⟨52⟩))))).take 200}"
  IO.println s!"lead = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "lead"))} state = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "state"))} Term = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "Term"))}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
  IO.println s!"absRaftLog post = {(toString (repr (absRaftLog σf ⟨32⟩))).take 200}"
  -- wrap depths (the §4c read-the-literal rule)
  let showV : GoLean.Sym.Value symDom → String := fun v => match v with
    | .int si k => s!"int {(repr si).pretty 10000} {(repr k).pretty 60}"
    | _ => "other"
  match GoLean.Sym.Heap.lookup Sfin.heap (.base ⟨31⟩) with
  | some (.mk _ (GoLean.Sym.Value.struct _ fs)) =>
      for p in fs.toList do
        if p.1 == "Vote" || p.1 == "lead" || p.1 == "state" || p.1 == "Term" || p.1 == "leadTransferee" then
          IO.println s!"symfield {p.1} = {(showV p.2).take 400}"
  | _ => IO.println "no raft cell"
  -- EMIT the literal module
  let header := "import GoLeanProofs.Specs.Raft.BfSteps2\nimport GoLeanProofs.Specs.Raft.SfHbLit\nimport GoLeanProofs.Specs.Raft.HhEquation\n\n" ++
    "/-! # A4-U17 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The stepLeader×MsgBeat arm chain's boundary states/configs as\n" ++
    "SOURCE LITERALS, generated by `artifacts/probe/SlbGen.lean`\n" ++
    "(dispatch fixture + 3 Visit picks + range-stop + sort collapse +\n" ++
    "the msgs spill + THE IN-PLACE SECOND APPEND — the atom-re-read\n" ++
    "crossing). The crossing outputs (even indices) are DEFINED via\n" ++
    "uCrossPick/Stop/Sort + the spill/in-place constructions in\n" ++
    "SlbEquation.lean. Counts/addresses are GENERATOR-EMITTED defs.\n" ++
    "The window LINK theorems in `SlbEquation.lean` (kernel_rfl)\n" ++
    "re-check every literal — the drift alarms. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  let mut wi := 0
  for n in counts do
    wi := wi + 1
    out := out ++ BfLitGen.emitDef s!"slbW{wi}n" "Nat" s!"{n}"
  out := out ++ BfLitGen.emitDef "slbMsgPtr" "Nat" s!"{spillMsgPtr}"
  out := out ++ BfLitGen.emitDef "slbTgt" "Nat" s!"{spillTgt}"
  out := out ++ BfLitGen.emitDef "slbElems" "Nat" s!"{spillElems}"
  out := out ++ BfLitGen.emitDef "slbBacking" "Nat" s!"{spillBacking}"
  out := out ++ BfLitGen.emitDef "slbMsg2Ptr" "Nat" s!"{ipMsg2Ptr}"
  out := out ++ BfLitGen.emitDef "slbTgt2" "Nat" s!"{ipTgt}"
  out := out ++ BfLitGen.emitDef "slbElems2" "Nat" s!"{ipElems}"
  for (nm, St) in states do
    out := out ++ BfLitGen.emitDef nm "SymState" (BfLitGen.pState St)
  for (nm, Cf) in configs do
    out := out ++ BfLitGen.emitDef nm "SymConfig" (BfLitGen.pC Cf)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/SlbLit.lean.gen" out
  IO.println s!"generated {out.length} chars"
