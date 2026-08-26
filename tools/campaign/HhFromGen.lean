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


/-! ## The From-SYMBOLIC handleHeartbeat chain (A4-U14 slice 2):
the Hh no-op fixture with cell 54 (m.From) SYMBOLIC (var 5). Probe
`HhFromProbe.lean` (this unit): windows [1259, 39, 25] + the BRANCH
crossing (send's self-addressed guard, cond = eqI(norm²(x₅), 1),
else-arm empty) + the spill crossing (Hh's cells verbatim: elems 124,
tgt 125, backing 126, msgPtr 74) = 1,325 steps — the concrete Hh
schedule, γ==machine at c=0/3/31 with ints5=2. Emits counts +
addresses as defs (the U13 improvement) + the four boundary states +
two quit configs. -/

namespace HhFromGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def hfS0 : SymState :=
  { heap := hhS0.heap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
      if p.1 == .base ⟨54⟩ then
        (p.1, .mk (some (.int .uint64)) (.int (.var 5) .uint64))
      else p),
    nextAddr := 55 }

def hfρ (c : Nat) : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5, 2].getD i 0
    bools := fun _ => false
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c⟩ else .nil
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) hhElemTy), hhBackingVal c⟩
      else ⟨none, .nil⟩ }

end HhFromGen

open BfLitGen HhFromGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  -- window 1: to the branch quit
  let (n1, S1, C1) := symEvalWindowTB bfTB 3000 HhFromGen.hfS0 hhC0
  IO.println s!"w1: {n1} (probe said 1259)"
  let (cond, elseArm, env1) := match C1 with
    | .retV (GoLean.Sym.Value.bool sb) (.ifK _ e env _) => (some sb, some e, some env)
    | _ => (none, none, none)
  if cond.isNone then IO.println "NOT A BRANCH QUIT — abort" else do
  -- branch crossing: else arm (γB false at ints5 ≠ 1), state unchanged
  let C1' : SymConfig := match C1 with
    | .retV _ (.ifK _ e env k) => .exec e env k
    | _ => .next .stop
  -- window 2: to the spill quit
  let (n2, S2, C2) := symEvalWindowTB bfTB 3000 S1 C1'
  IO.println s!"w2: {n2} (probe said 39)"
  let (tgt, elemsBase) := match C2 with
    | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK _ _ done _ _ _) =>
        (match done with
         | [_, GoLean.Sym.Value.addr (.base t)] => (t.id, match sv.base with
            | some (.base b) => b.id | _ => 0)
         | _ => (0, 0))
    | _ => (0, 0)
  let msgPtr := match GoLean.Sym.Heap.lookup S2.heap (.base ⟨elemsBase⟩) with
    | some (.mk _ (.array vs)) => (match vs.toList with
        | (GoLean.Sym.Value.addr (.base m)) :: _ => m.id
        | _ => 0)
    | _ => 0
  IO.println s!"spill tgt={tgt} elems={elemsBase} msgPtr={msgPtr} S2 na={S2.nextAddr}"
  if tgt == 0 || msgPtr == 0 then IO.println "OPERAND EXTRACTION FAILED" else do
  let backing := S2.nextAddr
  let S3 : SymState :=
    { heap := (GoLean.Sym.Heap.set S2.heap (.base ⟨tgt⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 0))) ++ [(.base ⟨backing⟩, .atom 0)],
      nextAddr := backing + 1 }
  let k2 := match C2 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let (n3, S4, C4) := symEvalWindowTB bfTB 300 S3 (.next k2)
  let stop4 := match C4 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"w3: {n3} (probe said 25); stop={stop4}"
  if !stop4 then IO.println "W3 DID NOT STOP" else do
  -- EMIT
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Sym.BranchTransport\nimport GoLeanProofs.Specs.Raft.HhLit\nimport GoLeanProofs.Specs.Raft.HhEquation\n\n" ++
    "/-! # A4-U14 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The From-SYMBOLIC handleHeartbeat chain's boundary states/configs\n" ++
    "as SOURCE LITERALS, generated by `artifacts/probe/HhFromGen.lean`\n" ++
    "(the Hh no-op fixture with cell 54 = var 5; windows [1259,39,25],\n" ++
    "the send self-addressed-guard BRANCH crossing between windows 1-2,\n" ++
    "the Hh spill crossing between 2-3). Counts/addresses are\n" ++
    "GENERATOR-EMITTED defs (the U13 improvement). Correctness: the\n" ++
    "window LINK theorems in `HhFromEquation.lean` (kernel rfl)\n" ++
    "re-check every literal — the drift alarms. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  out := out ++ BfLitGen.emitDef "hhFromW1n" "Nat" s!"{n1}"
  out := out ++ BfLitGen.emitDef "hhFromW2n" "Nat" s!"{n2}"
  out := out ++ BfLitGen.emitDef "hhFromW3n" "Nat" s!"{n3}"
  out := out ++ BfLitGen.emitDef "hhFromMsgPtr" "Nat" s!"{msgPtr}"
  out := out ++ BfLitGen.emitDef "hhFromTgt" "Nat" s!"{tgt}"
  out := out ++ BfLitGen.emitDef "hhFromBacking" "Nat" s!"{backing}"
  out := out ++ BfLitGen.emitDef "hhFromS1" "SymState" (BfLitGen.pState S1)
  out := out ++ BfLitGen.emitDef "hhFromC1" "SymConfig" (BfLitGen.pC C1)
  out := out ++ BfLitGen.emitDef "hhFromS2" "SymState" (BfLitGen.pState S2)
  out := out ++ BfLitGen.emitDef "hhFromC2" "SymConfig" (BfLitGen.pC C2)
  out := out ++ BfLitGen.emitDef "hhFromS3" "SymState" (BfLitGen.pState S3)
  out := out ++ BfLitGen.emitDef "hhFromS4" "SymState" (BfLitGen.pState S4)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/HhFromLit.lean.gen" out
  IO.println s!"generated {out.length} chars"
  -- MACHINE validation
  let nTot := n1 + 1 + n2 + 1 + n3
  IO.println s!"total = {nTot}"
  for c in [0, 3, 31] do
    let σ0 := γS (HhFromGen.hfρ c) wBase HhFromGen.hfS0
    match stepFnIter nTot σ0 (γC (HhFromGen.hfρ c) hhC0) (c :: List.replicate 20 0) with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (HhFromGen.hfρ c) wBase S4
        IO.println s!"c={c}: stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"c={c}: ERROR {e.message.take 100}"
  -- projections at γ(S4), ints5 = 2
  let σ4 := γS (HhFromGen.hfρ 3) wBase S4
  let msgsStr : String := "msgs"
  let maaStr : String := "msgsAfterAppend"
  let raftTid : GoLean.TypeId := ⟨"raft.raft"⟩
  let voteStr : String := "Vote"
  IO.println s!"absOutbox(msgs) = {(toString (repr (absOutbox σ4 ⟨31⟩ msgsStr))).take 200}"
  IO.println s!"absOutbox(maa) = {(toString (repr (absOutbox σ4 ⟨31⟩ maaStr))).take 80}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σ4 ⟨31⟩ raftTid voteStr))}"
  IO.println s!"absRaftLog post = {(toString (repr (absRaftLog σ4 ⟨32⟩))).take 200}"
  IO.println s!"absMessage(arg) = {(toString (repr (absMessage σ4 (.addr (.base ⟨52⟩))))).take 240}"
