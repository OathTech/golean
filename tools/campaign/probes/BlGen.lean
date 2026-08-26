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



/-! ## The becomeLeader chain (A4-U13 slice 2): the Bf31 reset spine
(4 picks + range-stop + sort) + the La tail (spill/len/spill).
Fixture: bf31 heap at state = CONCRETE 1 (candidate; the panic guard
branches on it), Vote/lead/ldT symbolic vars 1/2/4, na₀ = 52, no
static complement (census: the path reads none). Windows (walker,
validated): [659,183,28,28,28,3,4236,83,1096,113]; crossings pick₅,
pick₆, pick₇, pick₈, range-stop, sort, spill(atoms 0: tgt 328,
backing 329), len := 1, spill(atoms 1: tgt 395, backing 396). -/

namespace BlGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def blSymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (renameValue shBfc' (uRaftVal 0 0 1 0)))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def blSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 1 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (renameLoc shBfc' l, .mk c.declaredTy blSymRaft)
    else (renameLoc shBfc' l,
      .mk c.declaredTy (embedGo (renameValue shBfc' c.value))))

def blS0 : SymState := { heap := blSymHeap, nextAddr := 52 }

def blC0 : SymConfig :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomeLeader"⟩ [] [] [] [] .stop)

-- concrete machine fixture (Vote 7 lead 2 state 1 ldT 5)
def blHeapC : GoCore.Heap :=
  (uHeap 7 2 1 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))
def blσ0C : ExecState := { wBase with heap := blHeapC, nextAddr := 52 }
def blC0C : Machine.Config :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomeLeader"⟩ [] [] [] [] .stop)

def blCap (c : Nat) : Nat := GoLean.SliceMem.appendRealizedCap 0 1 (c % 32)

end BlGen

open BfLitGen BlGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let header := "import GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.Bf31\n\n" ++
    "/-! # A4-U13 (GENERATED — DO NOT EDIT BY HAND)\n\n" ++
    "The becomeLeader chain's window-output states/configs as SOURCE\n" ++
    "LITERALS, generated by `artifacts/probe/BlGen.lean` (fixture: the\n" ++
    "bf31 heap at state = 1, vars 1/2/4; the Bf31 reset spine + the La\n" ++
    "tail; value/cell atoms 0 = the unstable.entries append spill,\n" ++
    "atoms 1 = the msgsAfterAppend self-ack spill). Correctness: the\n" ++
    "window LINK theorems in `BlEquation.lean` (kernel rfl) re-check\n" ++
    "every literal — the drift alarms; regenerate on any fixture\n" ++
    "change. -/\n\n" ++
    "namespace GoLean.RaftSeam\n\n" ++
    "open GoLean GoLean.GoCore GoLean.Sym\n\n" ++
    "set_option maxRecDepth 1000000\n\n"
  let mut out := header
  let mut S := BlGen.blS0
  let mut C := BlGen.blC0
  -- W1..W6 + spine crossings (pick 5/6/7/8, stop, sort)
  let expects : List Nat := [659, 183, 28, 28, 28, 3]
  let crossings : List (String × Nat) :=
    [("pick", 5), ("pick", 6), ("pick", 7), ("pick", 8), ("stop", 0), ("sort", 0)]
  let mut idx := 1
  for ((exp, (kindS, var)), _) in (expects.zip crossings).zip (List.range 6) do
    let (n, S', C') := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S C
    IO.println s!"w{idx}: {n} steps (expect {exp}); na={S'.nextAddr}"
    out := out ++ BfLitGen.emitDef s!"blS{idx}" "SymState" (BfLitGen.pState S')
    out := out ++ BfLitGen.emitDef s!"blC{idx}" "SymConfig" (BfLitGen.pC C')
    if kindS == "pick" then
      let kind : IntKind := if var == 5 then .int else .uint64
      let (S2, C2) := uCrossPick var kind S' C'
      S := S2; C := C2
    else if kindS == "stop" then
      let (S2, C2) := uCrossStop S' C'
      S := S2; C := C2
    else
      let (S2, C2) := uCrossSort S' C'
      S := S2; C := C2
    idx := idx + 2
  -- W7 → spill A (atoms 0)
  let (n7, S13, C13) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S C
  IO.println s!"w7: {n7} steps (expect 4236); na={S13.nextAddr}"
  out := out ++ BfLitGen.emitDef "blS13" "SymState" (BfLitGen.pState S13)
  out := out ++ BfLitGen.emitDef "blC13" "SymConfig" (BfLitGen.pC C13)
  let k13 := match C13 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  -- spill-1 operands + elems element
  let (tgt1, elems1) := match C13 with
    | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK _ _ done _ _ _) =>
        ((match done with
          | [_, GoLean.Sym.Value.addr (.base a)] => a.id
          | _ => 0),
         (match sv.base with | some (.base b) => b.id | _ => 0))
    | _ => (0, 0)
  let e1 : String := match GoLean.Sym.Heap.lookup S13.heap (.base ⟨elems1⟩) with
    | some (.mk _ (.array vs)) => (vs.toList.map BfLitGen.pV).headD "NONE"
    | _ => "ODD"
  IO.println s!"spill-1: tgt={tgt1} elems={elems1} element0={e1} backing at {S13.nextAddr}"
  let S14 : SymState :=
    { heap := (GoLean.Sym.Heap.set S13.heap (.base ⟨tgt1⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))))
          (.atom 0))) ++ [(.base ⟨S13.nextAddr⟩, .atom 0)],
      nextAddr := S13.nextAddr + 1 }
  out := out ++ BfLitGen.emitDef "blS14" "SymState" (BfLitGen.pState S14)
  -- W8 → LEN
  let (n8, S15, C15) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S14 (.next k13)
  IO.println s!"w8: {n8} steps (expect 83); na={S15.nextAddr}"
  out := out ++ BfLitGen.emitDef "blS15" "SymState" (BfLitGen.pState S15)
  out := out ++ BfLitGen.emitDef "blC15" "SymConfig" (BfLitGen.pC C15)
  let kLen := match C15 with
    | .retV _ (.strictK _ _ _ _ k') => k'
    | _ => .stop
  -- W9 → spill B (atoms 1)
  let (n9, S17, C17) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S15
    (.retV (.int (.lit 1) .int) kLen)
  IO.println s!"w9: {n9} steps (expect 1096); na={S17.nextAddr}"
  out := out ++ BfLitGen.emitDef "blS17" "SymState" (BfLitGen.pState S17)
  out := out ++ BfLitGen.emitDef "blC17" "SymConfig" (BfLitGen.pC C17)
  let k17 := match C17 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let (tgt2, elems2) := match C17 with
    | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK _ _ done _ _ _) =>
        ((match done with
          | [_, GoLean.Sym.Value.addr (.base a)] => a.id
          | _ => 0),
         (match sv.base with | some (.base b) => b.id | _ => 0))
    | _ => (0, 0)
  let e2 : String := match GoLean.Sym.Heap.lookup S17.heap (.base ⟨elems2⟩) with
    | some (.mk _ (.array vs)) => (vs.toList.map BfLitGen.pV).headD "NONE"
    | _ => "ODD"
  IO.println s!"spill-2: tgt={tgt2} elems={elems2} element0={e2} backing at {S17.nextAddr}"
  let S18 : SymState :=
    { heap := (GoLean.Sym.Heap.set S17.heap (.base ⟨tgt2⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 1))) ++ [(.base ⟨S17.nextAddr⟩, .atom 1)],
      nextAddr := S17.nextAddr + 1 }
  out := out ++ BfLitGen.emitDef "blS18" "SymState" (BfLitGen.pState S18)
  -- W10 → stop
  let (n10, S19, C19) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S18 (.next k17)
  let stop19 := match C19 with | GoLean.Sym.Config.next .stop => true | _ => false
  IO.println s!"w10: {n10} steps (expect 113); ends at stop: {stop19}"
  out := out ++ BfLitGen.emitDef "blS19" "SymState" (BfLitGen.pState S19)
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "../artifacts/probe/gen/BlLit.lean.gen" out
  IO.println s!"total generated size: {out.length} chars"

-- MACHINE VALIDATION (γ-agreement at the final literal + projections)
open BfLitGen BlGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
def blρw (c5 c6 : Nat) : Valuation :=
  { ints := fun i =>
      if i = 1 then 7 else if i = 2 then 2 else if i = 4 then 5
      else if i = 5 then 3 else if i = 6 then 2 else if i = 7 then 1
      else if i = 8 then 3 else 0
    bools := fun _ => false
    vals := fun i =>
      if i = 0 then .slice ⟨some (.base ⟨329⟩), 0, 1, BlGen.blCap c5⟩
      else if i = 1 then .slice ⟨some (.base ⟨396⟩), 0, 1, BlGen.blCap c6⟩
      else .nil
    cells := fun i =>
      if i = 0 then ⟨some (.array (BlGen.blCap c5) (.pointer (.defined ⟨"raftpb.Entry"⟩))),
        .array ⟨[.addr (.base ⟨287⟩)] ++ List.replicate (BlGen.blCap c5 - 1) .nil⟩⟩
      else if i = 1 then ⟨some (.array (BlGen.blCap c6) (.pointer (.defined ⟨"raftpb.Message"⟩))),
        .array ⟨[.addr (.base ⟨353⟩)] ++ List.replicate (BlGen.blCap c6 - 1) .nil⟩⟩
      else ⟨none, .nil⟩ }

open BfLitGen BlGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  -- recompute the final literal (cheap, compiled) to compare against
  let mut S := BlGen.blS0
  let mut C := BlGen.blC0
  for (kindS, var) in [("pick", 5), ("pick", 6), ("pick", 7), ("pick", 8), ("stop", 0), ("sort", 0)] do
    let (_, S', C') := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S C
    if kindS == "pick" then
      let kind : IntKind := if var == 5 then .int else .uint64
      let (S2, C2) := uCrossPick var kind S' C'
      S := S2; C := C2
    else if kindS == "stop" then
      let (S2, C2) := uCrossStop S' C'
      S := S2; C := C2
    else
      let (S2, C2) := uCrossSort S' C'
      S := S2; C := C2
  let (_, S13, C13) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S C
  let k13 := match C13 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let S14 : SymState :=
    { heap := (GoLean.Sym.Heap.set S13.heap (.base ⟨328⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))))
          (.atom 0))) ++ [(.base ⟨329⟩, .atom 0)],
      nextAddr := 330 }
  let (_, S15, C15) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S14 (.next k13)
  let kLen := match C15 with
    | .retV _ (.strictK _ _ _ _ k') => k'
    | _ => .stop
  let (_, S17, C17) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S15
    (.retV (.int (.lit 1) .int) kLen)
  let k17 := match C17 with
    | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
    | _ => .stop
  let S18 : SymState :=
    { heap := (GoLean.Sym.Heap.set S17.heap (.base ⟨395⟩)
        (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))))
          (.atom 1))) ++ [(.base ⟨396⟩, .atom 1)],
      nextAddr := 397 }
  let (_, S19, _) := symEvalWindowTB GoLean.RaftSeam.bfTB 30000 S18 (.next k17)
  for (c5, c6) in [(0, 0), (3, 5), (31, 31)] do
    let stream : Choices := [3, 1, 0, 0, c5, c6] ++ List.replicate 40 0
    match stepFnIter 6466 BlGen.blσ0C BlGen.blC0C stream with
    | .ok (cM, σM, chM) =>
        let stop := match cM with | Machine.Config.next .stop => true | _ => false
        let γfin := γS (blρw c5 c6) BlGen.blσ0C S19
        IO.println s!"(c5,c6)=({c5},{c6}): stop={stop} chLeft={chM.length} heapEq={σM.heap == γfin.heap} naEq={σM.nextAddr == γfin.nextAddr}"
    | .error e => IO.println s!"({c5},{c6}): machine ERROR {e.message.take 120}"
  -- projections at γ(S19)
  let σf := γS (blρw 3 5) BlGen.blσ0C S19
  let maaStr : String := "msgsAfterAppend"
  let msgsStr : String := "msgs"
  IO.println s!"absOutbox(msgsAfterAppend) = {toString (repr (absOutbox σf ⟨31⟩ maaStr))}"
  IO.println s!"absOutbox(msgs) = {toString (repr (absOutbox σf ⟨31⟩ msgsStr))}"
  IO.println s!"absRaftLog post = {toString (repr (absRaftLog σf ⟨32⟩))}"
  IO.println s!"absRaftLog pre = {toString (repr (absRaftLog (γS (blρw 3 5) BlGen.blσ0C BlGen.blS0) ⟨32⟩))}"
  IO.println s!"respMsg(353) = {toString (repr (absMessage σf (.addr (.base ⟨353⟩)))) |>.take 260}"
  IO.println s!"Vote = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "Vote"))}"
  IO.println s!"lead = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "lead"))}"
  IO.println s!"state = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "state"))}"
  IO.println s!"pendingConfIndex = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "pendingConfIndex"))}"
  IO.println s!"Term = {toString (repr (GoLean.Lens.fieldReadU64 σf ⟨31⟩ ⟨"raft.raft"⟩ "Term"))}"
