import GoLeanProofs

/-! # A4-U21 MsgAppRingGen — printer (BfLitGen, verbatim from HhGen) + ring generator -/

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

partial def pC : SymConfig → String
  | .exec stmt env k => s!"(GoLean.Sym.Config.exec {pr stmt} {pr env} {pK k})"
  | .evalE e env k => s!"(GoLean.Sym.Config.evalE {pr e} {pr env} {pK k})"
  | .retV v k => s!"(GoLean.Sym.Config.retV {pV v} {pK k})"
  | .next k => s!"(GoLean.Sym.Config.next {pK k})"
  | .breaking k => s!"(GoLean.Sym.Config.breaking {pK k})"
  | .continuing k => s!"(GoLean.Sym.Config.continuing {pK k})"
  | .returning k => s!"(GoLean.Sym.Config.returning {pK k})"
  | .breakingTo label k => s!"(GoLean.Sym.Config.breakingTo {pr label} {pK k})"
  | .continuingTo label k => s!"(GoLean.Sym.Config.continuingTo {pr label} {pK k})"
  | .panicking chain k => s!"(GoLean.Sym.Config.panicking {pList (chain.map pPE)} {pK k})"
  | .panicked msg => s!"(GoLean.Sym.Config.panicked {pr msg})"
  | .opDone sched inner => s!"(GoLean.Sym.Config.opDone {pr sched} {pC inner})"
  | _ => panic! "pC: unexpected config shape in this chain (FAIL-NOISY: emitted invalid token)" ++ " !!UNPRINTABLE_CONFIG!!"

def emitDef (name ty body : String) : String :=
  s!"def {name} : {ty} :=\n  {body}\n\n"

end BfLitGen

/-! # A4-U25: THE MSGVOTERESP ELECTION-COMPLETION FULL-ROUND GENERATOR — the real vote family
round, anchor to anchor (19,291 steps, 9 draws: the SEMANTIC delivery
pick @207 + 4 becomeFollower-reset mapIters @3522/3706/3735/3764 +
4 latitude appendSpills @10764/13408/15193/15243 — census
`artifacts/probe/votering.out`), mirrored in 13 windows with the U22
GENERALIZED DIFF-CROSSINGS template (crossing post-states are diffs
over the pre-states; spill post-configs share the pre continuation;
mapIter post-configs reflected + γ-checked — the template's uniform
crossing handling, U22 lesson (b)). Prints RoundVoteLit literals for
the canonical run behind the R-form's second instance. -/

namespace VoteGen
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def isAnchor : Config → Bool
  | .exec (.ifThenElse (Expr.lessCmp (Expr.var "round") (Expr.intLit 400 _)) _ _) _ _ => true
  | _ => false

partial def walkToAnchor (n : Nat) (σ : ExecState) (c : Config) (ch : Choices)
    (fuel : Nat) : Option (Nat × ExecState × Config × Choices) :=
  if fuel = 0 then none
  else if isAnchor c then some (n, σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkToAnchor (n+1) σ2 c2 ch2 (fuel-1)
    | .error _ => none

def findTwin2 (h : GoCore.Heap) : Option Loc :=
  h.findSome? (fun (l, c) =>
    if c.declaredTy == some (.defined ⟨"main.twin"⟩) then some l else none)

/-- Walk to the Nth loop-head anchor (anchor 3 = the first LEADER
anchor, per the AnchorScan probe). -/
partial def walkToAnchorN (rounds : Nat) (σ : ExecState) (c : Config)
    (ch : Choices) : Option (Nat × ExecState × Config × Choices) := do
  let (n, σA, cA, chA) ← walkToAnchor 0 σ c ch 300000
  if rounds = 0 then some (n, σA, cA, chA)
  else
    match stepFn σA cA chA with
    | .ok (c2, σ2, ch2) =>
        (walkToAnchorN (rounds - 1) σ2 c2 ch2).map
          (fun (m, s, cc, hh) => (n + 1 + m, s, cc, hh))
    | .error _ => none

/-- A4-U24: the doctored MsgAppResp, THE MAYBECOMMIT FAMILY
(TwinMarFixProbe's, verbatim): Type 4, To 1 (THE LEADER), From 2,
Term na+6 (1 = the leader's term), Index na+12 (2 = the becomeLeader
noop pending quorum), LogTerm nil, no entries, Reject nil. -/
def mvMsgVal (na : Nat) : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨na⟩)), ("To", .addr (.base ⟨na+1⟩)),
    ("From", .addr (.base ⟨na+2⟩)), ("Term", .addr (.base ⟨na+6⟩)),
    ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .nil), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def mvEntryVal (na : Nat) : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨na+7⟩)), ("Index", .addr (.base ⟨na+8⟩)),
    ("Type", .nil),
    ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def doctor (σ : ExecState) : Option ExecState := do
  let tl ← findTwin2 σ.heap
  let tc ← GoCore.Heap.lookup σ.heap tl
  let na := σ.nextAddr
  let tv' ← match tc.value with
    | .struct tid fs => some (GoValue.struct tid (fs.map (fun (q : String × GoValue) =>
        if q.1 == "net" then
          (q.1, .slice { base := some (.base ⟨na+4⟩), offset := 0, len := 1, cap := 1 })
        else if q.1 == "live" then
          (q.1, .slice { base := some (.base ⟨na+5⟩), offset := 0, len := 1, cap := 1 })
        else q)))
    | _ => none
  let heap' := GoCore.Heap.set σ.heap tl ⟨tc.declaredTy, tv'⟩ ++
    [(.base ⟨na⟩, ⟨some (.int .int32), .int 6 .int32⟩),
     (.base ⟨na+1⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+2⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+3⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), mvMsgVal na⟩),
     (.base ⟨na+4⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Message"⟩))),
        .array #[.addr (.base ⟨na+3⟩)]⟩),
     (.base ⟨na+5⟩, ⟨some (.array 1 .bool), .array #[.bool true]⟩),
     (.base ⟨na+6⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+7⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+8⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+9⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), mvEntryVal na⟩),
     (.base ⟨na+10⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
        .array #[.addr (.base ⟨na+9⟩)]⟩),
     (.base ⟨na+11⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+12⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]
  pure { σ with heap := heap', nextAddr := na + 13 }

/-- TwinVrFixProbe's printed read set (`vrfix.out`). -/
def keptCells : List Nat :=
  [15, 18, 27, 28, 57, 67, 110, 115, 121, 170, 179, 286, 295, 298,
   300, 349, 389, 1086, 1103, 1107, 1110, 1212, 1742, 1764, 1770,
   3369, 5058, 5198, 5661, 5666, 5669, 5672, 5675, 5758, 6070, 6072,
   8191, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201,
   8202, 8203]

def cfgHead (c : Config) : String :=
  match c with
  | .exec (.call _ fid _) _ _ => s!"call {fid.key}"
  | .retV _ (.stmtOpK (.appendSlice _) _ _ _ _ _) => "SPILL retV stmtOpK appendSlice"
  | .exec s _ _ => s!"exec {(toString (repr s)).take 60}"
  | .retV _ _ => "retV _"
  | .next _ => "next _"
  | _ => "other"

/-- Walk exactly k machine steps. -/
partial def walkN (σ : ExecState) (c : Config) (ch : Choices) (k : Nat) :
    Except String (ExecState × Config × Choices) :=
  if k = 0 then .ok (σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkN σ2 c2 ch2 (k-1)
    | .error e => .error s!"{e.message.take 200}"


/-- Positional heap diff (machine level): changed (loc, postCell) and
appended (loc, postCell). Fail-noisy on loc moves. -/
def heapDiff (pre post : GoCore.Heap) :
    IO (List (Loc × GoCore.HeapCell) × List (Loc × GoCore.HeapCell)) := do
  let common := min pre.length post.length
  let mut changed : List (Loc × GoCore.HeapCell) := []
  for i in [0:common] do
    match pre[i]?, post[i]? with
    | some (la, ca), some (lb, cb) =>
        if la != lb then
          IO.println s!"  DIFF LOC MOVE at {i} — UNSUPPORTED"
        else if ca.declaredTy != cb.declaredTy || ca.value != cb.value then
          changed := (lb, cb) :: changed
    | _, _ => IO.println "  DIFF index error"
  let mut appended : List (Loc × GoCore.HeapCell) := []
  if post.length > pre.length then
    for i in [pre.length:post.length] do
      match post[i]? with
      | some (lb, cb) => appended := (lb, cb) :: appended
      | none => IO.println "  DIFF append index error"
  if pre.length > post.length then IO.println "  DIFF SHRANK — UNSUPPORTED"
  return (changed.reverse, appended.reverse)

/-- Apply a reflected diff to a mirror state. -/
def applyDiff (S : SymState) (changed appended : List (Loc × GoCore.HeapCell))
    (naPost : Nat) : SymState :=
  let hSet := changed.foldl (fun h (lc : Loc × GoCore.HeapCell) =>
    GoLean.Sym.Heap.set h lc.1 (reflectCell symDom lc.2)) S.heap
  { heap := hSet ++ appended.map (fun (lc : Loc × GoCore.HeapCell) =>
      (lc.1, reflectCell symDom lc.2)),
    nextAddr := naPost }

def reflectS (σ : ExecState) : SymState :=
  { heap := reflectHeap symDom σ.heap, nextAddr := σ.nextAddr }


end VoteGen

open BfLitGen VoteGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let ρ0 : Valuation :=
    { ints := fun _ => 0, bools := fun _ => false,
      vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }
  let stream : Choices := List.replicate 25000 0
  match runProgramSetupM 20000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[] stream with
  | .error e => IO.println s!"SETUP ERROR: {e.message.take 300}"
  | .ok (c₀, s₃, _, ch₁) =>
  match VoteGen.walkToAnchorN 2 s₃ c₀ ch₁ with
  | none => IO.println "anchor not found"
  | some (nA, σA, cA, chA) =>
  match VoteGen.doctor σA with
  | none => IO.println "doctor failed"
  | some σD =>
  let σP := { σD with heap := σD.heap.filter (fun (l, _) =>
    match l with
    | .base b => VoteGen.keptCells.contains b.id
    | _ => true) }
  IO.println s!"fixture: anchor {nA}, {σP.heap.length} cells, na {σP.nextAddr}, ch {chA.length}"
  -- AUTO-DISCOVERED boundary schedule (A4-U23 template generalization):
  -- the mirror's own quit sites define the crossings (a choice census
  -- cannot see choice-FREE quit sites, e.g. mapIterK exhaustion-exit —
  -- the vote round's becomeFollower Visit loop, found at step 3793);
  -- windows are chunked at ≤2500 steps for module parallelism.
  let total := 33274
  let chunk := 2500
  let mut idx := 0
  let mut bIdx := 0            -- boundary name counter
  let mut S := VoteGen.reflectS σP
  let mut C := reflectC symDom cA
  let mut σ := σP
  let mut c := cA
  let mut ch := chA
  let mut boundaries : List (String × SymState × SymConfig) := [("B0", S, C)]
  let mut manifest : List String := []
  let mut allOk := true
  while idx < total && allOk do
    let budget := min chunk (total - idx)
    let (n, S', C') := symEvalWindowTB GoLean.RaftSeam.bfTB budget S C
    if n > 0 then
      -- machine to the same boundary + γ-check
      match VoteGen.walkN σ c ch n with
      | .error e => IO.println s!"MACHINE ERROR in window @{idx}+{n}: {e}"; allOk := false
      | .ok (σb, cb, chb) =>
        let σγ := γS ρ0 σP S'
        let hEq := σγ.heap == σb.heap
        let naEq := σγ.nextAddr == σb.nextAddr
        let cEq := toString (repr (γC ρ0 C')) == toString (repr cb)
        let preName := s!"B{bIdx}"
        let postName := s!"B{bIdx+1}"
        IO.println s!"  WIN {preName} --{n}--> {postName} @[{idx}..{idx+n}] γ={hEq}/{naEq}/{cEq}"
        if !hEq || !naEq || !cEq then allOk := false
        manifest := s!"SEG\t{preName}\t{n}\t{postName}" :: manifest
        boundaries := (postName, S', C') :: boundaries
        bIdx := bIdx + 1
        σ := σb; c := cb; ch := chb; S := S'; C := C'
        idx := idx + n
    if allOk && idx < total && n < budget then
      -- the mirror QUIT here: crossing (machine-step once, diff)
      match stepFn σ c ch with
      | .error e => IO.println s!"MACHINE ERROR at crossing @{idx}: {e.message.take 200}"; allOk := false
      | .ok (c2, σ2, ch2) =>
        let consumed := ch.length - ch2.length
        let (changed, appended) ← VoteGen.heapDiff σ.heap σ2.heap
        let preName := s!"B{bIdx}"
        let postName := s!"B{bIdx+1}"
        let (Cpost, kind) := match C with
          | .retV _ (.stmtOpK _ _ _ _ _ k') => ((.next k' : SymConfig), "spill")
          | _ => (reflectC symDom c2, "reflect")
        let Spost := VoteGen.applyDiff S changed appended σ2.nextAddr
        let σγp := γS ρ0 σP Spost
        let hEqP := σγp.heap == σ2.heap
        let naEqP := σγp.nextAddr == σ2.nextAddr
        let cEqP := toString (repr (γC ρ0 Cpost)) == toString (repr c2)
        IO.println s!"  CROSS {preName} -> {postName} @[{idx}] consumed={consumed} kind={kind} changed={changed.length} appended={appended.length} γ={hEqP}/{naEqP}/{cEqP} :: {VoteGen.cfgHead c}"
        if !hEqP || !naEqP || !cEqP then allOk := false
        manifest := s!"CROSS\t{preName}\t{postName}\t{consumed}\t{kind}" :: manifest
        boundaries := (postName, Spost, Cpost) :: boundaries
        bIdx := bIdx + 1
        σ := σ2; c := c2; ch := ch2; S := Spost; C := Cpost
        idx := idx + 1
  if !allOk then IO.println "PROPAGATION FAILED — not printing"; return
  IO.println s!"vote-round propagation γ-valid; {bIdx} boundaries past B0; final idx={idx}"
  IO.println "=== MANIFEST (in order) ==="
  for line in manifest.reverse do IO.println line
  -- print literals
  let hdrCommon := "import GoLeanProofs.Sym.Mirror\n\n/-! GENERATED (A4-U25; `artifacts/probe/RoundVrGen.lean` — DO NOT\nEDIT BY HAND). The MsgVoteResp ELECTION-COMPLETION FULL-ROUND\nliterals (anchor 2 to anchor 3: the CANDIDATE handles the\nquorum-completing VoteResp — becomeLeader + the noop append +\nbcastAppend), boundary schedule AUTO-DISCOVERED from the mirror's\nown quit sites (the U23 template).\nThe window LINK theorems in `RoundVrEq*.lean` re-check every\nliteral against the mirror. -/\n\nnamespace GoLean.RaftSeam.RoundVr\n\nopen GoLean GoLean.GoCore GoLean.Sym\n\nset_option maxRecDepth 8000000\n\n"
  let ordered := boundaries.reverse
  let mut out := hdrCommon
  let mut fileNo := 1
  let mut inFile := 0
  for (nm, Sx, Cx) in ordered do
    out := out ++ BfLitGen.emitDef s!"vrS{nm}" "SymState" (BfLitGen.pState Sx)
    out := out ++ BfLitGen.emitDef s!"vrC{nm}" "SymConfig" (BfLitGen.pC Cx)
    inFile := inFile + 1
    if inFile ≥ 5 then
      out := out ++ "end GoLean.RaftSeam.RoundVr\n"
      IO.FS.writeFile s!"../artifacts/probe/gen/RoundVrLit{fileNo}.lean.gen" out
      IO.println s!"written RoundVrLit{fileNo}.lean.gen: {out.length} chars"
      out := hdrCommon
      fileNo := fileNo + 1
      inFile := 0
  if inFile > 0 then
    out := out ++ "end GoLean.RaftSeam.RoundVr\n"
    IO.FS.writeFile s!"../artifacts/probe/gen/RoundVrLit{fileNo}.lean.gen" out
    IO.println s!"written RoundVrLit{fileNo}.lean.gen: {out.length} chars"
  IO.println s!"END: na={σ.nextAddr} heap={σ.heap.length} chConsumed={chA.length - ch.length}"
