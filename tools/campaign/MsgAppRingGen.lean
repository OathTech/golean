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


/-! # A4-U21 (C2c): THE MSGAPP RING GENERATOR
Builds the append-family MsgApp round fixture (TwinMsgAppFixProbe's
doctor + its 39-cell prune), walks to the RING START (7,425 steps =
the `main.twin.harvest` call), prunes AGAIN from there (the ring's own
read-before-write footprint — the I2 footprint-for-preconditions
census), then walks the 13,870-step ring concretely, reflecting
boundary/crossing states into Sym-domain literals and printing them
as `RingLit.lean` defs. The mirror is verified segment-by-segment
against the machine (pState string equality — the honest coverage
test the U18/U20 ledger rows owed). -/

namespace RingGen
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

def maMsgVal (na : Nat) : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨na⟩)), ("To", .addr (.base ⟨na+1⟩)),
    ("From", .addr (.base ⟨na+2⟩)), ("Term", .nil),
    ("LogTerm", .addr (.base ⟨na+11⟩)), ("Index", .addr (.base ⟨na+12⟩)),
    ("Entries", .slice { base := some (.base ⟨na+10⟩), offset := 0, len := 1, cap := 1 }),
    ("Commit", .addr (.base ⟨na+6⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def maEntryVal (na : Nat) : GoValue :=
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
    [(.base ⟨na⟩, ⟨some (.int .int32), .int 3 .int32⟩),
     (.base ⟨na+1⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+2⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+3⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), maMsgVal na⟩),
     (.base ⟨na+4⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Message"⟩))),
        .array #[.addr (.base ⟨na+3⟩)]⟩),
     (.base ⟨na+5⟩, ⟨some (.array 1 .bool), .array #[.bool true]⟩),
     (.base ⟨na+6⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+7⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+8⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
     (.base ⟨na+9⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), maEntryVal na⟩),
     (.base ⟨na+10⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
        .array #[.addr (.base ⟨na+9⟩)]⟩),
     (.base ⟨na+11⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
     (.base ⟨na+12⟩, ⟨some (.int .uint64), .int 1 .uint64⟩)]
  pure { σ with heap := heap', nextAddr := na + 13 }

/-- TwinMsgAppFixProbe's printed 39-cell read set. -/
def keptCells : List Nat :=
  [15, 25, 27, 28, 57, 110, 121, 170, 1764, 1770, 1779, 1886, 1895,
   1898, 1900, 1949, 1989, 3342, 3344, 3351, 3354, 3357, 3360, 3369,
   6070, 6072, 6073, 6074, 6075, 6076, 6077, 6078, 6079, 6080, 6081,
   6082, 6083, 6084, 6085]

/-- Walk exactly k steps (concrete). -/
partial def walkN (σ : ExecState) (c : Config) (ch : Choices) (k : Nat) :
    Except String (ExecState × Config × Choices) :=
  if k = 0 then .ok (σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkN σ2 c2 ch2 (k-1)
    | .error e => .error s!"{e.message.take 200}"

/-- The ring END predicate: the `main.twin.projection` call config. -/
def isRingEnd : Config → Bool
  | .exec (.call _ ⟨"main.twin.projection"⟩ _) _ _ => true
  | _ => false

partial def walkToRingEnd (n : Nat) (σ : ExecState) (c : Config) (ch : Choices)
    (fuel : Nat) : Except String (Nat × ExecState × Config × Choices) :=
  if fuel = 0 then .error "OUT OF FUEL"
  else if isRingEnd c then .ok (n, σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkToRingEnd (n+1) σ2 c2 ch2 (fuel-1)
    | .error e => .error s!"@{n}: {e.message.take 200}"

def parseUnbound (msg : String) : Option Nat := do
  let parts := msg.splitOn "id := "
  if parts.length < 2 then none else
  let tail := parts[1]!
  let digits := tail.toList.takeWhile Char.isDigit
  if digits.isEmpty then none else (String.ofList digits).toNat?

/-- Ring-scoped prune loop (walks to the projection call). -/
partial def pruneLoop (full : ExecState) (c0 : Config) (ch : Choices)
    (kept : List Nat) (iter : Nat) : IO (List Nat) := do
  if iter > 1500 then IO.println "PRUNE: iteration cap"; return kept
  let heap' := full.heap.filter (fun (l, _) =>
    match l with
    | .base b => kept.contains b.id
    | _ => true)
  let σ' := { full with heap := heap' }
  match walkToRingEnd 0 σ' c0 ch 20000 with
  | .ok (n, _, _, _) =>
      IO.println s!"RING PRUNE done: kept={kept.length} cells, ring steps={n} (iter {iter})"
      return kept
  | .error e =>
      match parseUnbound e with
      | some cellId =>
          if kept.contains cellId then
            IO.println s!"RING PRUNE stuck (cell {cellId} kept): {e.take 150}"
            return kept
          else pruneLoop full c0 ch (cellId :: kept) (iter + 1)
      | none =>
          IO.println s!"RING PRUNE unparseable: {e.take 250}"
          return kept

def reflectS (σ : ExecState) : SymState :=
  { heap := reflectHeap symDom σ.heap, nextAddr := σ.nextAddr }

/-- The named schedule (ring-relative indices from the census
`artifacts/probe/msgappring.out`, fixture indices minus 7,425). -/
def sched : List (Nat × String) := [
  (0, "0"), (3257, "P1a"), (3258, "P1b"), (3327, "1"),
  (5185, "P2a"), (5186, "P2b"), (7958, "P3a"), (7959, "P3b"),
  (8321, "P4a"), (8322, "P4b"), (8371, "P5a"), (8372, "P5b"),
  (8512, "2"), (8836, "3"), (12038, "4"), (13870, "5")]

def cfgHead (c : Config) : String :=
  match c with
  | .exec (.call _ fid _) _ _ => s!"call {fid.key}"
  | .retV _ (.stmtOpK (.appendSlice _) _ _ _ _ _) => "SPILL retV stmtOpK appendSlice"
  | .exec s _ _ => s!"exec {(toString (repr s)).take 60}"
  | .retV _ _ => "retV _"
  | .next _ => "next _"
  | _ => "other"

/-- Walk the ring, saving (σ, c) at scheduled indices. -/
partial def walkCollect (n : Nat) (σ : ExecState) (c : Config) (ch : Choices)
    (stopAt : Nat) (acc : List (String × ExecState × Config)) :
    IO (List (String × ExecState × Config)) := do
  let acc ← match sched.find? (fun (i, _) => i == n) with
    | some (_, name) => do
        IO.println s!"  @[{n}] {name}: na={σ.nextAddr} heap={σ.heap.length} ch={ch.length} :: {cfgHead c}"
        pure ((name, σ, c) :: acc)
    | none => pure acc
  if n == stopAt then return acc.reverse
  match stepFn σ c ch with
  | .ok (c2, σ2, ch2) => walkCollect (n+1) σ2 c2 ch2 stopAt acc
  | .error e => IO.println s!"WALK ERROR @{n}: {e.message.take 150}"; return acc.reverse

end RingGen

open BfLitGen RingGen GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface GoLean.RaftSeam in
#eval show IO Unit from do
  IO.FS.createDirAll "../artifacts/probe/gen"
  let ρ0 : Valuation :=
    { ints := fun _ => 0, bools := fun _ => false,
      vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }
  -- 1. fixture + walk to ring start
  let stream : Choices := List.replicate 25000 0
  match runProgramSetupM 20000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[] stream with
  | .error e => IO.println s!"SETUP ERROR: {e.message.take 300}"
  | .ok (c₀, s₃, _, ch₁) =>
  match RingGen.walkToAnchor 0 s₃ c₀ ch₁ 200000 with
  | none => IO.println "anchor not found"
  | some (nA, σA, cA, chA) =>
  match RingGen.doctor σA with
  | none => IO.println "doctor failed"
  | some σD =>
  let σP := { σD with heap := σD.heap.filter (fun (l, _) =>
    match l with
    | .base b => RingGen.keptCells.contains b.id
    | _ => true) }
  match RingGen.walkN σP cA chA 7425 with
  | .error e => IO.println s!"to-ring-start FAILED: {e}"
  | .ok (σR, cR, chR) =>
  let ringKept : List Nat :=
    [15, 57, 121, 1770, 1779, 1895, 1898, 1900, 1949, 1989, 3342, 3344,
     3351, 3354, 3357, 3360, 6075, 6077, 6078, 6080, 6081, 6082, 6132,
     6138, 6424, 6456, 6499]
  let σRP := { σR with heap := σR.heap.filter (fun (l, _) =>
    match l with
    | .base b => ringKept.contains b.id
    | _ => true) }
  IO.println s!"ring start pruned: na={σRP.nextAddr} heap={σRP.heap.length}"
  -- 2. concrete boundary collection
  let states ← RingGen.walkCollect 0 σRP cR chR 13870 []
  if states.length != RingGen.sched.length then
    IO.println s!"COLLECT MISMATCH: {states.length}"; return
  let get := fun (name : String) =>
    (states.find? (fun (n, _, _) => n == name)).getD ("MISSING", σRP, cR)
  -- 3. MIRROR PROPAGATION with γ-fidelity validation at every boundary
  let segs : List (String × Nat × String) := [
    ("0", 3257, "P1a"), ("P1b", 69, "1"), ("1", 1858, "P2a"),
    ("P2b", 2772, "P3a"), ("P3b", 362, "P4a"), ("P4b", 49, "P5a"),
    ("P5b", 140, "2"), ("2", 324, "3"), ("3", 3202, "4"),
    ("4", 1832, "5")]
  let mut mstates : List (String × SymState × SymConfig) :=
    [("0", RingGen.reflectS σRP, reflectC symDom cR)]
  let mut allOk := true
  let mget := fun (ms : List (String × SymState × SymConfig)) (name : String) =>
    (ms.find? (fun (n, _, _) => n == name)).getD
      ("MISSING", RingGen.reflectS σRP, reflectC symDom cR)
  for (a, len, b) in segs do
    let (an, Sa, Ca) := mget mstates a
    if an == "MISSING" then IO.println s!"missing mirror {a}"; allOk := false
    let (_, σb, cb) := get b
    let (n, S', C') := symEvalWindowTB GoLean.RaftSeam.bfTB len Sa Ca
    -- γ-fidelity: the mirror boundary state's image is the machine state
    let σγ := γS ρ0 σRP S'
    let hEq := σγ.heap == σb.heap
    let naEq := σγ.nextAddr == σb.nextAddr
    let cEq := toString (repr (γC ρ0 C')) == toString (repr cb)
    IO.println s!"  {a} --{len}--> {b}: n={n} γheap={hEq} γna={naEq} γcfg={cEq}"
    if n != len || !hEq || !naEq || !cEq then allOk := false
    -- crossing? PROPAGATE THROUGH: post = set/append over the mirror pre
    -- (machine order: alloc-append the backing, then store the target) —
    -- untouched cells stay the SAME terms, so the crossing kernel_rfl
    -- compares them syntactically (the tree-vs-literal γ-evaluation pit
    -- of the reflect-reset form, measured at >46 min/crossing, is gone).
    if b.endsWith "a" && b.startsWith "P" then
      let postName := String.ofList b.toList.dropLast ++ "b"
      let (_, σpost, _) := get postName
      match C' with
      | .retV _ (.stmtOpK _ _ done _ _ k') =>
          -- target loc from the done list [old, .addr tloc]
          let tlocOpt := match done with
            | [_, .addr tloc] => some tloc
            | _ => none
          match tlocOpt with
          | none => IO.println s!"  {b}: done list shape unexpected"; allOk := false
          | some tloc =>
            let backLoc : Loc := .base ⟨S'.nextAddr⟩
            match GoCore.Heap.lookup σpost.heap backLoc,
                  GoCore.Heap.lookup σpost.heap tloc with
            | some backM, some tgtM =>
                let backC := reflectCell symDom backM
                let tgtC := reflectCell symDom tgtM
                let Spost : SymState :=
                  { heap := GoLean.Sym.Heap.set (S'.heap ++ [(backLoc, backC)]) tloc tgtC,
                    nextAddr := S'.nextAddr + 1 }
                -- immediate γ-fidelity of the propagated post
                let σγp := γS ρ0 σRP Spost
                let hEqP := σγp.heap == σpost.heap
                let naEqP := σγp.nextAddr == σpost.nextAddr
                IO.println s!"  {b}->post: γheap={hEqP} γna={naEqP}"
                if !hEqP || !naEqP then allOk := false
                mstates := (postName, Spost, .next k') :: (b, S', C') :: mstates
            | _, _ => IO.println s!"  {b}: post cells missing"; allOk := false
      | _ =>
          IO.println s!"  {b}: quit config NOT a stmtOpK spill!"; allOk := false
    else
      mstates := (b, S', C') :: mstates
  if !allOk then IO.println "MIRROR PROPAGATION FAILED — not printing"; return
  IO.println "mirror propagation γ-valid at all 16 boundaries"
  -- 4. print literals (the MIRROR chain's states — kernel-rfl coherent)
  let mut out := "import GoLeanProofs.Specs.TwinProgram\nimport GoLeanProofs.Sym.SpillTransport\nimport GoLeanProofs.Specs.Raft.HandlerEqSym\n\n"
  out := out ++ "/-! # RingLit — GENERATED literals (A4-U21 C2c; generator\n"
  out := out ++ "`artifacts/probe/MsgAppRingGen.lean` — DO NOT EDIT BY HAND).\n\n"
  out := out ++ "The MsgApp append-family ROUND fixture's harvest-ring segment\n"
  out := out ++ "(ring step 0 = the `main.twin.harvest` call, 7,425 steps into the\n"
  out := out ++ "round; 13,870 ring steps to the `main.twin.projection` call),\n"
  out := out ++ "pruned to the ring's own 27-cell read-before-write footprint,\n"
  out := out ++ "MIRROR-PROPAGATED (states carry unreduced SymInt trees — the\n"
  out := out ++ "mirror does no constant folding; γ evaluates them) with crossing\n"
  out := out ++ "resets to the reflected machine post-states. γ-fidelity against\n"
  out := out ++ "the machine walk was generator-verified at every boundary;\n"
  out := out ++ "the window LINK theorems in RingEquation.lean (kernel rfl)\n"
  out := out ++ "re-check every literal against the mirror — the drift alarms. -/\n\n"
  out := out ++ "namespace GoLean.RaftSeam.Ring\n\n"
  out := out ++ "open GoLean GoLean.GoCore GoLean.Sym\n\n"
  out := out ++ "set_option maxRecDepth 8000000\n\n"
  let names : List String := ["0", "P1a", "P1b", "1", "P2a", "P2b",
    "P3a", "P3b", "P4a", "P4b", "P5a", "P5b", "2", "3", "4", "5"]
  for nm in names do
    let (fnd, Sx, Cx) := mget mstates nm
    if fnd == "MISSING" then IO.println s!"PRINT MISSING {nm}"; return
    out := out ++ BfLitGen.emitDef s!"maS{nm}" "SymState" (BfLitGen.pState Sx)
    out := out ++ BfLitGen.emitDef s!"maC{nm}" "SymConfig" (BfLitGen.pC Cx)
  out := out ++ "end GoLean.RaftSeam.Ring\n"
  IO.FS.writeFile "../artifacts/probe/gen/RingLit.lean.gen" out
  IO.println s!"written RingLit.lean.gen: {out.length} chars"
  -- 5. crossing metadata from the MIRROR quit configs
  for nm in ["P1a", "P2a", "P3a", "P4a", "P5a"] do
    let (_, Sx, Cx) := mget mstates nm
    match Cx with
    | .retV ev (.stmtOpK (.appendSlice elem) nt done _ _ _) =>
        let doneStr := String.intercalate " || " (done.map (fun v => ((BfLitGen.pV v).take 120).toString))
        IO.println s!"  {nm}: elem={(toString (repr elem)).take 90} nt={nt} retV={(BfLitGen.pV ev).take 140} done={doneStr} na={Sx.nextAddr}"
    | _ => IO.println s!"  {nm}: unexpected"
  -- 6. endpoint observables
  let (_, σ5, _) := get "5"
  let (_, σ0, _) := get "0"
  IO.println s!"b0: na={σ0.nextAddr}; b5: na={σ5.nextAddr}; ch consumed in ring: 5"
