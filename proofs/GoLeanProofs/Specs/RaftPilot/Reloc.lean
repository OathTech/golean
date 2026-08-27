import GoLeanProofs.Specs.RaftPilot.BfFixture

/-!
# W2 unit 4: the TRACKED, layout-compliant fixture mechanism —
relocation-as-definition (the F6 lesson, closed structurally)

W1 finding 3 (design note §3): `bodies_inv` forces every
transport-admissible ρ to fix the twin's 31 static addresses
(`.base ⟨0⟩ … ⟨30⟩`, wire declaration order — `seedGlobals`' pin), so
the arc4d pilot fixture (raft cell at `⟨0⟩`, nextAddr 21) is
CANONICAL-ONLY: no nonempty-frame `FrameSim` image of it exists
(`ShiftSpec.alloc_reg` caps the identity region at the fixture's
`nextAddr`). The COMPLIANT layout reserves `[0, 31)` for the statics
and packs fixture cells from `⟨31⟩`; the frame gap then sits above
the fixture top, where a caller's locals live.

**The mechanism** (an [AGENT]-recorded deviation from the "generator
in `tools/`" spelling, STRICTLY STRONGER under the F6 rule): instead
of an emitter producing literal source (the untracked-generator
failure class — registry Finding #3), the compliant fixture is
DEFINED as a computable RELOCATION of the existing tracked literals:
`rAddr` fixes the one true static the span touches (`⟨18⟩`,
`raft.globalRand` — already at its true address in the arc4d layout)
and shifts every other cell by +31. Nothing is generated, nothing is
untracked, and the window LINK theorems (`CBfFixture.lean`, kernel
`rfl` against the evaluator) re-check the relocated chain exactly as
they checked the original — the drift alarms are preserved. Code
payloads (Stmt/Expr/plans) are NEVER touched — the relocation moves
DATA addresses only, which is precisely what `bodies_inv` demands.

`symPlugK`/`symPlugC` are the Sym-level analogue of the plug rule's
replacement (`Frame/Plug.lean`): they install an OPEN caller context
at the (closed) relocated chain's barrier frame, giving the
continuation-parametric compliant configs.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.Sym

/-- The relocation address map: the true static stays; everything
else shifts above the reserved global region. -/
def rAddr (a : Nat) : Nat := if a = 18 then 18 else a + 31

def relocLoc : Loc → Loc
  | .base ⟨a⟩ => .base ⟨rAddr a⟩
  | .field b tid f => .field (relocLoc b) tid f
  | .index b i => .index (relocLoc b) i

def relocSlice (s : SliceValue) : SliceValue :=
  { s with base := s.base.map relocLoc }

def relocMap (m : MapValue) : MapValue :=
  { m with base := m.base.map relocLoc }

def relocChan (c : ChanValue) : ChanValue :=
  { c with base := c.base.map relocLoc }

def relocV : SymValue → SymValue
  | .unit => .unit
  | .bool b => .bool b
  | .int v kind => .int v kind
  | .float bits kind => .float bits kind
  | .string s => .string s
  | .addr loc => .addr (relocLoc loc)
  | .nil => .nil
  | .interface dyn v => .interface dyn (relocV v)
  | .struct tid fields => .struct tid (fields.attach.map
      (fun ⟨(name, v), _⟩ => (name, relocV v)))
  | .array vs => .array (vs.attach.map (fun ⟨v, _⟩ => relocV v))
  | .slice v => .slice (relocSlice v)
  | .map v => .map (relocMap v)
  | .mapData entries => .mapData (entries.attach.map
      (fun ⟨(k, v), _⟩ => (relocV k, relocV v)))
  | .chan v => .chan (relocChan v)
  | .chanData buf cap closed =>
      .chanData (buf.attach.map (fun ⟨v, _⟩ => relocV v)) cap closed
  | .funcVal fid captured =>
      .funcVal fid (captured.attach.map (fun ⟨v, _⟩ => relocV v))
  | .syncData p => .syncData p
  | .atom a => .atom a
termination_by v => sizeOf v
decreasing_by
  all_goals
    first
      | (rename_i h
         first
           | (have hlt := Array.sizeOf_lt_of_mem h; simp_all; omega)
           | (have hlt := List.sizeOf_lt_of_mem h; simp_all; omega))
      | (simp_all; omega)

def relocCell : SymHeapCell → SymHeapCell
  | .mk dty v => .mk dty (relocV v)
  | .atom a => .atom a

def relocS (S : SymState) : SymState :=
  { heap := S.heap.map (fun p => (relocLoc p.1, relocCell p.2)),
    nextAddr := rAddr S.nextAddr }

def relocEnv (env : LocalEnv) : LocalEnv :=
  env.map (fun scope => scope.map (fun p => (p.1, relocLoc p.2)))

def relocTR : Sym.TargetRef symDom → Sym.TargetRef symDom
  | .chain anchor idxs steps => .chain (relocV anchor) (idxs.map relocV) steps
  | .mapElem base key kt vt => .mapElem (relocV base) (relocV key) kt vt

def relocPE (p : Sym.PanicEntry symDom) : Sym.PanicEntry symDom :=
  ⟨relocV p.value, p.recovered⟩

def relocK : SymCont → SymCont
  | .stop => .stop
  | .seq rest env k => .seq rest (relocEnv env) (relocK k)
  | .loop c b env k => .loop c b (relocEnv env) (relocK k)
  | .frame t te r ds k w =>
      .frame t (relocEnv te) (r.map relocLoc)
        (ds.map (fun d => (relocV d.1, d.2.map relocV))) (relocK k) w
  | .deferCalleeK args env k => .deferCalleeK args (relocEnv env) (relocK k)
  | .deferArgsK cv vals pending env k =>
      .deferArgsK (relocV cv) (vals.map relocV) pending (relocEnv env)
        (relocK k)
  | .breakableK k => .breakableK (relocK k)
  | .labelK l k => .labelK l (relocK k)
  | .callValCalleeK t args env k =>
      .callValCalleeK t args (relocEnv env) (relocK k)
  | .callValArgsK cv t vals pending env k =>
      .callValArgsK (relocV cv) t (vals.map relocV) pending (relocEnv env)
        (relocK k)
  | .strictK op done pending env k =>
      .strictK op (done.map relocV) pending (relocEnv env) (relocK k)
  | .andK r env k => .andK r (relocEnv env) (relocK k)
  | .orK r env k => .orK r (relocEnv env) (relocK k)
  | .boolK k => .boolK (relocK k)
  | .ifK t e env k => .ifK t e (relocEnv env) (relocK k)
  | .whileK c b env k => .whileK c b (relocEnv env) (relocK k)
  | .callArgsK fid t vals pending env k =>
      .callArgsK fid t (vals.map relocV) pending (relocEnv env) (relocK k)
  | .stmtOpK op nt done pending env k =>
      .stmtOpK op nt (done.map relocV) pending (relocEnv env) (relocK k)
  | .mapRangeK kv vv kt vt b env k =>
      .mapRangeK kv vv kt vt b (relocEnv env) (relocK k)
  | .mapIterK kv vv kt vt b base produced start env k =>
      .mapIterK kv vv kt vt b (base.map relocLoc) (produced.map relocV)
        (start.map relocV) (relocEnv env) (relocK k)
  | .panicArgK k => .panicArgK (relocK k)
  | .panicResumeK chain k => .panicResumeK (chain.map relocPE) (relocK k)
  | .chanStK op done pending env k =>
      .chanStK op (done.map relocV) pending (relocEnv env) (relocK k)
  | .selectOpsK cl d done pending env k =>
      .selectOpsK cl d (done.map relocV) pending (relocEnv env) (relocK k)
  | .tgtOpK sh ops pending refs targets rop rhs vals b env k =>
      .tgtOpK sh (ops.map relocV) pending (refs.map relocTR) targets rop rhs
        (vals.map relocV) b (relocEnv env) (relocK k)
  | .rhsK rop refs done pending b env k =>
      .rhsK rop (refs.map relocTR) (done.map relocV) pending b
        (relocEnv env) (relocK k)
  | .storeK refs vals b env k =>
      .storeK (refs.map relocTR) (vals.map relocV) b (relocEnv env)
        (relocK k)
  | .goCalleeK args env k => .goCalleeK args (relocEnv env) (relocK k)
  | .goArgsK cv vals pending env k =>
      .goArgsK (relocV cv) (vals.map relocV) pending (relocEnv env)
        (relocK k)
  | .syncStK op done pending env k =>
      .syncStK op (done.map relocV) pending (relocEnv env) (relocK k)

def relocEvClause : Sym.EvClause symDom → Sym.EvClause symDom
  | .sendEv chv v elem body => .sendEv (relocV chv) (relocV v) elem body
  | .recvEv chv targets elem body => .recvEv (relocV chv) targets elem body

def relocC : SymConfig → SymConfig
  | .exec s env k => .exec s (relocEnv env) (relocK k)
  | .evalE e env k => .evalE e (relocEnv env) (relocK k)
  | .retV v k => .retV (relocV v) (relocK k)
  | .next k => .next (relocK k)
  | .breaking k => .breaking (relocK k)
  | .continuing k => .continuing (relocK k)
  | .returning k => .returning (relocK k)
  | .breakingTo l k => .breakingTo l (relocK k)
  | .continuingTo l k => .continuingTo l (relocK k)
  | .panicking chain k => .panicking (chain.map relocPE) (relocK k)
  | .panicked msg => .panicked msg
  | .blockedSend ch v k => .blockedSend (ch.map relocLoc) (relocV v) (relocK k)
  | .blockedRecv ch t e env k =>
      .blockedRecv (ch.map relocLoc) t e (relocEnv env) (relocK k)
  | .blockedSelect cl env k =>
      .blockedSelect (cl.map relocEvClause) (relocEnv env) (relocK k)
  | .opDone sched inner => .opDone sched (relocC inner)
  | .blockedSync op l env k =>
      .blockedSync op (relocLoc l) (relocEnv env) (relocK k)

/-! ## The Sym-level plug (open caller context at the barrier) -/

/-- Install an open caller context at the barrier (the unique frame
over `.stop`) of a CLOSED continuation — the Sym-level analogue of
`Frame.plugK`. -/
def symPlugK (tenv : LocalEnv) (kc : SymCont) : SymCont → SymCont
  | .frame t _te r ds .stop w => .frame t tenv r ds kc w
  | .stop => kc
  | .seq a b k => .seq a b (symPlugK tenv kc k)
  | .loop a b c k => .loop a b c (symPlugK tenv kc k)
  | .frame t te r ds k w => .frame t te r ds (symPlugK tenv kc k) w
  | .deferCalleeK a b k => .deferCalleeK a b (symPlugK tenv kc k)
  | .deferArgsK a b c d k => .deferArgsK a b c d (symPlugK tenv kc k)
  | .breakableK k => .breakableK (symPlugK tenv kc k)
  | .labelK a k => .labelK a (symPlugK tenv kc k)
  | .callValCalleeK a b c k => .callValCalleeK a b c (symPlugK tenv kc k)
  | .callValArgsK a b c d e k => .callValArgsK a b c d e (symPlugK tenv kc k)
  | .strictK a b c d k => .strictK a b c d (symPlugK tenv kc k)
  | .andK a b k => .andK a b (symPlugK tenv kc k)
  | .orK a b k => .orK a b (symPlugK tenv kc k)
  | .boolK k => .boolK (symPlugK tenv kc k)
  | .ifK a b c k => .ifK a b c (symPlugK tenv kc k)
  | .whileK a b c k => .whileK a b c (symPlugK tenv kc k)
  | .callArgsK a b c d e k => .callArgsK a b c d e (symPlugK tenv kc k)
  | .stmtOpK a b c d e k => .stmtOpK a b c d e (symPlugK tenv kc k)
  | .mapRangeK a b c d e f k => .mapRangeK a b c d e f (symPlugK tenv kc k)
  | .mapIterK a b c d e f g h i k =>
      .mapIterK a b c d e f g h i (symPlugK tenv kc k)
  | .panicArgK k => .panicArgK (symPlugK tenv kc k)
  | .panicResumeK a k => .panicResumeK a (symPlugK tenv kc k)
  | .chanStK a b c d k => .chanStK a b c d (symPlugK tenv kc k)
  | .selectOpsK a b c d e k => .selectOpsK a b c d e (symPlugK tenv kc k)
  | .tgtOpK a b c d e f g h i j k =>
      .tgtOpK a b c d e f g h i j (symPlugK tenv kc k)
  | .rhsK a b c d e f k => .rhsK a b c d e f (symPlugK tenv kc k)
  | .storeK a b c d k => .storeK a b c d (symPlugK tenv kc k)
  | .goCalleeK a b k => .goCalleeK a b (symPlugK tenv kc k)
  | .goArgsK a b c d k => .goArgsK a b c d (symPlugK tenv kc k)
  | .syncStK a b c d k => .syncStK a b c d (symPlugK tenv kc k)

def symPlugC (tenv : LocalEnv) (kc : SymCont) : SymConfig → SymConfig
  | .exec s env k => .exec s env (symPlugK tenv kc k)
  | .evalE e env k => .evalE e env (symPlugK tenv kc k)
  | .retV v k => .retV v (symPlugK tenv kc k)
  | .next k => .next (symPlugK tenv kc k)
  | .breaking k => .breaking (symPlugK tenv kc k)
  | .continuing k => .continuing (symPlugK tenv kc k)
  | .returning k => .returning (symPlugK tenv kc k)
  | .breakingTo l k => .breakingTo l (symPlugK tenv kc k)
  | .continuingTo l k => .continuingTo l (symPlugK tenv kc k)
  | .panicking chain k => .panicking chain (symPlugK tenv kc k)
  | .panicked msg => .panicked msg
  | .blockedSend ch v k => .blockedSend ch v (symPlugK tenv kc k)
  | .blockedRecv ch t e env k => .blockedRecv ch t e env (symPlugK tenv kc k)
  | .blockedSelect cl env k => .blockedSelect cl env (symPlugK tenv kc k)
  | .opDone sched inner => .opDone sched (symPlugC tenv kc inner)
  | .blockedSync op l env k => .blockedSync op l env (symPlugK tenv kc k)

end GoLean.RaftSeam
