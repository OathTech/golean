import GoLean.GoCore.StepFn

/-!
# The executable frame theorem, module 1: the rename algebra
(verified-examples arc slice 2b part 2; design of record
`docs/2026-08-13_executable-frame-theorem.md`)

Address renaming over every machine carrier: `Loc`, `GoValue`, heap
cells, environments, program syntax (`Expr`/`Stmt` — `Expr.locLit` is
the one loc-carrying node, so renaming the SYNTAX closes the locLit arm
with no side condition; seeds discharge program-invariance separately),
continuations, and configurations.

The renaming is parameterized by an arbitrary `ρ : Nat → Nat` subject to
`ShiftSpec ρ na₀ na` — injectivity plus "uniform shift on the fresh
region" (`ρ (na₀ + k) = na + k`). The design's uniform shift
(`uniformShift`, identity below `na₀`) is the canonical instance; the
abstraction is deliberate and costs nothing in the proofs (every lemma
uses only injectivity, plus the shift law exactly once, at allocation):
it additionally admits input-RELOCATING renamings (canonical placement
at low addresses transferred to an arbitrary admissible placement),
which the memory-input examples (reverse and the 2c set) consume.

No Iris anywhere in this file's import closure — the frame theorem is
first-order over the interpreter (statement-TCB doctrine).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## The renaming hypothesis -/

/-- `ρ` is injective and acts as the uniform shift on the fresh region:
the k-th fresh canonical address (`na₀ + k`) maps to the k-th fresh
framed address (`na + k`). Below `na₀` (the pre-existing addresses) `ρ`
is any injection avoiding the fresh image — which is automatic from
injectivity, see `ShiftSpec.low_lt`. -/
structure ShiftSpec (ρ : Nat → Nat) (na₀ na : Nat) : Prop where
  inj : ∀ {x y : Nat}, ρ x = ρ y → x = y
  shift : ∀ k : Nat, ρ (na₀ + k) = na + k

namespace ShiftSpec

variable {ρ : Nat → Nat} {na₀ na : Nat}

theorem shift' (h : ShiftSpec ρ na₀ na) {x : Nat} (hx : na₀ ≤ x) :
    ρ x = x - na₀ + na := by
  have := h.shift (x - na₀)
  rw [Nat.add_sub_cancel' hx] at this
  omega

/-- Successor commutes with `ρ` inside the fresh region. -/
theorem succ (h : ShiftSpec ρ na₀ na) {x : Nat} (hx : na₀ ≤ x) :
    ρ (x + 1) = ρ x + 1 := by
  rw [h.shift' hx, h.shift' (by omega : na₀ ≤ x + 1)]
  omega

/-- A pre-existing address never lands in the fresh image: `ρ x < na`
for `x < na₀` (pure injectivity + the shift law). -/
theorem low_lt (h : ShiftSpec ρ na₀ na) {x : Nat} (hx : x < na₀) :
    ρ x < na := by
  cases Nat.lt_or_ge (ρ x) na with
  | inl h' => exact h'
  | inr hge' =>
      exfalso
      have h1 : ρ (na₀ + (ρ x - na)) = na + (ρ x - na) := h.shift _
      have h2 : na + (ρ x - na) = ρ x := by omega
      have h3 : na₀ + (ρ x - na) = x := h.inj (by rw [h1, h2])
      omega

/-- A fresh address's image sits at or above `na`. -/
theorem fresh_ge (h : ShiftSpec ρ na₀ na) {x : Nat} (hx : na₀ ≤ x) :
    na ≤ ρ x := by
  rw [h.shift' hx]; omega

end ShiftSpec

/-- The design of record's uniform shift: identity below `na₀`, the
allocation bijection `[na₀, ∞) ≃ [na, ∞)` above it. -/
def uniformShift (na₀ na : Nat) : Nat → Nat :=
  fun x => if x < na₀ then x else x - na₀ + na

theorem uniformShift_spec {na₀ na : Nat} (h : na₀ ≤ na) :
    ShiftSpec (uniformShift na₀ na) na₀ na := by
  constructor
  · intro x y hxy
    simp only [uniformShift] at hxy
    split at hxy <;> split at hxy <;> omega
  · intro k
    simp only [uniformShift]
    split <;> omega

theorem uniformShift_low {na₀ na x : Nat} (hx : x < na₀) :
    uniformShift na₀ na x = x := by
  simp [uniformShift, hx]

/-! ## Renaming the carriers -/

variable (ρ : Nat → Nat)

/-- Locations: base ids rename; field/index steps rename their base. -/
def renameLoc : Loc → Loc
  | .base a => .base ⟨ρ a.id⟩
  | .field b tid f => .field (renameLoc b) tid f
  | .index b i => .index (renameLoc b) i

mutual

/-- Values: `.addr` and the slice/map/chan base references rename;
aggregates rename pointwise; every scalar (ints, floats, strings, sync
state) is loc-free and unchanged. -/
def renameValue : GoValue → GoValue
  | .unit => .unit
  | .bool b => .bool b
  | .int v k => .int v k
  | .float b k => .float b k
  | .string s => .string s
  | .nil => .nil
  | .addr l => .addr (renameLoc ρ l)
  | .interface t v => .interface t (renameValue v)
  | .struct tid fields => .struct tid (renameValueFields fields.toList).toArray
  | .array vs => .array (renameValueList vs.toList).toArray
  | .slice s => .slice { s with base := s.base.map (renameLoc ρ) }
  | .map m => .map { base := m.base.map (renameLoc ρ) }
  | .mapData es => .mapData (renameValueEntries es.toList).toArray
  | .chan c => .chan { base := c.base.map (renameLoc ρ) }
  | .chanData buf cap closed =>
      .chanData (renameValueList buf.toList).toArray cap closed
  | .funcVal fid captured => .funcVal fid (renameValueList captured)
  | .syncData p => .syncData p

def renameValueList : List GoValue → List GoValue
  | [] => []
  | v :: vs => renameValue v :: renameValueList vs

def renameValueFields : List (String × GoValue) → List (String × GoValue)
  | [] => []
  | (n, v) :: rest => (n, renameValue v) :: renameValueFields rest

def renameValueEntries : List (GoValue × GoValue) → List (GoValue × GoValue)
  | [] => []
  | (k, v) :: rest => (renameValue k, renameValue v) :: renameValueEntries rest

end

/-- Heap cells: the stored value renames; the declared type is loc-free. -/
def renameCell (c : HeapCell) : HeapCell :=
  { c with value := renameValue ρ c.value }

def renameScope (sc : Scope) : Scope :=
  sc.map (fun p => (p.1, renameLoc ρ p.2))

def renameEnv (env : LocalEnv) : LocalEnv :=
  env.map (renameScope ρ)

/-! ### Program syntax

`Expr.locLit` is the only loc-carrying node. Renaming the syntax (rather
than carrying a locLit-freeness side condition through every
configuration) closes the design's per-arm exclusion at zero cost: the
`locLit` arm steps to the renamed address on both sides. Seeds discharge
program-invariance (`renameStmt ρ body = body`) once, from `locSup`
bounds. -/

mutual

def renameExpr : Expr → Expr
  | .var id => .var id
  | .nil t => .nil t
  | .intLit v k => .intLit v k
  | .floatLit n d k => .floatLit n d k
  | .stringLit s => .stringLit s
  | .boolLit b => .boolLit b
  | .convert t e => .convert t (renameExpr e)
  | .bytesFromString e => .bytesFromString (renameExpr e)
  | .stringFromByteSlice e => .stringFromByteSlice (renameExpr e)
  | .stringFromRune e => .stringFromRune (renameExpr e)
  | .runesFromString e => .runesFromString (renameExpr e)
  | .stringFromRuneSlice e => .stringFromRuneSlice (renameExpr e)
  | .add l r => .add (renameExpr l) (renameExpr r)
  | .sub l r => .sub (renameExpr l) (renameExpr r)
  | .mul l r => .mul (renameExpr l) (renameExpr r)
  | .div l r => .div (renameExpr l) (renameExpr r)
  | .mod l r => .mod (renameExpr l) (renameExpr r)
  | .shiftLeft l r => .shiftLeft (renameExpr l) (renameExpr r)
  | .shiftRight l r => .shiftRight (renameExpr l) (renameExpr r)
  | .bitAnd l r => .bitAnd (renameExpr l) (renameExpr r)
  | .bitOr l r => .bitOr (renameExpr l) (renameExpr r)
  | .bitXor l r => .bitXor (renameExpr l) (renameExpr r)
  | .bitClear l r => .bitClear (renameExpr l) (renameExpr r)
  | .bitNeg e => .bitNeg (renameExpr e)
  | .neg e => .neg (renameExpr e)
  | .eqCmp t l r => .eqCmp t (renameExpr l) (renameExpr r)
  | .neqCmp t l r => .neqCmp t (renameExpr l) (renameExpr r)
  | .atMostCmp l r => .atMostCmp (renameExpr l) (renameExpr r)
  | .atLeastCmp l r => .atLeastCmp (renameExpr l) (renameExpr r)
  | .lessCmp l r => .lessCmp (renameExpr l) (renameExpr r)
  | .greaterCmp l r => .greaterCmp (renameExpr l) (renameExpr r)
  | .and l r => .and (renameExpr l) (renameExpr r)
  | .or l r => .or (renameExpr l) (renameExpr r)
  | .not e => .not (renameExpr e)
  | .ref id => .ref id
  | .funcVal fid captured => .funcVal fid (renameExprList captured.toList).toArray
  | .locLit l => .locLit (renameLoc ρ l)
  | .deref e t => .deref (renameExpr e) t
  | .addrOfDeref e => .addrOfDeref (renameExpr e)
  | .structLit t args => .structLit t (renameExprList args.toList).toArray
  | .fieldGet e tid f => .fieldGet (renameExpr e) tid f
  | .fieldAddr e tid f => .fieldAddr (renameExpr e) tid f
  | .arrayLit n elem args => .arrayLit n elem (renameKeyedExprList args.toList).toArray
  | .defaultValue t => .defaultValue t
  | .toInterface tgt dyn e => .toInterface tgt dyn (renameExpr e)
  | .typeAssert e tgt src => .typeAssert (renameExpr e) tgt src
  | .indexGet b i => .indexGet (renameExpr b) (renameExpr i)
  | .indexAddr b i => .indexAddr (renameExpr b) (renameExpr i)
  | .mapGet b i kt vt => .mapGet (renameExpr b) (renameExpr i) kt vt
  | .slice b lo hi m => .slice (renameExpr b) (renameExpr lo) (renameExpr hi) (renameOptExpr m)
  | .length e t => .length (renameExpr e) t
  | .capacity e t => .capacity (renameExpr e) t
  | .minOf args => .minOf (renameExprList args.toList).toArray
  | .maxOf args => .maxOf (renameExprList args.toList).toArray
  | .runeAt s off => .runeAt (renameExpr s) (renameExpr off)
  | .runeSizeAt s off => .runeSizeAt (renameExpr s) (renameExpr off)
  | .recoverCall => .recoverCall
  | .unsupported f => .unsupported f

def renameOptExpr : Option Expr → Option Expr
  | none => none
  | some e => some (renameExpr e)

def renameExprList : List Expr → List Expr
  | [] => []
  | e :: es => renameExpr e :: renameExprList es

def renameKeyedExprList : List (Int × Expr) → List (Int × Expr)
  | [] => []
  | (k, e) :: es => (k, renameExpr e) :: renameKeyedExprList es

end

def renameAssignee : Assignee → Assignee
  | .var id => .var id
  | .addr e => .addr (renameExpr ρ e)
  | .mapElem b k kt vt => .mapElem (renameExpr ρ b) (renameExpr ρ k) kt vt
  | .unsupported f => .unsupported f

def renameAssigneeList (l : List Assignee) : List Assignee :=
  l.map (renameAssignee ρ)

def renameSelectHead : SelectClauseHead → SelectClauseHead
  | .send ch v elem => .send (renameExpr ρ ch) (renameExpr ρ v) elem
  | .recv targets ch elem =>
      .recv ((renameAssigneeList ρ targets.toList).toArray) (renameExpr ρ ch) elem

mutual

def renameStmt : Stmt → Stmt
  | .seqn ss => .seqn (renameStmtList ss.toList).toArray
  | .block decls ss => .block decls (renameStmtList ss.toList).toArray
  | .breakable b => .breakable (renameStmt b)
  | .initialization p => .initialization p
  | .assign l r => .assign (renameAssignee ρ l) (renameExpr ρ r)
  | .assignMany ls rs =>
      .assignMany ((ls.toList.map (renameAssignee ρ)).toArray)
        ((renameExprList ρ rs.toList).toArray)
  | .newValue t v ty => .newValue (renameAssignee ρ t) (renameExpr ρ v) ty
  | .makeSlice t elem len cap =>
      .makeSlice (renameAssignee ρ t) elem (renameExpr ρ len) (renameOptExpr ρ cap)
  | .makeMap t k v space =>
      .makeMap (renameAssignee ρ t) k v (renameOptExpr ρ space)
  | .mapAssign b i v kt vt =>
      .mapAssign (renameExpr ρ b) (renameExpr ρ i) (renameExpr ρ v) kt vt
  | .mapDelete b i kt => .mapDelete (renameExpr ρ b) (renameExpr ρ i) kt
  | .clearMap b => .clearMap (renameExpr ρ b)
  | .clearSlice b elem => .clearSlice (renameExpr ρ b) elem
  | .sortSlice b elem => .sortSlice (renameExpr ρ b) elem
  | .mapLookup t okT b i kt vt =>
      .mapLookup (renameAssignee ρ t) (renameAssignee ρ okT)
        (renameExpr ρ b) (renameExpr ρ i) kt vt
  | .typeAssert t okT e tgt =>
      .typeAssert (renameAssignee ρ t) (renameAssignee ρ okT) (renameExpr ρ e) tgt
  | .appendSlice t elem sl els =>
      .appendSlice (renameAssignee ρ t) elem (renameExpr ρ sl) (renameExpr ρ els)
  | .copySlice t dst src =>
      .copySlice (renameAssignee ρ t) (renameExpr ρ dst) (renameExpr ρ src)
  | .call targets fid args =>
      .call ((targets.toList.map (renameAssignee ρ)).toArray) fid
        ((renameExprList ρ args.toList).toArray)
  | .callValue targets callee args =>
      .callValue ((targets.toList.map (renameAssignee ρ)).toArray)
        (renameExpr ρ callee) ((renameExprList ρ args.toList).toArray)
  | .deferCall callee args =>
      .deferCall (renameExpr ρ callee) ((renameExprList ρ args.toList).toArray)
  | .ifThenElse c t e => .ifThenElse (renameExpr ρ c) (renameStmt t) (renameStmt e)
  | .while c b => .while (renameExpr ρ c) (renameStmt b)
  | .mapRange kv vv me kt vt body =>
      .mapRange kv vv (renameExpr ρ me) kt vt (renameStmt body)
  | .returnStmt => .returnStmt
  | .breakStmt => .breakStmt
  | .continueStmt => .continueStmt
  | .labeled l b => .labeled l (renameStmt b)
  | .breakTo l => .breakTo l
  | .continueTo l => .continueTo l
  | .panicStmt e => .panicStmt (renameExpr ρ e)
  | .label n => .label n
  | .makeChan t elem cap => .makeChan (renameAssignee ρ t) elem (renameOptExpr ρ cap)
  | .chanSend ch v elem => .chanSend (renameExpr ρ ch) (renameExpr ρ v) elem
  | .chanRecv targets ch elem =>
      .chanRecv ((targets.toList.map (renameAssignee ρ)).toArray)
        (renameExpr ρ ch) elem
  | .closeChan ch => .closeChan (renameExpr ρ ch)
  | .selectStmt clauses default? =>
      .selectStmt (renameSelectClauses clauses.toList).toArray
        (renameOptStmt default?)
  | .goStmt callee args =>
      .goStmt (renameExpr ρ callee) ((renameExprList ρ args.toList).toArray)
  | .unsupported f => .unsupported f
  | .syncStmt op args targets =>
      .syncStmt op ((renameExprList ρ args.toList).toArray)
        ((targets.toList.map (renameAssignee ρ)).toArray)

def renameStmtList : List Stmt → List Stmt
  | [] => []
  | s :: ss => renameStmt s :: renameStmtList ss

def renameSelectClauses : List (SelectClauseHead × Stmt) → List (SelectClauseHead × Stmt)
  | [] => []
  | (h, b) :: rest => (renameSelectHead ρ h, renameStmt b) :: renameSelectClauses rest

def renameOptStmt : Option Stmt → Option Stmt
  | none => none
  | some s => some (renameStmt s)

end

/-! ### Machine-internal carriers -/

def renameTargetRef : TargetRef → TargetRef
  | .chain anchor idxs steps =>
      .chain (renameValue ρ anchor) (renameValueList ρ idxs) steps
  | .mapElem b k kt vt => .mapElem (renameValue ρ b) (renameValue ρ k) kt vt

def renamePlans (l : List (TargetShape × List Expr)) :
    List (TargetShape × List Expr) :=
  l.map (fun p => (p.1, renameExprList ρ p.2))

def renameChanOp : ChanStOp → ChanStOp
  | .send elem => .send elem
  | .recv targets elem => .recv (renameAssigneeList ρ targets) elem
  | .close => .close

def renameSyncOp : SyncOp → SyncOp
  | .onceBegin targets => .onceBegin (renameAssigneeList ρ targets)
  | op => op

def renameEntry (e : PanicEntry) : PanicEntry :=
  { e with value := renameValue ρ e.value }

def renameChain (chain : List PanicEntry) : List PanicEntry :=
  chain.map (renameEntry ρ)

def renameDefer (d : GoValue × List GoValue) : GoValue × List GoValue :=
  (renameValue ρ d.1, renameValueList ρ d.2)

def renameDefers (ds : List (GoValue × List GoValue)) :
    List (GoValue × List GoValue) :=
  ds.map (renameDefer ρ)

def renameEvClause : EvClause → EvClause
  | .sendEv chv v elem body =>
      .sendEv (renameValue ρ chv) (renameValue ρ v) elem (renameStmt ρ body)
  | .recvEv chv targets elem body =>
      .recvEv (renameValue ρ chv) (renameAssigneeList ρ targets) elem
        (renameStmt ρ body)

def renameCont : Cont → Cont
  | .stop => .stop
  | .seq rest env k =>
      .seq (renameStmtList ρ rest) (renameEnv ρ env) (renameCont k)
  | .loop cond body env k =>
      .loop (renameExpr ρ cond) (renameStmt ρ body) (renameEnv ρ env) (renameCont k)
  | .frame targets tenv results defers k w =>
      .frame (renamePlans ρ targets) (renameEnv ρ tenv)
        (results.map (renameLoc ρ)) (renameDefers ρ defers) (renameCont k) w
  | .deferCalleeK args env k =>
      .deferCalleeK (renameExprList ρ args) (renameEnv ρ env) (renameCont k)
  | .deferArgsK callee vals pending env k =>
      .deferArgsK (renameValue ρ callee) (renameValueList ρ vals)
        (renameExprList ρ pending) (renameEnv ρ env) (renameCont k)
  | .breakableK k => .breakableK (renameCont k)
  | .labelK l k => .labelK l (renameCont k)
  | .callValCalleeK targets args env k =>
      .callValCalleeK (renamePlans ρ targets) (renameExprList ρ args)
        (renameEnv ρ env) (renameCont k)
  | .callValArgsK callee targets vals pending env k =>
      .callValArgsK (renameValue ρ callee) (renamePlans ρ targets)
        (renameValueList ρ vals) (renameExprList ρ pending)
        (renameEnv ρ env) (renameCont k)
  | .strictK op done pending env k =>
      .strictK op (renameValueList ρ done) (renameExprList ρ pending)
        (renameEnv ρ env) (renameCont k)
  | .andK r env k => .andK (renameExpr ρ r) (renameEnv ρ env) (renameCont k)
  | .orK r env k => .orK (renameExpr ρ r) (renameEnv ρ env) (renameCont k)
  | .boolK k => .boolK (renameCont k)
  | .ifK t e env k =>
      .ifK (renameStmt ρ t) (renameStmt ρ e) (renameEnv ρ env) (renameCont k)
  | .whileK c b env k =>
      .whileK (renameExpr ρ c) (renameStmt ρ b) (renameEnv ρ env) (renameCont k)
  | .callArgsK fid targets vals pending env k =>
      .callArgsK fid (renamePlans ρ targets) (renameValueList ρ vals)
        (renameExprList ρ pending) (renameEnv ρ env) (renameCont k)
  | .stmtOpK op nt done pending env k =>
      .stmtOpK op nt (renameValueList ρ done) (renameExprList ρ pending)
        (renameEnv ρ env) (renameCont k)
  | .mapRangeK kv vv kt vt body env k =>
      .mapRangeK kv vv kt vt (renameStmt ρ body) (renameEnv ρ env) (renameCont k)
  | .mapIterK kv vv kt vt body base produced start env k =>
      .mapIterK kv vv kt vt (renameStmt ρ body)
        (base.map (renameLoc ρ))
        (renameValueList ρ produced.toList).toArray
        (renameValueList ρ start.toList).toArray
        (renameEnv ρ env) (renameCont k)
  | .panicArgK k => .panicArgK (renameCont k)
  | .panicResumeK chain k => .panicResumeK (renameChain ρ chain) (renameCont k)
  | .chanStK op done pending env k =>
      .chanStK (renameChanOp ρ op) (renameValueList ρ done)
        (renameExprList ρ pending) (renameEnv ρ env) (renameCont k)
  | .selectOpsK clauses default? done pending env k =>
      .selectOpsK (renameSelectClauses ρ clauses) (renameOptStmt ρ default?)
        (renameValueList ρ done) (renameExprList ρ pending)
        (renameEnv ρ env) (renameCont k)
  | .tgtOpK sh ops pending refs targets rop rhs vals body env k =>
      .tgtOpK sh (renameValueList ρ ops) (renameExprList ρ pending)
        (refs.map (renameTargetRef ρ)) (renamePlans ρ targets) rop
        (renameExprList ρ rhs) (renameValueList ρ vals) (renameStmt ρ body)
        (renameEnv ρ env) (renameCont k)
  | .rhsK rop refs done pending body env k =>
      .rhsK rop (refs.map (renameTargetRef ρ)) (renameValueList ρ done)
        (renameExprList ρ pending) (renameStmt ρ body) (renameEnv ρ env)
        (renameCont k)
  | .storeK refs vals body env k =>
      .storeK (refs.map (renameTargetRef ρ)) (renameValueList ρ vals)
        (renameStmt ρ body) (renameEnv ρ env) (renameCont k)
  | .goCalleeK args env k =>
      .goCalleeK (renameExprList ρ args) (renameEnv ρ env) (renameCont k)
  | .goArgsK callee vals pending env k =>
      .goArgsK (renameValue ρ callee) (renameValueList ρ vals)
        (renameExprList ρ pending) (renameEnv ρ env) (renameCont k)
  | .syncStK op done pending env k =>
      .syncStK (renameSyncOp ρ op) (renameValueList ρ done)
        (renameExprList ρ pending) (renameEnv ρ env) (renameCont k)

def renameConfig : Config → Config
  | .exec stmt env k => .exec (renameStmt ρ stmt) (renameEnv ρ env) (renameCont ρ k)
  | .evalE e env k => .evalE (renameExpr ρ e) (renameEnv ρ env) (renameCont ρ k)
  | .retV v k => .retV (renameValue ρ v) (renameCont ρ k)
  | .next k => .next (renameCont ρ k)
  | .breaking k => .breaking (renameCont ρ k)
  | .continuing k => .continuing (renameCont ρ k)
  | .returning k => .returning (renameCont ρ k)
  | .breakingTo l k => .breakingTo l (renameCont ρ k)
  | .continuingTo l k => .continuingTo l (renameCont ρ k)
  | .panicking chain k => .panicking (renameChain ρ chain) (renameCont ρ k)
  | .panicked msg => .panicked msg
  | .blockedSend ch v k =>
      .blockedSend (ch.map (renameLoc ρ)) (renameValue ρ v) (renameCont ρ k)
  | .blockedRecv ch targets elem env k =>
      .blockedRecv (ch.map (renameLoc ρ)) (renameAssigneeList ρ targets) elem
        (renameEnv ρ env) (renameCont ρ k)
  | .blockedSelect clauses env k =>
      .blockedSelect (clauses.map (renameEvClause ρ)) (renameEnv ρ env)
        (renameCont ρ k)
  | .opDone sc inner => .opDone sc (renameConfig inner)
  | .blockedSync op loc env k =>
      .blockedSync (renameSyncOp ρ op) (renameLoc ρ loc) (renameEnv ρ env)
        (renameCont ρ k)

/-! ## List-helper normalization (the `.map` bridges) -/

theorem renameValueList_eq_map (l : List GoValue) :
    renameValueList ρ l = l.map (renameValue ρ) := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp [renameValueList, ih]

theorem renameValueFields_eq_map (l : List (String × GoValue)) :
    renameValueFields ρ l = l.map (fun p => (p.1, renameValue ρ p.2)) := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp [renameValueFields, ih]

theorem renameValueEntries_eq_map (l : List (GoValue × GoValue)) :
    renameValueEntries ρ l = l.map (fun p => (renameValue ρ p.1, renameValue ρ p.2)) := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp [renameValueEntries, ih]

theorem renameExprList_eq_map (l : List Expr) :
    renameExprList ρ l = l.map (renameExpr ρ) := by
  induction l with
  | nil => rfl
  | cons e es ih => simp [renameExprList, ih]

theorem renameStmtList_eq_map (l : List Stmt) :
    renameStmtList ρ l = l.map (renameStmt ρ) := by
  induction l with
  | nil => rfl
  | cons s ss ih => simp [renameStmtList, ih]

theorem renameValueList_length (l : List GoValue) :
    (renameValueList ρ l).length = l.length := by
  rw [renameValueList_eq_map]; exact List.length_map ..

theorem renameExprList_length (l : List Expr) :
    (renameExprList ρ l).length = l.length := by
  rw [renameExprList_eq_map]; exact List.length_map ..

theorem renameValueList_append (a b : List GoValue) :
    renameValueList ρ (a ++ b) = renameValueList ρ a ++ renameValueList ρ b := by
  simp [renameValueList_eq_map]

theorem renameExprList_append (a b : List Expr) :
    renameExprList ρ (a ++ b) = renameExprList ρ a ++ renameExprList ρ b := by
  simp [renameExprList_eq_map]

theorem renameValueList_reverse (a : List GoValue) :
    renameValueList ρ a.reverse = (renameValueList ρ a).reverse := by
  simp [renameValueList_eq_map]

/-! ## Injectivity and `BEq` transport -/

section Inj

variable {ρ : Nat → Nat} (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
include hinj

theorem renameLoc_inj : ∀ {l l' : Loc},
    renameLoc ρ l = renameLoc ρ l' → l = l' := by
  intro l
  induction l with
  | base a =>
      intro l' h
      cases l' with
      | base b =>
          obtain ⟨i⟩ := a; obtain ⟨j⟩ := b
          simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at h ⊢
          exact hinj h
      | field b tid f => simp [renameLoc] at h
      | index b i => simp [renameLoc] at h
  | field b tid f ih =>
      intro l' h
      cases l' with
      | base a => simp [renameLoc] at h
      | field b' tid' f' =>
          simp only [renameLoc, Loc.field.injEq] at h ⊢
          obtain ⟨h1, h2, h3⟩ := h
          exact ⟨ih h1, h2, h3⟩
      | index b' i' => simp [renameLoc] at h
  | index b i ih =>
      intro l' h
      cases l' with
      | base a => simp [renameLoc] at h
      | field b' tid' f' => simp [renameLoc] at h
      | index b' i' =>
          simp only [renameLoc, Loc.index.injEq] at h ⊢
          obtain ⟨h1, h2⟩ := h
          exact ⟨ih h1, h2⟩

/-- `BEq` transport on locations: renamed comparisons decide the
original ones (both directions; `LawfulBEq Loc` bridges). -/
theorem renameLoc_beq (l l' : Loc) :
    (renameLoc ρ l == renameLoc ρ l') = (l == l') := by
  by_cases h : l = l'
  · subst h; simp
  · have h' : renameLoc ρ l ≠ renameLoc ρ l' := fun hc => h (renameLoc_inj hinj hc)
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

theorem renameLoc_base_inv {l : Loc} {a : Nat}
    (h : renameLoc ρ l = .base ⟨ρ a⟩) : l = .base ⟨a⟩ := by
  cases l with
  | base b =>
      obtain ⟨i⟩ := b
      simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at h ⊢
      exact hinj h
  | field b tid f => simp [renameLoc] at h
  | index b i => simp [renameLoc] at h

theorem renameOptLoc_inj {a b : Option Loc}
    (h : a.map (renameLoc ρ) = b.map (renameLoc ρ)) : a = b := by
  cases a <;> cases b <;> simp_all
  exact renameLoc_inj hinj h

theorem renameOptLoc_beq (a b : Option Loc) :
    (a.map (renameLoc ρ) == b.map (renameLoc ρ)) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : a.map (renameLoc ρ) ≠ b.map (renameLoc ρ) :=
      fun hc => h (renameOptLoc_inj hinj hc)
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

theorem renameScope_inj : ∀ {s s' : Scope},
    renameScope ρ s = renameScope ρ s' → s = s' := by
  intro s
  induction s with
  | nil =>
      intro s' h
      cases s' with
      | nil => rfl
      | cons q rest' => simp [renameScope] at h
  | cons p rest ih =>
      intro s' h
      cases s' with
      | nil => simp [renameScope] at h
      | cons q rest' =>
          obtain ⟨ps, pl⟩ := p
          obtain ⟨qs, ql⟩ := q
          simp only [renameScope, List.map_cons, List.cons.injEq,
            Prod.mk.injEq] at h
          obtain ⟨⟨h1, h2⟩, h3⟩ := h
          have hl := renameLoc_inj hinj h2
          subst h1 hl
          exact congrArg _ (ih (by simpa [renameScope] using h3))

theorem renameEnv_inj : ∀ {e e' : LocalEnv},
    renameEnv ρ e = renameEnv ρ e' → e = e' := by
  intro e
  induction e with
  | nil =>
      intro e' h
      cases e' with
      | nil => rfl
      | cons sc rest' => simp [renameEnv] at h
  | cons sc rest ih =>
      intro e' h
      cases e' with
      | nil => simp [renameEnv] at h
      | cons sc' rest' =>
          simp only [renameEnv, List.map_cons, List.cons.injEq] at h
          obtain ⟨h1, h2⟩ := h
          have hs := renameScope_inj hinj h1
          subst hs
          exact congrArg _ (ih (by simpa [renameEnv] using h2))

theorem renameEnv_eq_iff (e e' : LocalEnv) :
    renameEnv ρ e = renameEnv ρ e' ↔ e = e' :=
  ⟨renameEnv_inj hinj, fun h => by rw [h]⟩

end Inj

end GoLean.Frame
