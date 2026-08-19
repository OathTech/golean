import GoLeanProofs.Sym.Domain

/-!
# The mirror step function `stepFn'` (WP arc slice 4, phase 1, deliverable 2)

The shared parametric mirror of `GoLean.GoCore.Machine.stepFn` over a
`ScalarDom` (design §1.3 option 1b, ruled OQ1): ONE transcription of
the machine's logic, with every payload use routed through the domain —
class-A sites (payload-blind term production) call the total
constructors; class-B sites (payload-consulting control decisions) call
`toInt?`/`toBool?` and QUIT on `none`, carrying their `QuitSite`
(ruled OQ2). Route B: GoCore is untouched; the mirror lives entirely in
proof land, outside the statement TCB (walker-enforced).

**Transcription contract.** Every `stepFn` arm has a mirror arm, in the
same match ORDER (match semantics are order-dependent); arms outside
the v1 fragment quit immediately with their catalog entry. A quit is a
SHORTER WINDOW, never an error and never an unsound claim — the
refinement/drift statements are success-only, so a quit arm asserts
nothing. Fidelity of the computing arms is enforced by the drift
theorem (`Sym/Drift.lean`, a default build target): any computing arm
diverging from `stepFn` fails the build.

**Quit-site fidelity note.** `QuitSite` payloads are diagnostic
documentation (the design's §4 catalog as code); they never carry
claims. A mislabeled site costs debuggability, not soundness.

**Panics quit (Q6).** In GoCore a panic STEP is a successful step to a
`.panicking` configuration; v1 windows are success-straight-line
(design §4 Q6), so the mirror quits where `stepFn` would construct
`.panicking` — including division by zero on concrete payloads and
store-time bounds panics. The `.panicking`/`.panicked` configurations
exist in the mirror grammar (the transcription covers all arms) but
their arms quit.

Choices: the mirror takes NO choice stream. Every consuming site
(mapRange pick, append spill) quits Q3, which is exactly what makes the
transported window's `∀ ch, ch`-unchanged claim true by construction
(design §5/§6.1) — and insulates the mirror from the W3.2 `Choices`
reshape except through the drift theorem's visible break.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## The quit catalog as code (design §4, ruled OQ2)

Each constructor's docstring records (i) the machine site(s), (ii)
whether the quit is FORCED (the successor genuinely depends on an
unvaluated symbol) or CONSERVATIVE (a stronger evaluator could proceed
given more input), and (iii) the v2 lever that would lift it, if any
(design §6.4 — minimality is DOCUMENTED, not proven; an over-eager
quit costs automation, never soundness). -/
inductive QuitSite where
  /-- Q1 — branch on a symbolic bool: `valueAsBool` at
  `ifK`/`whileK`/`andK`/`orK`/`boolK` (`StepFn.lean:324-344`). FORCED:
  the next configuration depends on the payload; a window is one
  trace. Proof layer: case split on the emitted `decide (…)` and
  re-enter per branch (the shipped `B0`/`B1` segment pattern). -/
  | q1Branch
  /-- Q2 — symbolic address material: `valueAsInt` at index/bounds
  positions (`indexTargetLoc`, `sliceIndexLoc`, `arrayGet/Set`, slice
  bounds), `valueAsLoc` on a non-`.addr`. FORCED at symbolic indices
  under v1's absolute-address heaps; CONSERVATIVE under D-relative
  addressing (the v2 lever, design §3). Proof layer: the conditioned
  store/read kit steps (`StepKit.stepFn_var`/`stepFn_store_step`). -/
  | q2Address
  /-- Q3 — choice consumption: the mapRange pick (`StepFn.lean:599`)
  and the append-spill capacity (`Machine.lean:863`). FORCED: the
  successor depends on the stream, and the fragment's claim is
  `ch`-invariant. Proof layer: `mapPickLoop_generic`, the GAP-APPEND
  spill lemma. -/
  | q3Choice
  /-- Q4 — program/type-table consultation: `enterFrame` (every
  call/defer entry), `TypeEnv.lookup` inside
  normalize/default/convert/valueEq at `.defined` types,
  `toInterface`/`typeAssert`/dispatch machinery, hashability of
  interface-typed keys. CONSERVATIVE: v2's conditioned-facts-as-inputs
  lever (ruled OQ6, deferred) would convert these to proceeds; v1
  quits unconditionally at BOTH instances — which is what makes
  emitted windows program-generic by construction (JC-1). Proof layer:
  split the window and condition on the executable fact
  (`stepFn_call_enter` with an `enterFrame … = .ok …` hypothesis). -/
  | q4Program
  /-- Q5 — payload-dependent success inside an op: symbolic divisor
  (`/ %`), symbolic shift count/operand, symbolic `make` sizes,
  symbolic slice-expression bounds, `natFromNonnegativeInt` on a
  symbolic, int→float conversion of a symbolic. FORCED (success vs
  panic depends on the payload). Proof layer: a conditioned apply
  lemma at the site (`kd_make_apply` is the worked exemplar). -/
  | q5OpPayload
  /-- Q6 — panic paths: any step whose GoCore result is `.panicking`
  (strict-op panics incl. div-by-zero and bounds, store-time panics,
  nil-callee/nil-deref, `panicStmt` delivery), plus the whole
  `.panicking` unwinding cluster and `recoverCall` (JC-5a — the
  recover walk is panic machinery; v2 lever: mirror
  `recoverResult`). v1 windows are success-straight-line; panic
  behavior lives in the NegativeSpecs lane, never inside segment
  windows. CONSERVATIVE only in that a panic-window evaluator could
  exist; no consumer wants one. -/
  | q6Panic
  /-- Q7 — concurrency surface: chan/select/sync/go statement arms
  (entry AND apply — JC-5b), the blocked shapes, `spawned`. Out of the
  sequential gallery fragment; nothing in the campaign corpus
  regresses. -/
  | q7Concurrency
  /-- Q8 — symbolic map keys / entries: `mapEntryIndex?`'s scan needs
  equality DECISIONS on keys; `isNormalForTy` on symbolic payloads
  reads them. Concrete keys with symbolic VALUES do NOT quit (the scan
  compares keys only). FORCED at genuinely symbolic keys; the decided
  equality family also serves the Q9 aggregate folds (recorded
  imprecision: those decisions report this site). v2 lever: a
  decidable key theory. -/
  | q8MapSym
  /-- Q9 — inspection-driven aggregates: `min`/`max` folds and
  `sortSlice` over symbolic elements (comparison-driven results).
  FORCED. Proof layer: per-example branch reasoning (rare, cheap by
  hand). -/
  | q9Aggregate
  /-- Q10 — opaque-atom inspection: any class-B operation (or
  head-shape discrimination) reaching an `atom` cell's content.
  Riding through, being loaded to `retV`, or being stored wholesale
  does NOT quit. FORCED (the atom's shape is unvaluated by
  construction). Proof layer: conditioned lookup lemmas over the
  ridden cells (`lookup_kSu` style). -/
  | q10Atom
  /-- Q11 — evaluator-internal fail-closed: malformed mirror states
  (the concrete machine's `.stuck`/`.internal`/`.unsupported`
  classifications), fuel exhaustion inside type-directed walks,
  terminal configurations handed to the step. Not semantic quits;
  they produce no window rather than a shorter one. -/
  | q11Internal
  deriving DecidableEq, Repr

/-- The mirror's outcome monad (ruled OQ2): `Except QuitSite`, with the
DRIVER converting quit into a shorter window. -/
abbrev M (α : Type _) := Except QuitSite α

@[inline] def quit {α : Type _} (q : QuitSite) : M α := .error q

/-! ## The mirror value grammar (design §1.3/§5.1)

`GoValue`'s grammar constructor-for-constructor with `.int`'s payload
replaced by `D.IntR`, `.bool`'s by `D.BoolR`, plus the opaque-cell
`atom`. Everything else — addresses, handles, strings, floats, sync
state — stays CONCRETE (v1 scope). -/

inductive Value (D : ScalarDom) where
  | unit
  | bool (b : D.BoolR)
  | int (v : D.IntR) (kind : IntKind)
  | float (bits : Nat) (kind : FloatKind)
  | string (s : GoString)
  | addr (loc : Loc)
  | nil
  | interface (dynamic : Ty) (value : Value D)
  | struct (typeId : TypeId) (fields : Array (String × Value D))
  | array (values : Array (Value D))
  | slice (v : SliceValue)
  | map (v : MapValue)
  | mapData (entries : Array (Value D × Value D))
  | chan (v : ChanValue)
  | chanData (buf : Array (Value D)) (capacity : Nat) (closed : Bool)
  | funcVal (fid : FuncId) (captured : List (Value D))
  | syncData (p : SyncPrim)
  /-- The opaque heap-cell payload (design §1.2/§2.1): a whole cell the
  window never inspects, γ-mapped to `ρ.vals a` at the symbolic
  instance; uninhabited (`Empty`) at the concrete instance (JC-2). -/
  | atom (a : D.Atom)

/-- Mirror of `Machine.PanicEntry` (carried by the panicking shapes,
which the mirror covers but quits on). -/
structure PanicEntry (D : ScalarDom) where
  value : Value D
  recovered : Bool

/-- Mirror of `Machine.TargetRef` (phase-1-resolved store targets). -/
inductive TargetRef (D : ScalarDom) where
  | chain (anchor : Value D) (idxs : List (Value D)) (steps : List TargetStep)
  | mapElem (base key : Value D) (keyTy valueTy : Ty)

/-- Mirror of `Machine.EvClause` (select-clause payloads; Q7 zone). -/
inductive EvClause (D : ScalarDom) where
  | sendEv (chv v : Value D) (elem : Ty) (body : Stmt)
  | recvEv (chv : Value D) (targets : List Assignee) (elem : Ty) (body : Stmt)

/-- Mirror of `GoCore.HeapCell`, PLUS the whole-cell opaque atom
(JC-6): `declaredTy` stays concrete — it drives the store-time
normalizer's TYPE dispatch (design §1.2) — and a cell whose declared
type itself depends on a symbol (Kadane's `kBack n l` backing:
`.array n …`) rides as a CELL atom, quitting Q10 on any load or
store through it (heap lookups compare keys, never cell contents, so
ride-through is exact). -/
inductive HeapCell (D : ScalarDom) where
  | mk (declaredTy : Option Ty) (value : Value D)
  | atom (a : D.Atom)

abbrev Heap (D : ScalarDom) := List (Loc × HeapCell D)

/-- The mirror state (design §5.1): concrete-keyed heap skeleton +
allocator bound. NO types/functions/methods/methodSets — Q4 quits are
what enforce program-genericity by construction. -/
structure State (D : ScalarDom) where
  heap : Heap D := []
  nextAddr : Nat := 0

/-- Mirror of `Machine.Cont`, constructor-for-constructor (same order),
with carried VALUES at the domain's payloads; program syntax,
environments, `Loc`s and shapes stay concrete (they come from the
pinned program and the window's closed continuation). -/
inductive Cont (D : ScalarDom) where
  | stop
  | seq (rest : List Stmt) (env : LocalEnv) (k : Cont D)
  | loop (cond : Expr) (body : Stmt) (env : LocalEnv) (k : Cont D)
  | frame (targets : List (TargetShape × List Expr)) (tenv : LocalEnv)
      (results : List Loc)
      (defers : List (Value D × List (Value D))) (k : Cont D) (wrapper : Bool := false)
  | deferCalleeK (args : List Expr) (env : LocalEnv) (k : Cont D)
  | deferArgsK (callee : Value D) (vals : List (Value D))
      (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | breakableK (k : Cont D)
  | labelK (label : String) (k : Cont D)
  | callValCalleeK (targets : List (TargetShape × List Expr))
      (args : List Expr) (env : LocalEnv) (k : Cont D)
  | callValArgsK (callee : Value D) (targets : List (TargetShape × List Expr))
      (vals : List (Value D)) (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | strictK (op : StrictOp) (done : List (Value D)) (pending : List Expr)
      (env : LocalEnv) (k : Cont D)
  | andK (right : Expr) (env : LocalEnv) (k : Cont D)
  | orK (right : Expr) (env : LocalEnv) (k : Cont D)
  | boolK (k : Cont D)
  | ifK (thenBranch elseBranch : Stmt) (env : LocalEnv) (k : Cont D)
  | whileK (cond : Expr) (body : Stmt) (env : LocalEnv) (k : Cont D)
  | callArgsK (fid : FuncId) (targets : List (TargetShape × List Expr))
      (vals : List (Value D)) (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | stmtOpK (op : StmtOp) (ntargets : Nat) (done : List (Value D))
      (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | mapRangeK (keyVar valVar : Option String) (keyTy valTy : Ty)
      (body : Stmt) (env : LocalEnv) (k : Cont D)
  | mapIterK (keyVar valVar : Option String) (keyTy valTy : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array (Value D))
      (env : LocalEnv) (k : Cont D)
  | panicArgK (k : Cont D)
  | panicResumeK (chain : List (PanicEntry D)) (k : Cont D)
  | chanStK (op : ChanStOp) (done : List (Value D))
      (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | selectOpsK (clauses : List (SelectClauseHead × Stmt)) (default? : Option Stmt)
      (done : List (Value D)) (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | tgtOpK (sh : TargetShape) (ops : List (Value D)) (pending : List Expr)
      (refs : List (TargetRef D)) (targets : List (TargetShape × List Expr))
      (rop : RhsOp) (rhs : List Expr) (vals : List (Value D)) (body : Stmt)
      (env : LocalEnv) (k : Cont D)
  | rhsK (rop : RhsOp) (refs : List (TargetRef D)) (done : List (Value D))
      (pending : List Expr) (body : Stmt) (env : LocalEnv) (k : Cont D)
  | storeK (refs : List (TargetRef D)) (vals : List (Value D))
      (body : Stmt) (env : LocalEnv) (k : Cont D)
  | goCalleeK (args : List Expr) (env : LocalEnv) (k : Cont D)
  | goArgsK (callee : Value D) (vals : List (Value D))
      (pending : List Expr) (env : LocalEnv) (k : Cont D)
  | syncStK (op : SyncOp) (done : List (Value D))
      (pending : List Expr) (env : LocalEnv) (k : Cont D)

/-- Mirror of `Machine.Config`, constructor-for-constructor (same
order). -/
inductive Config (D : ScalarDom) where
  | exec (stmt : Stmt) (env : LocalEnv) (k : Cont D)
  | evalE (e : Expr) (env : LocalEnv) (k : Cont D)
  | retV (v : Value D) (k : Cont D)
  | next (k : Cont D)
  | breaking (k : Cont D)
  | continuing (k : Cont D)
  | returning (k : Cont D)
  | breakingTo (label : String) (k : Cont D)
  | continuingTo (label : String) (k : Cont D)
  | panicking (chain : List (PanicEntry D)) (k : Cont D)
  | panicked (msg : String)
  | blockedSend (ch : Option Loc) (v : Value D) (k : Cont D)
  | blockedRecv (ch : Option Loc) (targets : List Assignee) (elem : Ty)
      (env : LocalEnv) (k : Cont D)
  | blockedSelect (clauses : List (EvClause D)) (env : LocalEnv) (k : Cont D)
  | spawned (k : Cont D)
  | blockedSync (op : SyncOp) (loc : Loc) (env : LocalEnv) (k : Cont D)

variable {D : ScalarDom}

/-! ## Heap and state operations (mirrors of `State.lean`'s) -/

def Heap.lookup : Heap D → Loc → Option (HeapCell D)
  | [], _ => none
  | (loc, cell) :: rest, needle =>
      if loc == needle then some cell else Heap.lookup rest needle

def Heap.set : Heap D → Loc → HeapCell D → Heap D
  | [], loc, cell => [(loc, cell)]
  | (loc, old) :: rest, needle, cell =>
      if loc == needle then
        (loc, cell) :: rest
      else
        (loc, old) :: Heap.set rest needle cell

def State.freshLoc (s : State D) : Loc × State D :=
  (Loc.base { id := s.nextAddr }, { s with nextAddr := s.nextAddr + 1 })

def State.alloc (s : State D) (value : Value D) (typ : Option Ty := none) :
    Loc × State D :=
  let (loc, s) := s.freshLoc
  (loc, { s with heap := Heap.set s.heap loc (.mk typ value) })

/-! ## Payload projections (the class-B inspection census)

Every `toInt?`/`toBool?` call in this module routes through the
functions in this section (plus `isNormalForTyFuel'`'s int arm and the
`sortSlice` element reads) — grep `toInt?\|toBool?` to audit the
complete inspection surface. -/

/-- Project a concrete `Int` at inspection site `q`. GoCore analogue:
`valueAsInt` (stuck on non-ints → Q11); atoms are Q10. -/
def Value.asIntAt (q : QuitSite) : Value D → M Int
  | .int v _ =>
      match D.toInt? v with
      | some n => .ok n
      | none => quit q
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- Project a concrete `Bool` at inspection site `q` (GoCore:
`valueAsBool`). -/
def Value.asBoolAt (q : QuitSite) : Value D → M Bool
  | .bool b =>
      match D.toBool? b with
      | some x => .ok x
      | none => quit q
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- GoCore `valueAsLoc`: nil is the nil-deref PANIC (Q6). -/
def Value.asLoc : Value D → M Loc
  | .addr loc => .ok loc
  | .nil => quit .q6Panic
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- The int payload with its kind (class-A entry; no inspection). -/
def Value.asIntR : Value D → M (D.IntR × IntKind)
  | .int v kind => .ok (v, kind)
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

def Value.asSlice : Value D → M SliceValue
  | .slice v => .ok v
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

def Value.asMap : Value D → M MapValue
  | .map v => .ok v
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- GoCore `deferrableCallee` (head-shape discrimination — an atom
cannot answer it). -/
def Value.deferrable : Value D → M Bool
  | .funcVal _ _ => .ok true
  | .nil => .ok true
  | .atom _ => quit .q10Atom
  | _ => .ok false

/-! ## Concrete-side lifted helpers

Bounds checks and index arithmetic operate on concrete data in v1
(absolute addresses, concrete handles — design §3); their PANIC
outcomes quit Q6, their fail-closed outcomes Q11. -/

/-- GoCore `arrayIndexNat`, over the element COUNT (the only thing it
reads). Panic → Q6. -/
def arrayIndexNat' (size : Nat) (index : Int) : M Nat :=
  if index < 0 then quit .q6Panic
  else
    let i := index.toNat
    if i < size then .ok i else quit .q6Panic

/-- GoCore `checkSliceBounds` (messages dropped: panics quit). -/
def checkSliceBounds' (limit : Nat) (low high : Int) : M (Nat × Nat) :=
  if high < 0 then quit .q6Panic
  else if high > limit then quit .q6Panic
  else if low < 0 then quit .q6Panic
  else if low > high then quit .q6Panic
  else .ok (low.toNat, high.toNat)

/-- GoCore `checkSliceBounds3`. -/
def checkSliceBounds3' (max : Nat) (low high : Int) : M (Nat × Nat) :=
  if high < 0 then quit .q6Panic
  else if high > max then quit .q6Panic
  else if low < 0 then quit .q6Panic
  else if low > high then quit .q6Panic
  else .ok (low.toNat, high.toNat)

/-- GoCore `checkSliceMax`. -/
def checkSliceMax' (limit : Nat) (max : Int) : M Nat :=
  if max < 0 then quit .q6Panic
  else if max > limit then quit .q6Panic
  else .ok max.toNat

/-- GoCore `validateSlice` (fail-closed shapes → Q11). -/
def validateSlice' (slice : SliceValue) : M Unit :=
  if slice.len > slice.cap then quit .q11Internal
  else
    match slice.base with
    | some _ => .ok ()
    | none =>
        if slice.offset == 0 && slice.len == 0 && slice.cap == 0 then .ok ()
        else quit .q11Internal

/-- GoCore `sliceIndexLoc` (concrete handle, concrete index). -/
def sliceIndexLoc' (slice : SliceValue) (index : Int) : M Loc := do
  validateSlice' slice
  let i ←
    if index < 0 then quit .q6Panic
    else pure index.toNat
  if i < slice.len then
    match slice.base with
    | some base => .ok (.index base (Int.ofNat (slice.offset + i)))
    | none => quit .q11Internal
  else quit .q6Panic

/-- GoCore `sliceFromSlice`. -/
def sliceFromSlice' (slice : SliceValue) (low high : Int) (max : Option Int) :
    M (Value D) := do
  validateSlice' slice
  match max with
  | none =>
      let (low, high) ← checkSliceBounds' slice.cap low high
      .ok (.slice { base := slice.base, offset := slice.offset + low,
                    len := high - low, cap := slice.cap - low })
  | some max =>
      let max ← checkSliceMax' slice.cap max
      let (low, high) ← checkSliceBounds3' max low high
      .ok (.slice { base := slice.base, offset := slice.offset + low,
                    len := high - low, cap := max - low })

/-- GoCore `sliceFromArray`. -/
def sliceFromArray' (base : Loc) (length : Nat) (low high : Int)
    (max : Option Int) : M (Value D) := do
  match max with
  | none =>
      let (low, high) ← checkSliceBounds' length low high
      .ok (.slice { base := some base, offset := low,
                    len := high - low, cap := length - low })
  | some max =>
      let max ← checkSliceMax' length max
      let (low, high) ← checkSliceBounds3' max low high
      .ok (.slice { base := some base, offset := low,
                    len := high - low, cap := max - low })

/-- GoCore `stringSlice`. -/
def stringSlice' (value : GoString) (low high : Int) (max : Option Int) :
    M (Value D) := do
  if max.isSome then quit .q11Internal
  let (low, high) ← checkSliceBounds' value.length low high
  .ok (.string (value.slice low high))

/-- GoCore `stringByteGet`. -/
def stringByteGet' (value : GoString) (index : Int) : M (Value D) := do
  if index < 0 then quit .q6Panic
  let i := index.toNat
  match value.byte? i with
  | some byte => .ok (.int (D.litI (Int.ofNat byte.toNat)) .uint8)
  | none => quit .q6Panic

/-! ## Value walks: coerce / normalize / default / equality -/

/-- Pairwise coercion at the (already fuel-decremented) element
coercer — the de-WF recipe's shape, mirroring `coerceArray`. -/
def coerceListWith' (f : Value D → Value D → M (Value D)) :
    List (Value D) → List (Value D) → M (Array (Value D))
  | oldValue :: oldRest, newValue :: newRest => do
      let head ← f oldValue newValue
      let tail ← coerceListWith' f oldRest newRest
      .ok (#[head] ++ tail)
  | _, _ => .ok #[]

/-- Pairwise field coercion, mirroring `coerceStruct`. -/
def coerceFieldsWith' (f : Value D → Value D → M (Value D)) :
    List (String × Value D) → List (String × Value D) →
    M (Array (String × Value D))
  | (oldName, oldValue) :: oldRest, (newName, newValue) :: newRest => do
      if oldName != newName then quit .q11Internal
      let head ← f oldValue newValue
      let tail ← coerceFieldsWith' f oldRest newRest
      .ok (#[(oldName, head)] ++ tail)
  | _, _ => .ok #[]

/-- Mirror of `coerceStoredValue` (untyped-cell stores), on the FUEL
recipe (GoCore's original is structural-mutual and WF-compiled; the
mirror trades that for fuel-structural kernel reducibility — the seal
lesson in reverse — quitting Q11 on exhaustion, a conservative quit no
real value reaches at `valueEqbFuel` depth). Arms where GoCore
discriminates on BOTH heads quit Q10 when either side is an atom; the
identity catch-all passes atoms through faithfully (GoCore returns the
new value unchanged for every unmatched pair). -/
def coerceStoredValueFuel' : Nat → Value D → Value D → M (Value D)
  | 0, _, _ => quit .q11Internal
  | _ + 1, .int _ kind, .int value _ => .ok (.int (D.norm kind value) kind)
  | _ + 1, .float _ kind, .float bits k =>
      if k == kind then .ok (.float (kind.normalizeBits bits) kind)
      else quit .q11Internal
  | fuel + 1, .array oldValues, .array newValues =>
      if oldValues.size != newValues.size then quit .q11Internal
      else Value.array <$>
        coerceListWith' (coerceStoredValueFuel' fuel)
          oldValues.toList newValues.toList
  | fuel + 1, .struct oldType oldFields, .struct newType newFields =>
      if oldType != newType then quit .q11Internal
      else if oldFields.size != newFields.size then quit .q11Internal
      else Value.struct oldType <$>
        coerceFieldsWith' (coerceStoredValueFuel' fuel)
          oldFields.toList newFields.toList
  | _ + 1, .atom _, _ => quit .q10Atom
  | _ + 1, _, .atom _ => quit .q10Atom
  | _ + 1, _, value => .ok value

@[inherit_doc coerceStoredValueFuel']
def coerceStoredValue' (old new : Value D) : M (Value D) :=
  coerceStoredValueFuel' valueEqbFuel old new

/-- Mirror of `normalizeListWith` (the de-WF recipe: parameterized,
structural on the list, fuel decremented by the caller). -/
def normalizeListWith' (f : Value D → M (Value D)) :
    List (Value D) → M (Array (Value D))
  | value :: rest => do
      let head ← f value
      let tail ← normalizeListWith' f rest
      .ok (#[head] ++ tail)
  | [] => .ok #[]

/-- Mirror of `normalizeValueForTyFuel` (fuel-structural, kernel-
reducible; design §1.2: normalization at store time is a CONSTRUCTOR —
target `Ty`, value head, and int kind are all concrete in v1, only the
payload rides through `norm`). `.defined` targets are program consults
(Q4); struct-arm normalization only arises under them, so the
`normalizeStructValueWith`/`normalizeFieldsWith` pair has no mirror. -/
def normalizeValueForTyFuel' : Nat → Ty → Value D → M (Value D)
  | 0, _, _ => quit .q11Internal
  | _ + 1, .int kind, .int value _ => .ok (.int (D.norm kind value) kind)
  | _ + 1, .int _, .atom _ => quit .q10Atom
  | _ + 1, .int _, _ => quit .q11Internal
  | _ + 1, .float kind, .float bits k =>
      if k == kind then .ok (.float (kind.normalizeBits bits) kind)
      else quit .q11Internal
  | _ + 1, .float _, .atom _ => quit .q10Atom
  | _ + 1, .float _, _ => quit .q11Internal
  | fuel + 1, .array length elem, .array values => do
      if values.size != length then quit .q11Internal
      else
        Value.array <$>
          normalizeListWith' (normalizeValueForTyFuel' fuel elem) values.toList
  | _ + 1, .array _ _, .atom _ => quit .q10Atom
  | _ + 1, .array _ _, _ => quit .q11Internal
  | _ + 1, .interface _, value => .ok value
  | _ + 1, .funcType _ _, .funcVal fid captured => .ok (.funcVal fid captured)
  | _ + 1, .funcType _ _, .nil => .ok .nil
  | _ + 1, .funcType _ _, .atom _ => quit .q10Atom
  | _ + 1, .funcType _ _, _ => quit .q11Internal
  | _ + 1, .chan _ _, .chan cv => .ok (.chan cv)
  | _ + 1, .chan _ _, .nil => .ok (.chan { base := none })
  | _ + 1, .chan _ _, .atom _ => quit .q10Atom
  | _ + 1, .chan _ _, _ => quit .q11Internal
  | _ + 1, .sync kind, .syncData p =>
      if p.kind == kind then .ok (.syncData p) else quit .q11Internal
  | _ + 1, .sync _, .atom _ => quit .q10Atom
  | _ + 1, .sync _, _ => quit .q11Internal
  | _ + 1, .defined _, _ => quit .q4Program
  | _ + 1, .unsupported _, _ => quit .q11Internal
  | _ + 1, _, value => .ok value

def normalizeValueForTy' (ty : Ty) (value : Value D) : M (Value D) :=
  normalizeValueForTyFuel' typeResolutionFuel ty value

/-- Mirror of `isNormalListWith` at decided (`M Bool`) elements. -/
def isNormalListWith' (f : Value D → M Bool) : List (Value D) → M Bool
  | [] => .ok true
  | v :: rest => do
      let b ← f v
      if b then isNormalListWith' f rest else .ok false

/-- Mirror of `isNormalForTyFuel` — a DECISION on the payload, so the
int/float arms inspect (`toInt?`, Q8: the consumer is the mapRange
snapshot check). -/
def isNormalForTyFuel' : Nat → Ty → Value D → M Bool
  | 0, _, _ => .ok false
  | _ + 1, .int kind, .int value k => do
      match D.toInt? value with
      | some n => .ok (decide (kind.normalize n = n) && decide (kind = k))
      | none => quit .q8MapSym
  | _ + 1, .int _, .atom _ => quit .q10Atom
  | _ + 1, .int _, _ => .ok false
  | _ + 1, .float kind, .float bits k =>
      .ok (decide (kind.normalizeBits bits = bits) && decide (kind = k))
  | _ + 1, .float _, .atom _ => quit .q10Atom
  | _ + 1, .float _, _ => .ok false
  | fuel + 1, .array length elem, .array values => do
      if values.size = length then
        isNormalListWith' (isNormalForTyFuel' fuel elem) values.toList
      else .ok false
  | _ + 1, .array _ _, .atom _ => quit .q10Atom
  | _ + 1, .array _ _, _ => .ok false
  | _ + 1, .interface _, _ => .ok true
  | _ + 1, .funcType _ _, .funcVal _ _ => .ok true
  | _ + 1, .funcType _ _, .nil => .ok true
  | _ + 1, .funcType _ _, .atom _ => quit .q10Atom
  | _ + 1, .funcType _ _, _ => .ok false
  | _ + 1, .chan _ _, .chan _ => .ok true
  | _ + 1, .chan _ _, .atom _ => quit .q10Atom
  | _ + 1, .chan _ _, _ => .ok false
  | _ + 1, .sync kind, .syncData p => .ok (p.kind == kind)
  | _ + 1, .sync _, .atom _ => quit .q10Atom
  | _ + 1, .sync _, _ => .ok false
  | _ + 1, .defined _, _ => quit .q4Program
  | _ + 1, .unsupported _, _ => .ok false
  | _ + 1, _, _ => .ok true

def isNormalForTy' (ty : Ty) (value : Value D) : M Bool :=
  isNormalForTyFuel' typeResolutionFuel ty value

/-- Mirror of `defaultFieldsWith` — unreachable in v1 (only the
`.defined` arm builds struct defaults, and it quits Q4), kept for
arm-shape parity of the fuel walk. -/
def defaultValueFuel' : Nat → Ty → M (Value D)
  | 0, _ => quit .q11Internal
  | _ + 1, .bool => .ok (.bool (D.litB false))
  | _ + 1, .int kind => .ok (.int (D.litI 0) kind)
  | _ + 1, .float kind => .ok (.float 0 kind)
  | _ + 1, .string => .ok (.string GoString.empty)
  | fuel + 1, .array length elem => do
      if length == 0 then .ok (.array #[])
      else
        let elemDefault ← defaultValueFuel' fuel elem
        .ok (.array (Array.replicate length elemDefault))
  | _ + 1, .slice _ => .ok (.slice { base := none, offset := 0, len := 0, cap := 0 })
  | _ + 1, .map _ _ => .ok (.map { base := none })
  | _ + 1, .chan _ _ => .ok (.chan { base := none })
  | _ + 1, .sync kind => .ok (.syncData kind.zero)
  | _ + 1, .pointer _ => .ok .nil
  | _ + 1, .funcType _ _ => .ok .nil
  | _ + 1, .interface _ => .ok .nil
  | _ + 1, .defined _ => quit .q4Program
  | _ + 1, .unsupported _ => quit .q11Internal

def defaultValue' (ty : Ty) : M (Value D) :=
  defaultValueFuel' typeResolutionFuel ty

/-- Decided pairwise equality (mirror of `valueEqListWith` at a decided
comparator). -/
def valueEqListWith' (f : Value D → Value D → M Bool) :
    List (Value D) → List (Value D) → M Bool
  | leftValue :: leftRest, rightValue :: rightRest => do
      let b ← f leftValue rightValue
      if b then valueEqListWith' f leftRest rightRest else .ok false
  | _, _ => .ok true

/-- The DECIDED equality family (mirror of `valueEqFuel`, collapsed to
`Bool`): serves the map-key scans (Q8) and aggregate folds. Symbolic
int/bool payloads decide through the inspections (so fully-concrete
values never quit); `.defined`/`.interface` arms are program consults
(Q4); struct arms only arise under `.defined` (Q4 first). -/
def valueEqBFuel' : Nat → Ty → Value D → Value D → M Bool
  | 0, _, _, _ => quit .q11Internal
  | _ + 1, .bool, .bool left, .bool right => do
      match D.toBool? left, D.toBool? right with
      | some l, some r => .ok (l == r)
      | _, _ => quit .q8MapSym
  | _ + 1, .bool, .atom _, _ => quit .q10Atom
  | _ + 1, .bool, _, .atom _ => quit .q10Atom
  | _ + 1, .bool, _, _ => quit .q11Internal
  | _ + 1, .int _, .int left _, .int right _ => do
      match D.toInt? left, D.toInt? right with
      | some l, some r => .ok (l == r)
      | _, _ => quit .q8MapSym
  | _ + 1, .int _, .atom _, _ => quit .q10Atom
  | _ + 1, .int _, _, .atom _ => quit .q10Atom
  | _ + 1, .int _, _, _ => quit .q11Internal
  | _ + 1, .float kind, .float lb lk, .float rb rk =>
      if lk == kind && rk == kind then
        match kind with
        | .float64 => .ok (FloatBits.feq64 lb rb)
        | .float32 => .ok (FloatBits.feq32 lb rb)
      else quit .q11Internal
  | _ + 1, .float _, .atom _, _ => quit .q10Atom
  | _ + 1, .float _, _, .atom _ => quit .q10Atom
  | _ + 1, .float _, _, _ => quit .q11Internal
  | _ + 1, .string, .string left, .string right => .ok (left == right)
  | _ + 1, .string, .atom _, _ => quit .q10Atom
  | _ + 1, .string, _, .atom _ => quit .q10Atom
  | _ + 1, .string, _, _ => quit .q11Internal
  | _ + 1, .funcType _ _, .nil, .nil => .ok true
  | _ + 1, .funcType _ _, .funcVal _ _, .nil => .ok false
  | _ + 1, .funcType _ _, .nil, .funcVal _ _ => .ok false
  | _ + 1, .funcType _ _, .atom _, _ => quit .q10Atom
  | _ + 1, .funcType _ _, _, .atom _ => quit .q10Atom
  | _ + 1, .funcType _ _, _, _ => quit .q11Internal
  | _ + 1, .pointer _, .addr left, .addr right => .ok (left == right)
  | _ + 1, .pointer _, .nil, .nil => .ok true
  | _ + 1, .pointer _, .addr _, .nil => .ok false
  | _ + 1, .pointer _, .nil, .addr _ => .ok false
  | _ + 1, .pointer _, .atom _, _ => quit .q10Atom
  | _ + 1, .pointer _, _, .atom _ => quit .q10Atom
  | _ + 1, .pointer _, _, _ => quit .q11Internal
  | fuel + 1, .array length elem, .array left, .array right => do
      if left.size != length then quit .q11Internal
      else if right.size != length then quit .q11Internal
      else
        valueEqListWith' (valueEqBFuel' fuel elem) left.toList right.toList
  | _ + 1, .array _ _, .atom _, _ => quit .q10Atom
  | _ + 1, .array _ _, _, .atom _ => quit .q10Atom
  | _ + 1, .array _ _, _, _ => quit .q11Internal
  | _ + 1, .slice _, .slice left, .slice right => do
      validateSlice' left
      validateSlice' right
      match left.base, right.base with
      | none, none => .ok true
      | none, some _ => .ok false
      | some _, none => .ok false
      | some _, some _ => quit .q11Internal
  | _ + 1, .slice _, .slice left, .nil => do
      validateSlice' left
      .ok left.base.isNone
  | _ + 1, .slice _, .nil, .slice right => do
      validateSlice' right
      .ok right.base.isNone
  | _ + 1, .slice _, .atom _, _ => quit .q10Atom
  | _ + 1, .slice _, _, .atom _ => quit .q10Atom
  | _ + 1, .slice _, _, _ => quit .q11Internal
  | _ + 1, .map _ _, .map left, .map right =>
      (match left.base, right.base with
       | none, none => .ok true
       | none, some _ => .ok false
       | some _, none => .ok false
       | some _, some _ => quit .q11Internal)
  | _ + 1, .map _ _, .map left, .nil => .ok left.base.isNone
  | _ + 1, .map _ _, .nil, .map right => .ok right.base.isNone
  | _ + 1, .map _ _, .atom _, _ => quit .q10Atom
  | _ + 1, .map _ _, _, .atom _ => quit .q10Atom
  | _ + 1, .map _ _, _, _ => quit .q11Internal
  | _ + 1, .chan _ _, .chan left, .chan right => .ok (left == right)
  | _ + 1, .chan _ _, .chan left, .nil => .ok left.base.isNone
  | _ + 1, .chan _ _, .nil, .chan right => .ok right.base.isNone
  | _ + 1, .chan _ _, .nil, .nil => .ok true
  | _ + 1, .chan _ _, .atom _, _ => quit .q10Atom
  | _ + 1, .chan _ _, _, .atom _ => quit .q10Atom
  | _ + 1, .chan _ _, _, _ => quit .q11Internal
  | _ + 1, .interface _, _, _ => quit .q4Program
  | _ + 1, .sync _, _, _ => quit .q11Internal
  | _ + 1, .defined _, _, _ => quit .q4Program
  | _ + 1, .unsupported _, _, _ => quit .q11Internal

def valueEqB' (ty : Ty) (left right : Value D) : M Bool :=
  valueEqBFuel' typeResolutionFuel ty left right

/-- The VALUE-producing equality (the `eqCmp`/`neqCmp` strict ops,
design §1.2 "stored = constructor"): int operands form `eqI` TERMS
(never quit); every other type routes through the decided family and
injects the literal — so fully-concrete comparisons compute exactly
where today's `rfl` does. -/
def valueEqR' (ty : Ty) (left right : Value D) : M D.BoolR :=
  match ty, left, right with
  | .int _, .int l _, .int r _ => .ok (D.eqI l r)
  | ty, l, r => do
      let b ← valueEqB' ty l r
      .ok (D.litB b)

/-! ## Comparison and arithmetic result helpers (mirrors of
`Ops.lean`'s operator-result family) -/

/-- Mirror of `intBinaryResult` at a payload former: kinds are concrete
metadata; result kind and success are payload-independent (design
§1.1 A). -/
def intBinaryResult' (op : D.IntR → D.IntR → D.IntR) (left right : Value D) :
    M (Value D) := do
  let (leftValue, leftKind) ← left.asIntR
  let (rightValue, rightKind) ← right.asIntR
  match IntKind.compatibleResult leftKind rightKind with
  | some kind => .ok (.int (D.norm kind (op leftValue rightValue)) kind)
  | none => quit .q11Internal

/-- Float dispatch mirror of `floatBinaryResult` (concrete payloads). -/
def floatBinaryResult' (op64 op32 : Nat → Nat → Nat) (left right : Value D) :
    M (Value D) := do
  match left, right with
  | .float lb lk, .float rb rk =>
      if lk == rk then
        match lk with
        | .float64 => .ok (.float (FloatKind.float64.normalizeBits (op64 lb rb)) .float64)
        | .float32 => .ok (.float (FloatKind.float32.normalizeBits (op32 lb rb)) .float32)
      else quit .q11Internal
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-- Float comparison dispatch (concrete payloads; mirror of
`floatCompareResult`'s float/float body — callers handle non-float
heads). -/
def floatCompareResult' (cmp64 cmp32 : Nat → Nat → Bool) (lb : Nat)
    (lk : FloatKind) (rb : Nat) (rk : FloatKind) : M Bool :=
  if lk == rk then
    match lk with
    | .float64 => .ok (cmp64 lb rb)
    | .float32 => .ok (cmp32 lb rb)
  else quit .q11Internal

/-- Mirror of `valueLess` as a stored value: int → `ltI` term; float/
string → concrete literal. -/
def valueLess' : Value D → Value D → M D.BoolR
  | .int left _, .int right _ => .ok (D.ltI left right)
  | .float lb lk, .float rb rk => do
      let b ← floatCompareResult' FloatBits.flt64 FloatBits.flt32 lb lk rb rk
      .ok (D.litB b)
  | .string left, .string right =>
      .ok (D.litB (GoString.compare left right == .lt))
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-- Mirror of `valueAtMost`. -/
def valueAtMost' : Value D → Value D → M D.BoolR
  | .int left _, .int right _ => .ok (D.leI left right)
  | .float lb lk, .float rb rk => do
      let b ← floatCompareResult' FloatBits.fle64 FloatBits.fle32 lb lk rb rk
      .ok (D.litB b)
  | .string left, .string right =>
      .ok (D.litB (GoString.compare left right != .gt))
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-- Mirror of `valueGreater` (operand swap on the int former — the
machine's own `l > r = r < l` reading). -/
def valueGreater' : Value D → Value D → M D.BoolR
  | .int left _, .int right _ => .ok (D.ltI right left)
  | .float lb lk, .float rb rk => do
      let b ← floatCompareResult' (fun l r => FloatBits.flt64 r l)
        (fun l r => FloatBits.flt32 r l) lb lk rb rk
      .ok (D.litB b)
  | .string left, .string right =>
      .ok (D.litB (GoString.compare left right == .gt))
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-- Mirror of `valueAtLeast`. -/
def valueAtLeast' : Value D → Value D → M D.BoolR
  | .int left _, .int right _ => .ok (D.leI right left)
  | .float lb lk, .float rb rk => do
      let b ← floatCompareResult' (fun l r => FloatBits.fle64 r l)
        (fun l r => FloatBits.fle32 r l) lb lk rb rk
      .ok (D.litB b)
  | .string left, .string right =>
      .ok (D.litB (GoString.compare left right != .lt))
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-- Decided `<` for the min/max folds and `sortSlice` (Q9 zone): the
stored-comparison former followed by an inspection. -/
def valueLessB' (l r : Value D) : M Bool := do
  let b ← valueLess' l r
  match D.toBool? b with
  | some x => .ok x
  | none => quit .q9Aggregate

/-- Bitwise/shift ops are OUT of the v1 term set (ruled OQ5): both
operands must close, the result computes concretely through the GoCore
helper and re-injects as a literal — so fully-concrete windows never
quit — else Q5. `lift` is the GoCore computation at closed operands. -/
def closedIntOp (lift : Int → IntKind → Int → IntKind → Except GoError GoValue)
    (left right : Value D) : M (Value D) := do
  match left, right with
  | .int lv lk, .int rv rk =>
      match D.toInt? lv, D.toInt? rv with
      | some l, some r =>
          match lift l lk r rk with
          | .ok (.int n kind) => .ok (.int (D.litI n) kind)
          | .ok _ => quit .q11Internal
          | .error (.panic _) => quit .q6Panic
          | .error _ => quit .q11Internal
      | _, _ => quit .q5OpPayload
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-! ## Heap access (mirrors of `loadLoc`/`storeLoc`) -/

def StructFields.lookup' (fields : Array (String × Value D)) (needle : String) :
    Option (Value D) :=
  fields.foldl
    (fun found (name, value) =>
      match found with
      | some value => some value
      | none => if name == needle then some value else none)
    none

def StructFields.set' (fields : Array (String × Value D)) (needle : String)
    (value : Value D) : M (Array (String × Value D)) := do
  let mut out := #[]
  let mut found := false
  for (name, old) in fields do
    if name == needle then
      out := out.push (name, value)
      found := true
    else
      out := out.push (name, old)
  if found then
    return out
  else
    quit .q11Internal

def arrayGet' (values : Array (Value D)) (index : Int) : M (Value D) := do
  let i ← arrayIndexNat' values.size index
  match values[i]? with
  | some value => .ok value
  | none => quit .q6Panic

def arraySet' (values : Array (Value D)) (index : Int) (value : Value D) :
    M (Array (Value D)) := do
  let i ← arrayIndexNat' values.size index
  match values[i]? with
  | some old => do
      let coerced ← coerceStoredValue' old value
      .ok (values.set! i coerced)
  | none => quit .q6Panic

def loadLoc' (s : State D) : Loc → M (Value D)
  | loc@(.base _) =>
      match Heap.lookup s.heap loc with
      | some (.mk _ value) => .ok value
      | some (.atom _) => quit .q10Atom
      | none => quit .q11Internal
  | .field base typeId fieldName => do
      match ← loadLoc' s base with
      | .struct actualType fields =>
          if actualType != typeId then quit .q11Internal
          else
            match StructFields.lookup' fields fieldName with
            | some value => .ok value
            | none => quit .q11Internal
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .index base index => do
      match ← loadLoc' s base with
      | .array values => arrayGet' values index
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal

def storeLoc' (s : State D) : Loc → Value D → M (State D)
  | loc@(.base _), value => do
      match Heap.lookup s.heap loc with
      | some (.mk declaredTy oldValue) => do
          let value ←
            match declaredTy with
            | some ty => normalizeValueForTy' ty value
            | none => coerceStoredValue' oldValue value
          .ok { s with heap := Heap.set s.heap loc (.mk declaredTy value) }
      | some (.atom _) => quit .q10Atom
      | none =>
          .ok { s with heap := Heap.set s.heap loc (.mk none value) }
  | .field base typeId fieldName, value => do
      match ← loadLoc' s base with
      | .struct actualType fields =>
          if actualType != typeId then quit .q11Internal
          else do
            let updated ← StructFields.set' fields fieldName value
            storeLoc' s base (.struct actualType updated)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .index base index, value => do
      match ← loadLoc' s base with
      | .array values => do
          let updated ← arraySet' values index value
          storeLoc' s base (.array updated)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal

def loadMany' (s : State D) : List Loc → M (List (Value D))
  | [] => .ok []
  | loc :: locs => do
      let v ← loadLoc' s loc
      let vs ← loadMany' s locs
      .ok (v :: vs)

/-- Mirror of `allocDecls` (block-entry declarations). -/
def allocDecls' : LocalEnv → State D → List Param → M (LocalEnv × State D)
  | env, s, [] => .ok (env, s)
  | env, s, p :: rest => do
      let v ← defaultValue' p.typ
      let (loc, s₁) := s.alloc v (some p.typ)
      allocDecls' (env.declare p.id loc) s₁ rest

/-! ## Slice / map machinery -/

def sliceVisibleValues' (s : State D) (slice : SliceValue) :
    M (Array (Value D)) := do
  validateSlice' slice
  let mut values := #[]
  for i in [:slice.len] do
    let loc ← sliceIndexLoc' slice (Int.ofNat i)
    values := values.push (← loadLoc' s loc)
  return values

/-- Element-wise hashability at the (already fuel-decremented) checker —
the de-WF recipe's list shape (`isNormalListWith'`'s twin). -/
def hashabilityListWith' (f : Value D → M Bool) : List (Value D) → M Bool
  | [] => .ok true
  | v :: rest => do
      let b ← f v
      if b then hashabilityListWith' f rest else .ok false

/-- Mirror of `valueHashability` (VALUE-directed walk), on the FUEL
recipe (phase-2 delta, log JC-8: GoCore's mutual walk recurses through
`fields.toList` — WF-compiled, kernel-irreducible — so the mirror
trades that shape for fuel exactly as `coerceStoredValueFuel'` does;
fuel bounds nesting DEPTH, exhaustion quits Q11, a conservative quit no
real key reaches at `typeResolutionFuel`). Interfaces need the type
environment (Q4); atoms cannot answer (Q10); scalar and reference
shapes are hashable. GoCore answers `.hashable` exactly where this
answers `.ok true`; `.ok false` is unreachable from the leaves (kept
for the list helper's shape parity). -/
def valueHashabilityFuel' : Nat → Value D → M Bool
  | 0, _ => quit .q11Internal
  | _ + 1, .interface _ _ => quit .q4Program
  | fuel + 1, .struct _ fields =>
      hashabilityListWith' (valueHashabilityFuel' fuel)
        (fields.toList.map Prod.snd)
  | fuel + 1, .array values =>
      hashabilityListWith' (valueHashabilityFuel' fuel) values.toList
  | _ + 1, .atom _ => quit .q10Atom
  | _ + 1, _ => .ok true

@[inherit_doc valueHashabilityFuel']
def valueHashability' (v : Value D) : M Bool :=
  valueHashabilityFuel' typeResolutionFuel v

/-- Mirror of `checkKeyHashable`: an unhashable key is a PANIC (Q6). -/
def checkKeyHashable' (key : Value D) : M Unit := do
  let b ← valueHashability' key
  if b then .ok () else quit .q6Panic

/-- Mirror of `mapEntryIndex?` — the key scan, at DECIDED equality
(concrete keys compute; symbolic keys quit Q8 through the decided
family). -/
def mapEntryIndex?' (keyTy : Ty) (entries : Array (Value D × Value D))
    (key : Value D) : M (Option Nat) := do
  checkKeyHashable' key
  let mut i := 0
  for (entryKey, _) in entries do
    let hit ← valueEqB' keyTy entryKey key
    if hit then
      return some i
    i := i + 1
  return none

def mapEntries' (s : State D) (map : MapValue) :
    M (Option (Loc × Array (Value D × Value D))) := do
  match map.base with
  | none => .ok none
  | some baseLoc =>
      match ← loadLoc' s baseLoc with
      | .mapData entries => .ok (some (baseLoc, entries))
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal

def mapLookupValue' (s : State D) (map : MapValue) (key : Value D)
    (keyTy valueTy : Ty) : M (Value D × Bool) := do
  match ← mapEntries' s map with
  | none => do
      checkKeyHashable' key
      let zero ← defaultValue' valueTy
      .ok (zero, false)
  | some (_, entries) =>
      match ← mapEntryIndex?' keyTy entries key with
      | some i =>
          match entries[i]? with
          | some (_, value) => .ok (value, true)
          | none => quit .q11Internal
      | none => do
          let zero ← defaultValue' valueTy
          .ok (zero, false)

/-- Mirror of `mapAssignValue` (concrete keys, symbolic values fine —
design table row "map get/assign/delete — concrete key"). -/
def mapAssignValue' (s : State D) (keyTy valueTy : Ty)
    (baseV keyV valueV : Value D) : M (State D) := do
  let map ← baseV.asMap
  let key ← normalizeValueForTy' keyTy keyV
  let value ← normalizeValueForTy' valueTy valueV
  match ← mapEntries' s map with
  | none => quit .q6Panic
  | some (baseLoc, entries) =>
      let entries ←
        match ← mapEntryIndex?' keyTy entries key with
        | some i => pure (entries.set! i (key, value))
        | none => pure (entries.push (key, value))
      storeLoc' s baseLoc (.mapData entries)

/-! ## Address-chain machinery (mirrors of the target-store spine) -/

/-- Mirror of `indexTargetLoc` (the shared element-location former). -/
def indexTargetLoc' (s : State D) (b i : Value D) : M Loc := do
  let indexValue ← i.asIntAt .q2Address
  match b with
  | .slice slice => sliceIndexLoc' slice indexValue
  | .nil => quit .q6Panic
  | .addr baseLoc =>
      (match ← loadLoc' s baseLoc with
       | .array values => do
          let _ ← arrayIndexNat' values.size indexValue
          .ok (.index baseLoc indexValue)
       | .slice slice => sliceIndexLoc' slice indexValue
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- Mirror of `completeTargetRef` (arity check on the shape). -/
def completeTargetRef' : TargetShape → List (Value D) → Option (TargetRef D)
  | .chain steps, anchor :: idxs =>
      if idxs.length = indexStepCount steps then
        some (.chain anchor idxs steps)
      else none
  | .mapElem kt vt, [b, k] => some (.mapElem b k kt vt)
  | _, _ => none

/-- Mirror of `resolveChain` (phase-2 chain replay). -/
def resolveChain' (s : State D) : Value D → List TargetStep → List (Value D) →
    M (Value D)
  | cur, [], [] => .ok cur
  | cur, .index :: steps, i :: idxs => do
      let loc ← indexTargetLoc' s cur i
      resolveChain' s (.addr loc) steps idxs
  | cur, .field tid f :: steps, idxs => do
      let loc ← cur.asLoc
      resolveChain' s (.addr (.field loc tid f)) steps idxs
  | _, _, _ => quit .q11Internal

/-- Mirror of `storeTarget` (phase 2, one store). -/
def storeTarget' (s : State D) (r : TargetRef D) (v : Value D) : M (State D) := do
  match r with
  | .chain anchor idxs steps => do
      let resolved ← resolveChain' s anchor steps idxs
      let loc ← resolved.asLoc
      storeLoc' s loc v
  | .mapElem b k kt vt => mapAssignValue' s kt vt b k v

/-- Mirror of `applyRhsOp` (comma-ok value sources; `typeAssert`
consults the type tables → Q4). -/
def applyRhsOp' (s : State D) : RhsOp → List (Value D) → M (List (Value D))
  | .vals, vs => .ok vs
  | .mapLookup keyTy valueTy, [baseV, keyV] => do
      let map ← baseV.asMap
      let key ← normalizeValueForTy' keyTy keyV
      let pair ← mapLookupValue' s map key keyTy valueTy
      .ok [pair.1, .bool (D.litB pair.2)]
  | .typeAssert _, [_] => quit .q4Program
  | _, _ => quit .q11Internal

/-! ## Continuation utilities (mirrors of the `Cont` walks the fragment
uses; the recover walk deliberately has NO mirror — JC-5a, Q6) -/

/-- Mirror of `seqCont` (the `.seqn` splicing rule). -/
def seqCont' (ss : List Stmt) (env : LocalEnv) : Cont D → Cont D
  | .seq rest env' k => if env' = env then .seq (ss ++ rest) env k
                        else .seq ss env (.seq rest env' k)
  | k => .seq ss env k

/-- Mirror of `contHeadLabel` (the labeled-loop test). -/
def contHeadLabel' : Cont D → Option String
  | .labelK name _ => some name
  | _ => none

/-- Mirror of `pushDefer` (defer registration walks to the innermost
frame). -/
def pushDefer' (d : Value D × List (Value D)) : Cont D → Option (Cont D)
  | .frame t te r ds k w => some (.frame t te r (d :: ds) k w)
  | .seq rest env k => (pushDefer' d k).map (Cont.seq rest env)
  | .loop c b env k => (pushDefer' d k).map (Cont.loop c b env)
  | .breakableK k => (pushDefer' d k).map Cont.breakableK
  | .labelK name k => (pushDefer' d k).map (Cont.labelK name)
  | .mapIterK kv vv kt vt b base prod st env k =>
      (pushDefer' d k).map (Cont.mapIterK kv vv kt vt b base prod st env)
  | _ => none

/-! ## The strict-op apply (mirror of `applyStrictOp`) -/

/-- Mirror of `applySlice` (slice-expression application at concrete
bounds — the caller projects them at Q2). -/
def applySlice' (s : State D) (b : Value D) (lowValue highValue : Int)
    (maxValue : Option Int) : M (Value D) := do
  match b with
  | .string value => stringSlice' value lowValue highValue maxValue
  | .slice slice => sliceFromSlice' slice lowValue highValue maxValue
  | .addr baseLoc =>
      (match ← loadLoc' s baseLoc with
       | .array values =>
          sliceFromArray' baseLoc values.size lowValue highValue maxValue
       | .slice slice => sliceFromSlice' slice lowValue highValue maxValue
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .atom _ => quit .q10Atom
  | _ => quit .q11Internal

/-- Mirror of `convertValueToTyFuel`. Int targets are `norm`
constructors; float→int / int→float need concrete payloads (Q5);
`.defined` targets consult the tables (Q4); reference-shape passes
mirror GoCore's arms. -/
def convertValueToTyFuel' : Nat → Ty → Value D → M (Value D)
  | _, .int kind, .int value _ => .ok (.int (D.norm kind value) kind)
  | _, .int kind, .float bits fk =>
      (let n? := match fk with
        | .float64 => FloatBits.f64truncInt? bits
        | .float32 => FloatBits.f32truncInt? bits
       match n? with
       | some n =>
          if kind.normalize n == n then .ok (.int (D.litI n) kind)
          else quit .q11Internal
       | none => quit .q11Internal)
  | _, .int _, .atom _ => quit .q10Atom
  | _, .int _, _ => quit .q11Internal
  | _, .float kind, .float bits fk =>
      (match kind, fk with
       | .float64, .float64 => .ok (.float (kind.normalizeBits bits) kind)
       | .float32, .float32 => .ok (.float (kind.normalizeBits bits) kind)
       | .float64, .float32 => .ok (.float (kind.normalizeBits (FloatBits.f32to64 bits)) kind)
       | .float32, .float64 => .ok (.float (kind.normalizeBits (FloatBits.f64to32 bits)) kind))
  | _, .float kind, .int value _ =>
      (match D.toInt? value with
       | some n => .ok (.float (kind.normalizeBits (kind.ratToBits n 1)) kind)
       | none => quit .q5OpPayload)
  | _, .float _, .atom _ => quit .q10Atom
  | _, .float _, _ => quit .q11Internal
  | _ + 1, .defined _, _ => quit .q4Program
  | _, .string, .string str => .ok (.string str)
  | _, .pointer _, .addr loc => .ok (.addr loc)
  | _, .pointer _, .nil => .ok .nil
  | _, .slice _, .slice sv => .ok (.slice sv)
  | _, .slice _, .nil =>
      .ok (.slice { base := none, offset := 0, len := 0, cap := 0 })
  | _, .map _ _, .map mv => .ok (.map mv)
  | _, .map _ _, .nil => .ok (.map { base := none })
  | _, .chan _ _, .chan cv => .ok (.chan cv)
  | _, .chan _ _, .nil => .ok (.chan { base := none })
  | _, .funcType _ _, .funcVal fid captured => .ok (.funcVal fid captured)
  | _, .funcType _ _, .nil => .ok .nil
  | _, .interface _, .interface dynTy inner => .ok (.interface dynTy inner)
  | _, .interface _, .nil => .ok .nil
  | 0, .defined _, _ => quit .q11Internal
  | _, _, .atom _ => quit .q10Atom
  | _, _, _ => quit .q11Internal

def convertValueToTy' (ty : Ty) (value : Value D) : M (Value D) :=
  convertValueToTyFuel' typeResolutionFuel ty value

/-- Mirror of `buildArrayValue` (array literals at concrete keys). -/
def buildArrayValue' (length : Nat) (elem : Ty)
    (args : Array (Int × Value D)) : M (Value D) := do
  let mut values := #[]
  for _ in [:length] do
    values := values.push (← defaultValue' (D := D) elem)
  let mut seen : Array Int := #[]
  for (key, value) in args do
    if seen.contains key then
      quit .q11Internal
    seen := seen.push key
    if key < 0 then
      quit .q11Internal
    match values[key.toNat]? with
    | some old => do
        let normalized ← normalizeValueForTy' elem value
        let coerced ← coerceStoredValue' old normalized
        values := values.set! key.toNat coerced
    | none => quit .q11Internal
  return .array values

def buildDefaultArrayValue' (length : Nat) (elem : Ty) : M (Value D) :=
  buildArrayValue' length elem #[]

def anyFloatOperand' (vs : List (Value D)) : Bool :=
  vs.any fun v => match v with | .float _ _ => true | _ => false

/-- Atom guard for the `min`/`max` arms (phase-2 fidelity fix, log
JC-9): an ATOM operand's concretization can be a float, so the
machine's float-head discrimination is undecidable at the mirror —
the arms must quit Q10 before the float guard, not ride an atom
through the fold's blind spots (the single-operand `min(x)` shape
never compares `x`). Found BY the drift walk — the commutation lemma
is false without it. -/
def anyAtomOperand' (vs : List (Value D)) : Bool :=
  vs.any fun v => match v with | .atom _ => true | _ => false

/-- Mirror of `floatMinMax` (triage L3): float bits are CONCRETE in the
mirror, so the selection delegates to the SAME `floatMinMaxBits`
kernel; the machine's stuck arms quit Q11 (atoms are excluded upstream
by `anyAtomOperand'`, and again here for the two-operand shape). -/
def floatMinMax' (isMin : Bool) : Value D → Value D → M (Value D)
  | .float a ka, .float b kb =>
      if ka == kb then .ok (.float (floatMinMaxBits isMin ka a b) ka)
      else quit .q11Internal
  | .atom _, _ => quit .q10Atom
  | _, .atom _ => quit .q10Atom
  | _, _ => quit .q11Internal

/-- Mirror of `applyStrictOp`, arm-for-arm in the same order. Quit
classes per the §1.4 table: comparisons/arith at ints are FORMERS;
bitwise/shift close-or-Q5; `structLit`/`toInterface`/`typeAssert`/
`defaultValueOf` at `.defined` are Q4; index material closes or Q2;
panics Q6; head mismatches Q11; atoms Q10. -/
def applyStrictOp' (s : State D) : StrictOp → List (Value D) →
    M (Value D × State D)
  | .add, [l, r] =>
      (match l, r with
       | .int .., .int .. => do
          let v ← intBinaryResult' D.add l r
          .ok (v, s)
       | .float .., .float .. => do
          let v ← floatBinaryResult' FloatBits.fadd64 FloatBits.fadd32 l r
          .ok (v, s)
       | .string lv, .string rv => .ok (.string (GoString.append lv rv), s)
       | .atom _, _ => quit .q10Atom
       | _, .atom _ => quit .q10Atom
       | _, _ => quit .q11Internal)
  | .sub, [l, r] =>
      (match l, r with
       | .float .., .float .. => do
          let v ← floatBinaryResult' FloatBits.fsub64 FloatBits.fsub32 l r
          .ok (v, s)
       | _, _ => do
          let v ← intBinaryResult' D.sub l r
          .ok (v, s))
  | .mul, [l, r] =>
      (match l, r with
       | .float .., .float .. => do
          let v ← floatBinaryResult' FloatBits.fmul64 FloatBits.fmul32 l r
          .ok (v, s)
       | _, _ => do
          let v ← intBinaryResult' D.mul l r
          .ok (v, s))
  | .div, [l, r] =>
      (match l, r with
       | .float .., .float .. => do
          let v ← floatBinaryResult' FloatBits.fdiv64 FloatBits.fdiv32 l r
          .ok (v, s)
       | _, _ => do
          -- The divisor is a CONTROL decision (zero test): it must
          -- close (Q5); the dividend stays a term (`divC`).
          let divisor ← r.asIntAt .q5OpPayload
          if divisor == 0 then quit .q6Panic
          else do
            let (lv, lk) ← l.asIntR
            let (_, rk) ← r.asIntR
            match IntKind.compatibleResult lk rk with
            | some kind => .ok (.int (D.norm kind (D.divC lv divisor)) kind, s)
            | none => quit .q11Internal)
  | .mod, [l, r] => do
      let divisor ← r.asIntAt .q5OpPayload
      if divisor == 0 then quit .q6Panic
      else do
        let (lv, lk) ← l.asIntR
        let (_, rk) ← r.asIntR
        match IntKind.compatibleResult lk rk with
        | some kind => .ok (.int (D.norm kind (D.modC lv divisor)) kind, s)
        | none => quit .q11Internal
  | .shiftLeft, [l, r] => do
      let v ← closedIntOp
        (fun lv lk rv rk => intShiftLeftResult (.int lv lk) (.int rv rk)) l r
      .ok (v, s)
  | .shiftRight, [l, r] => do
      let v ← closedIntOp
        (fun lv lk rv rk => intShiftRightResult (.int lv lk) (.int rv rk)) l r
      .ok (v, s)
  | .bitAnd, [l, r] => do
      let v ← closedIntOp
        (fun lv lk rv rk => intBitwiseBinaryResult "&" Nat.land (.int lv lk) (.int rv rk)) l r
      .ok (v, s)
  | .bitOr, [l, r] => do
      let v ← closedIntOp
        (fun lv lk rv rk => intBitwiseBinaryResult "|" Nat.lor (.int lv lk) (.int rv rk)) l r
      .ok (v, s)
  | .bitXor, [l, r] => do
      let v ← closedIntOp
        (fun lv lk rv rk => intBitwiseBinaryResult "^" Nat.xor (.int lv lk) (.int rv rk)) l r
      .ok (v, s)
  | .bitClear, [l, r] => do
      let v ← closedIntOp
        (fun lv lk rv rk => intBitClearResult (.int lv lk) (.int rv rk)) l r
      .ok (v, s)
  | .bitNeg, [v] =>
      (match v with
       | .int value kind =>
          (match D.toInt? value with
           | some n =>
              (match intBitNegResult (.int n kind) with
               | .ok (.int m mk) => .ok (.int (D.litI m) mk, s)
               | .ok _ => quit .q11Internal
               | .error _ => quit .q11Internal)
           | none => quit .q5OpPayload)
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .neg, [v] =>
      (match v with
       | .int value kind => .ok (.int (D.norm kind (D.neg value)) kind, s)
       | .float bits kind =>
          .ok (.float (kind.normalizeBits (kind.negBits bits)) kind, s)
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .floatLit num den kind, [] =>
      if den == 0 then quit .q11Internal
      else .ok (.float (kind.normalizeBits (kind.ratToBits num den)) kind, s)
  | .not, [v] => do
      match v with
      | .bool b => .ok (.bool (D.notB b), s)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .eqCmp ty, [l, r] => do
      let b ← valueEqR' ty l r
      .ok (.bool b, s)
  | .neqCmp ty, [l, r] => do
      let b ← valueEqR' ty l r
      .ok (.bool (D.notB b), s)
  | .atMostCmp, [l, r] => do
      let b ← valueAtMost' l r
      .ok (.bool b, s)
  | .atLeastCmp, [l, r] => do
      let b ← valueAtLeast' l r
      .ok (.bool b, s)
  | .lessCmp, [l, r] => do
      let b ← valueLess' l r
      .ok (.bool b, s)
  | .greaterCmp, [l, r] => do
      let b ← valueGreater' l r
      .ok (.bool b, s)
  | .convert ty, [v] => do
      let v' ← convertValueToTy' ty v
      .ok (v', s)
  | .bytesFromString, [v] =>
      (match v with
       | .string value =>
          let bytes := value.bytes.map
            (fun b => Value.int (D := D) (D.litI (Int.ofNat b.toNat)) .uint8)
          let (base, s') := s.alloc (.array bytes)
            (some (.array bytes.size (.int .uint8)))
          .ok (.slice { base := some base, offset := 0,
                        len := bytes.size, cap := bytes.size }, s')
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .stringFromByteSlice, [v] => do
      let slice ← v.asSlice
      let values ← sliceVisibleValues' s slice
      let mut bytes := #[]
      for value in values do
        match value with
        | .int byteR .uint8 =>
            match D.toInt? byteR with
            | some byte =>
                if byte < 0 || byte > 255 then
                  quit .q11Internal
                bytes := bytes.push (UInt8.ofNat byte.toNat)
            | none => quit .q5OpPayload
        | .atom _ => quit .q10Atom
        | _ => quit .q11Internal
      return (.string { bytes := bytes }, s)
  | .stringFromRune, [v] => do
      let code ← v.asIntAt .q5OpPayload
      .ok (.string (GoString.fromCodePoint code), s)
  | .deref _, [v] => do
      let loc ← v.asLoc
      let value ← loadLoc' s loc
      .ok (value, s)
  | .addrOfDeref, [v] => do
      -- BUG-056: the nil-vs-addr decision is on the value STRUCTURE
      -- (`asLoc`: `.addr` computes, `.nil` quits Q6 like every
      -- machine panic, atoms quit Q10) — no scalar payload, no load.
      let loc ← v.asLoc
      .ok (.addr loc, s)
  | .fieldGet typeId fieldName, [v] => do
      match v with
      | .struct actualType fields =>
          if actualType != typeId then quit .q11Internal
          else
            match StructFields.lookup' fields fieldName with
            | some value => .ok (value, s)
            | none => quit .q11Internal
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .fieldAddr typeId fieldName, [v] => do
      let loc ← v.asLoc
      .ok (.addr (.field loc typeId fieldName), s)
  | .structLit _, _ => quit .q4Program
  | .arrayLit n elem keys, vs => do
      if keys.length != vs.length then quit .q11Internal
      else do
        let v ← buildArrayValue' n elem (keys.zip vs).toArray
        .ok (v, s)
  | .toInterface _ _, [_] => quit .q4Program
  | .typeAssert _ _, [_] => quit .q4Program
  | .indexGet, [b, i] => do
      let indexValue ← i.asIntAt .q2Address
      match b with
      | .array values => do
          let v ← arrayGet' values indexValue
          .ok (v, s)
      | .string value => do
          let v ← stringByteGet' value indexValue
          .ok (v, s)
      | .slice slice => do
          let loc ← sliceIndexLoc' slice indexValue
          let v ← loadLoc' s loc
          .ok (v, s)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .indexAddr, [b, i] => do
      let loc ← indexTargetLoc' s b i
      .ok (.addr loc, s)
  | .mapGet keyTy valueTy, [b, i] => do
      let map ← b.asMap
      let key ← normalizeValueForTy' keyTy i
      match map.base with
      | none => do
          checkKeyHashable' key
          let zero ← defaultValue' valueTy
          .ok (zero, s)
      | some baseLoc =>
          (match ← loadLoc' s baseLoc with
           | .mapData entries => do
              match ← mapEntryIndex?' keyTy entries key with
              | some idx =>
                  match entries[idx]? with
                  | some (_, value) => .ok (value, s)
                  | none => quit .q11Internal
              | none => do
                  let zero ← defaultValue' valueTy
                  .ok (zero, s)
           | .atom _ => quit .q10Atom
           | _ => quit .q11Internal)
  | .sliceExpr false, [b, lo, hi] => do
      let lowValue ← lo.asIntAt .q2Address
      let highValue ← hi.asIntAt .q2Address
      let v ← applySlice' s b lowValue highValue none
      .ok (v, s)
  | .sliceExpr true, [b, lo, hi, m] => do
      let lowValue ← lo.asIntAt .q2Address
      let highValue ← hi.asIntAt .q2Address
      let maxValue ← m.asIntAt .q2Address
      let v ← applySlice' s b lowValue highValue (some maxValue)
      .ok (v, s)
  | .lengthOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) => .ok (.int (D.litI n) .int, s)
      | _ =>
          match v with
          | .array values => .ok (.int (D.litI values.size) .int, s)
          | .addr baseLoc =>
              (match ← loadLoc' s baseLoc with
               | .array values => .ok (.int (D.litI values.size) .int, s)
               | .atom _ => quit .q10Atom
               | _ => quit .q11Internal)
          | .string value => .ok (.int (D.litI value.length) .int, s)
          | .slice slice => do
              validateSlice' slice
              .ok (.int (D.litI slice.len) .int, s)
          | .map map =>
              (match map.base with
               | none => .ok (.int (D.litI 0) .int, s)
               | some baseLoc => do
                  match ← loadLoc' s baseLoc with
                  | .mapData entries => .ok (.int (D.litI entries.size) .int, s)
                  | .atom _ => quit .q10Atom
                  | _ => quit .q11Internal)
          | .chan ch =>
              (match ch.base with
               | none => .ok (.int (D.litI 0) .int, s)
               | some baseLoc => do
                  match ← loadLoc' s baseLoc with
                  | .chanData buf _ _ => .ok (.int (D.litI buf.size) .int, s)
                  | .atom _ => quit .q10Atom
                  | _ => quit .q11Internal)
          | .atom _ => quit .q10Atom
          | _ => quit .q11Internal
  | .capacityOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) => .ok (.int (D.litI n) .int, s)
      | _ =>
          match v with
          | .array values => .ok (.int (D.litI values.size) .int, s)
          | .addr baseLoc =>
              (match ← loadLoc' s baseLoc with
               | .array values => .ok (.int (D.litI values.size) .int, s)
               | .atom _ => quit .q10Atom
               | _ => quit .q11Internal)
          | .slice slice => do
              validateSlice' slice
              .ok (.int (D.litI slice.cap) .int, s)
          | .chan ch =>
              (match ch.base with
               | none => .ok (.int (D.litI 0) .int, s)
               | some baseLoc => do
                  match ← loadLoc' s baseLoc with
                  | .chanData _ capacity _ => .ok (.int (D.litI capacity) .int, s)
                  | .atom _ => quit .q10Atom
                  | _ => quit .q11Internal)
          | .atom _ => quit .q10Atom
          | _ => quit .q11Internal
  | .funcValOf fid, vs => .ok (.funcVal fid vs, s)
  | .minOf, v :: vs =>
      if anyAtomOperand' (v :: vs) then quit .q10Atom
      else if anyFloatOperand' (v :: vs) then do
        -- the IEEE float fold (triage L3), transcribed — bits concrete
        let mut best := v
        for w in vs do
          best ← floatMinMax' true best w
        return (best, s)
      else do
        let mut best := v
        for w in vs do
          let lt ← valueLessB' w best
          if lt then
            best := w
        return (best, s)
  | .maxOf, v :: vs =>
      if anyAtomOperand' (v :: vs) then quit .q10Atom
      else if anyFloatOperand' (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax' false best w
        return (best, s)
      else do
        let mut best := v
        for w in vs do
          let lt ← valueLessB' best w
          if lt then
            best := w
        return (best, s)
  | .runeAt, [sv, ov] => do
      match sv with
      | .string str => do
          let off ← ov.asIntAt .q5OpPayload
          if off < 0 then quit .q11Internal
          else .ok (.int (D.litI (decodeRuneAt str off.toNat).1) .int32, s)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .runeSizeAt, [sv, ov] => do
      match sv with
      | .string str => do
          let off ← ov.asIntAt .q5OpPayload
          if off < 0 then quit .q11Internal
          else .ok (.int (D.litI (Int.ofNat (decodeRuneAt str off.toNat).2)) .int, s)
      | .atom _ => quit .q10Atom
      | _ => quit .q11Internal
  | .defaultValueOf ty, [] => do
      let v ← defaultValue' ty
      .ok (v, s)
  | .nilLit typ, [] =>
      (match typ with
       | none => .ok (.nil, s)
       | some ty =>
          match ty with
          | .slice _ => do
              let v ← defaultValue' (D := D) ty
              .ok (v, s)
          | .map _ _ => do
              let v ← defaultValue' (D := D) ty
              .ok (v, s)
          | .chan _ _ => do
              let v ← defaultValue' (D := D) ty
              .ok (v, s)
          | .pointer _ => .ok (.nil, s)
          | .unsupported _ => quit .q11Internal
          | _ => quit .q11Internal)
  -- `[]rune(s)` / `string([]rune)` (triage L1, 2026-08-19): transcribed
  -- from the machine arms. Strings are concrete in the mirror, so the
  -- decode kernel runs as-is; rune elements are payloads that must
  -- close (Q5), exactly the byte-loop treatment.
  | .runesFromString, [v] =>
      (match v with
       | .string value =>
          let runes := (runesOfString value).map
            (fun r => Value.int (D := D) (D.litI r) .int32)
          let (base, s') := s.alloc (.array runes)
            (some (.array runes.size (.int .int32)))
          .ok (.slice { base := some base, offset := 0,
                        len := runes.size, cap := runes.size }, s')
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)
  | .stringFromRuneSlice, [v] => do
      let slice ← v.asSlice
      let values ← sliceVisibleValues' s slice
      let mut str := GoString.empty
      for value in values do
        match value with
        | .int rR .int32 =>
            match D.toInt? rR with
            | some r => str := str.append (GoString.fromCodePoint r)
            | none => quit .q5OpPayload
        | .atom _ => quit .q10Atom
        | _ => quit .q11Internal
      return (.string str, s)
  | _, _ => quit .q11Internal

/-! ## Wide-statement apply (mirror of `applyStmtOpCore`/`applyStmtOp`) -/

/-- Mirror of `applyStmtOpCore` (choices-free wide ops). Sizes must
close (Q5); keys decide (Q8); `sortSlice` elements must close (Q9). -/
def applyStmtOpCore' (s : State D) (op : StmtOp) (vs : List (Value D)) :
    M (State D) := do
  match op with
  | .newValue typ =>
      (match vs with
       | [tv, value] => do
          let loc ← tv.asLoc
          let (nloc, s₁) := s.alloc value typ
          storeLoc' s₁ loc (.addr nloc)
       | _ => quit .q11Internal)
  | .makeSlice elem hasCap => do
      let (tv, lenV, capV?) ←
        match vs, hasCap with
        | [tv, lenV], false => pure (tv, lenV, none)
        | [tv, lenV, capV], true => pure (tv, lenV, some capV)
        | _, _ => quit .q11Internal
      let lenValue ← lenV.asIntAt .q5OpPayload
      let capValue ←
        match capV? with
        | none => pure lenValue
        | some capV => capV.asIntAt .q5OpPayload
      if lenValue < 0 then quit .q6Panic
      else if capValue < 0 then quit .q6Panic
      else do
        let len := lenValue.toNat
        let cap := capValue.toNat
        if cap < len then quit .q6Panic
        else do
          let backing ← buildDefaultArrayValue' cap elem
          let (base, s₁) := s.alloc backing (some (.array cap elem))
          let loc ← tv.asLoc
          storeLoc' s₁ loc (.slice { base := some base, offset := 0, len, cap })
  | .makeMap hasSpace => do
      let (tv, spaceV?) ←
        match vs, hasSpace with
        | [tv], false => pure (tv, none)
        | [tv, spaceV], true => pure (tv, some spaceV)
        | _, _ => quit .q11Internal
      match spaceV? with
      | none => pure ()
      | some spaceV => do
          let size ← spaceV.asIntAt .q5OpPayload
          if size < 0 then quit .q6Panic else pure ()
      let (base, s₁) := s.alloc (.mapData #[])
      let loc ← tv.asLoc
      storeLoc' s₁ loc (.map { base := some base })
  | .makeChan hasCap => do
      let (tv, capV?) ←
        match vs, hasCap with
        | [tv], false => pure (tv, none)
        | [tv, capV], true => pure (tv, some capV)
        | _, _ => quit .q11Internal
      let capacity ←
        match capV? with
        | none => pure 0
        | some capV => do
            let size ← capV.asIntAt .q5OpPayload
            if size < 0 then quit .q6Panic else pure size.toNat
      let (base, s₁) := s.alloc (.chanData #[] capacity false)
      let loc ← tv.asLoc
      storeLoc' s₁ loc (.chan { base := some base })
  | .mapAssign keyTy valueTy =>
      (match vs with
       | [baseV, keyV, valueV] => mapAssignValue' s keyTy valueTy baseV keyV valueV
       | _ => quit .q11Internal)
  | .mapDelete keyTy =>
      (match vs with
       | [baseV, keyV] => do
          let map ← baseV.asMap
          let key ← normalizeValueForTy' keyTy keyV
          match ← mapEntries' s map with
          | none => do
              checkKeyHashable' key
              .ok s
          | some (baseLoc, entries) =>
              (match ← mapEntryIndex?' keyTy entries key with
               | some i => storeLoc' s baseLoc (.mapData (entries.eraseIdx! i))
               | none => .ok s)
       | _ => quit .q11Internal)
  | .clearMap =>
      (match vs with
       | [baseV] => do
          let map ← baseV.asMap
          match ← mapEntries' s map with
          | none => .ok s
          | some (baseLoc, _) => storeLoc' s baseLoc (.mapData #[])
       | _ => quit .q11Internal)
  | .clearSlice elem =>
      (match vs with
       | [baseV] => do
          let slice ← baseV.asSlice
          validateSlice' slice
          let zero ← defaultValue' elem
          let mut current := s
          for i in [:slice.len] do
            let loc ← sliceIndexLoc' slice (Int.ofNat i)
            current ← storeLoc' current loc zero
          return current
       | _ => quit .q11Internal)
  | .sortSlice _ =>
      (match vs with
       | [baseV] => do
          let slice ← baseV.asSlice
          validateSlice' slice
          let mut loaded : Array (Int × IntKind) := #[]
          let mut current := s
          for i in [:slice.len] do
            let loc ← sliceIndexLoc' slice (Int.ofNat i)
            match ← loadLoc' current loc with
            | .int vR kind =>
                match D.toInt? vR with
                | some v => loaded := loaded.push (v, kind)
                | none => quit .q9Aggregate
            | .atom _ => quit .q10Atom
            | _ => quit .q11Internal
          let sorted := (sortLe (fun a b => a.1 ≤ b.1) loaded.toList).toArray
          for i in [:slice.len] do
            match sorted[i]? with
            | some (v, kind) => do
                let loc ← sliceIndexLoc' slice (Int.ofNat i)
                current ← storeLoc' current loc (.int (D.litI v) kind)
            | none => quit .q11Internal
          return current
       | _ => quit .q11Internal)
  | .copySlice =>
      (match vs with
       | [tv, dstV, srcV] => do
          let dstSlice ← dstV.asSlice
          let srcSlice ← srcV.asSlice
          validateSlice' dstSlice
          validateSlice' srcSlice
          let count := Nat.min dstSlice.len srcSlice.len
          let mut values := #[]
          for i in [:count] do
            let loc ← sliceIndexLoc' srcSlice (Int.ofNat i)
            values := values.push (← loadLoc' s loc)
          let mut current := s
          let mut i := 0
          for value in values do
            let loc ← sliceIndexLoc' dstSlice (Int.ofNat i)
            current ← storeLoc' current loc value
            i := i + 1
          let tloc ← tv.asLoc
          storeLoc' current tloc (.int (D.litI count) .int)
       | _ => quit .q11Internal)
  | .appendSlice _ => quit .q11Internal

/-- Mirror of `applyStmtOp`: `appendSlice` computes IN-CAP (concrete
handle, concrete count — the store loop is address-concrete) and quits
Q3 at the SPILL (the capacity choice); everything else dispatches to
the choices-free core. The mirror takes no stream — that absence IS
the fragment's `ch`-invariance. -/
def applyStmtOp' (s : State D) (op : StmtOp) (vs : List (Value D)) :
    M (State D) := do
  match op with
  | .appendSlice _ =>
      (match vs with
       | [tv, sliceV, elemsV] => do
          let slice ← sliceV.asSlice
          let elems ← elemsV.asSlice
          validateSlice' slice
          validateSlice' elems
          let elemValues ← sliceVisibleValues' s elems
          let newLen := slice.len + elemValues.size
          let tloc ← tv.asLoc
          if newLen <= slice.cap then do
            let mut current := s
            let mut i := 0
            for value in elemValues do
              match slice.base with
              | some base =>
                  current ← storeLoc' current
                    (.index base (Int.ofNat (slice.offset + slice.len + i))) value
                  i := i + 1
              | none => quit .q11Internal
            storeLoc' current tloc (.slice { slice with len := newLen })
          else
            quit .q3Choice
       | _ => quit .q11Internal)
  | op => applyStmtOpCore' s op vs

/-! ## mapRange start (BUG-005 (L): base + start-key set; the snapshot
transcriptions are retired with the snapshot itself. The PICK quits Q3
at any nonempty cell — one more slot of the SAME consumption site.) -/

def mapRangeStartSets' (s : State D) (v : Value D) :
    M (Option Loc × Array (Value D)) := do
  let map ← v.asMap
  match map.base with
  | none => .ok (none, #[])
  | some base =>
      (match ← loadLoc' s base with
       | .mapData es => .ok (some base, es.map (·.1))
       | .atom _ => quit .q10Atom
       | _ => quit .q11Internal)

/-! ## THE MIRROR STEP -/

/-- One mirrored machine step (design §6.1's `stepFnS`, parametric in
the domain). TRANSCRIBED from `stepFn` arm-for-arm in the same match
order; every arm outside the v1 fragment quits with its catalog entry.
No choice stream: consuming sites quit Q3. Terminal configurations are
Q11 (the driver never calls on them; fail-closed if it did). -/
def stepFn' (s : State D) (c : Config D) : M (Config D × State D) := do
  match c with
  | .panicked _ => quit .q11Internal
  | .panicking _ _ => quit .q6Panic
  | .exec stmt env k =>
      match stmt with
      | .seqn ss => .ok (.next (seqCont' ss.toList env k), s)
      | .block decls ss => do
          let (env', s') ← allocDecls' env.pushScope s decls.toList
          .ok (.next (.seq ss.toList env' k), s')
      | .initialization p =>
          (match k with
           | .seq rest kenv k' =>
              if kenv = env then do
                let v ← defaultValue' p.typ
                let (loc, s') := s.alloc v (some p.typ)
                .ok (.next (.seq rest (env.declare p.id loc) k'), s')
              else quit .q11Internal
           | _ => quit .q11Internal)
      | .assign lhs rhs =>
          (match targetPlan lhs with
           | some (sh, e :: ops) =>
              .ok (.evalE e env
                (.tgtOpK sh [] ops [] [] .vals [rhs] [] (.seqn #[]) env k), s)
           | some (_, []) => quit .q11Internal
           | none => quit .q11Internal)
      | .ifThenElse c t e => .ok (.evalE c env (.ifK t e env k), s)
      | .while c b => .ok (.evalE c env (.whileK c b env k), s)
      | .returnStmt => .ok (.returning k, s)
      | .breakStmt => .ok (.breaking k, s)
      | .continueStmt => .ok (.continuing k, s)
      | .label _ => .ok (.next k, s)
      | .labeled name b => .ok (.exec b env (.labelK name k), s)
      | .breakTo name => .ok (.breakingTo name k, s)
      | .continueTo name => .ok (.continuingTo name k, s)
      | .breakable b => .ok (.exec b env (.breakableK k), s)
      | .deferCall callee args =>
          .ok (.evalE callee env (.deferCalleeK args.toList env k), s)
      | .panicStmt _ => quit .q6Panic
      | .callValue targets callee args =>
          (match targetsPlan targets.toList with
           | some plans =>
              .ok (.evalE callee env (.callValCalleeK plans args.toList env k), s)
           | none => quit .q11Internal)
      | .call targets fid args =>
          (match targetsPlan targets.toList with
           | some plans =>
              (match args.toList with
               | a :: rest =>
                  .ok (.evalE a env (.callArgsK fid plans [] rest env k), s)
               | [] => quit .q4Program)
           | none => quit .q11Internal)
      | .mapRange keyVar valVar mapExpr keyTy valTy body =>
          .ok (.evalE mapExpr env
            (.mapRangeK keyVar valVar keyTy valTy body env k), s)
      | .chanSend _ _ _ => quit .q7Concurrency
      | .closeChan _ => quit .q7Concurrency
      | .chanRecv _ _ _ => quit .q7Concurrency
      | .goStmt _ _ => quit .q7Concurrency
      | .selectStmt _ _ => quit .q7Concurrency
      | .unsupported _ => quit .q11Internal
      | .mapLookup t okT base index keyTy valueTy =>
          (match targetsPlan [t, okT] with
           | some ((sh, e :: ops) :: rest) =>
              .ok (.evalE e env
                (.tgtOpK sh [] ops [] rest (.mapLookup keyTy valueTy)
                  [base, index] [] (.seqn #[]) env k), s)
           | some _ => quit .q11Internal
           | none => quit .q11Internal)
      | .typeAssert _ _ _ _ => quit .q4Program
      | .assignMany left right =>
          if left.size = right.size then
            match targetsPlan left.toList with
            | some ((sh, e :: ops) :: rest) =>
                .ok (.evalE e env
                  (.tgtOpK sh [] ops [] rest .vals right.toList [] (.seqn #[]) env k), s)
            | some _ => quit .q11Internal
            | none => quit .q11Internal
          else quit .q11Internal
      | .syncStmt _ _ _ => quit .q7Concurrency
      | wide =>
          (match stmtPlan wide with
           | some (op, nt, e :: rest) =>
              .ok (.evalE e env (.stmtOpK op nt [] rest env k), s)
           | some (op, _, []) => do
              let s' ← applyStmtOp' s op []
              .ok (.next k, s')
           | none => quit .q11Internal)
  | .evalE e env k =>
      match e with
      | .var id =>
          (match LocalEnv.lookup env id with
           | some loc => do
              let v ← loadLoc' s loc
              .ok (.retV v k, s)
           | none => quit .q11Internal)
      | .intLit value kind =>
          .ok (.retV (.int (D.litI (kind.normalize value)) kind) k, s)
      | .boolLit value => .ok (.retV (.bool (D.litB value)) k, s)
      | .stringLit value => .ok (.retV (.string value) k, s)
      | .ref id =>
          (match LocalEnv.lookup env id with
           | some loc => .ok (.retV (.addr loc) k, s)
           | none => quit .q11Internal)
      | .locLit l => .ok (.retV (.addr l) k, s)
      | .and l r => .ok (.evalE l env (.andK r env k), s)
      | .or l r => .ok (.evalE l env (.orK r env k), s)
      | .recoverCall => quit .q6Panic
      | .unsupported _ => quit .q11Internal
      | e =>
          (match strictPlan e with
           | some (op, e₁ :: rest) =>
              .ok (.evalE e₁ env (.strictK op [] rest env k), s)
           | some (op, []) => do
              let (v, s') ← applyStrictOp' s op []
              .ok (.retV v k, s')
           | none => quit .q11Internal)
  | .retV v k =>
      match k with
      | .strictK op done (e :: rest) env k' =>
          .ok (.evalE e env (.strictK op (v :: done) rest env k'), s)
      | .strictK op done [] _ k' => do
          let (out, s') ← applyStrictOp' s op (v :: done).reverse
          .ok (.retV out k', s')
      | .andK r env k' => do
          let b ← v.asBoolAt .q1Branch
          if b then
            .ok (.evalE r env (.boolK k'), s)
          else
            .ok (.retV (.bool (D.litB false)) k', s)
      | .orK r env k' => do
          let b ← v.asBoolAt .q1Branch
          if b then
            .ok (.retV (.bool (D.litB true)) k', s)
          else
            .ok (.evalE r env (.boolK k'), s)
      | .boolK k' => do
          let b ← v.asBoolAt .q1Branch
          .ok (.retV (.bool (D.litB b)) k', s)
      | .ifK t e env k' => do
          let b ← v.asBoolAt .q1Branch
          if b then
            .ok (.exec t env k', s)
          else
            .ok (.exec e env k', s)
      | .whileK c b env k' => do
          let cond ← v.asBoolAt .q1Branch
          if cond then
            .ok (.exec b env (.loop c b env k'), s)
          else
            .ok (.next k', s)
      | .callArgsK fid plans vals pending env k' =>
          (match pending with
           | a :: rest =>
              .ok (.evalE a env
                (.callArgsK fid plans (vals ++ [v]) rest env k'), s)
           | [] => quit .q4Program)
      | .stmtOpK op nt done pending env k' =>
          (match pending with
           | e :: rest =>
              if done.length < nt then do
                let _ ← v.asLoc
                .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s)
              else
                .ok (.evalE e env (.stmtOpK op nt (v :: done) rest env k'), s)
           | [] =>
              -- BUG-005 (L): mapDelete/clearMap REWRITE the
              -- continuation (the delete-prune of in-flight iteration
              -- frames) — a semantic-key computation the domain leaves
              -- undecided, so the mirror QUITS on those two ops rather
              -- than transcribing the prune (a quit asserts nothing;
              -- the drift theorem forces fidelity of what remains).
              (match op with
               | .mapDelete _ => quit .q4Program
               | .clearMap => quit .q4Program
               | _ => do
                  let s' ← applyStmtOp' s op (v :: done).reverse
                  .ok (.next k', s')))
      | .callValCalleeK plans args env k' =>
          (match v, args with
           | .funcVal _ _, [] => quit .q4Program
           | .nil, [] => quit .q6Panic
           | cv, a :: rest => do
              let ok ← cv.deferrable
              if ok then
                .ok (.evalE a env (.callValArgsK cv plans [] rest env k'), s)
              else quit .q11Internal
           | _, [] => quit .q11Internal)
      | .callValArgsK cv plans vals pending env k' =>
          (match pending with
           | a :: rest =>
              .ok (.evalE a env
                (.callValArgsK cv plans (vals ++ [v]) rest env k'), s)
           | [] =>
              (match cv with
               | .funcVal _ _ => quit .q4Program
               | .nil => quit .q6Panic
               | .atom _ => quit .q10Atom
               | _ => quit .q11Internal))
      | .deferCalleeK args env k' => do
          let ok ← v.deferrable
          if ok then
            match args with
            | a :: rest =>
                .ok (.evalE a env (.deferArgsK v [] rest env k'), s)
            | [] =>
                (match pushDefer' (v, []) k' with
                 | some k'' => .ok (.next k'', s)
                 | none => quit .q11Internal)
          else quit .q11Internal
      | .deferArgsK cv vals pending env k' =>
          (match pending with
           | a :: rest =>
              .ok (.evalE a env
                (.deferArgsK cv (vals ++ [v]) rest env k'), s)
           | [] =>
              (match pushDefer' (cv, vals ++ [v]) k' with
               | some k'' => .ok (.next k'', s)
               | none => quit .q11Internal))
      | .mapRangeK keyVar valVar keyTy valTy body env k' => do
          let bs ← mapRangeStartSets' s v
          .ok (.next (.mapIterK keyVar valVar keyTy valTy body
            bs.1 #[] bs.2 env k'), s)
      | .panicArgK _ => quit .q6Panic
      | .chanStK _ _ _ _ _ => quit .q7Concurrency
      | .selectOpsK _ _ _ _ _ _ => quit .q7Concurrency
      | .tgtOpK sh ops pending refs targets rop rhs vals body env k' =>
          (match pending with
           | e :: rest =>
              .ok (.evalE e env
                (.tgtOpK sh (v :: ops) rest refs targets rop rhs vals body env k'), s)
           | [] =>
              (match completeTargetRef' sh (v :: ops).reverse with
               | none => quit .q11Internal
               | some r =>
                  (match targets with
                   | (sh', e :: ops') :: rest =>
                      .ok (.evalE e env
                        (.tgtOpK sh' [] ops' (refs ++ [r]) rest rop rhs vals body env k'), s)
                   | (_, []) :: _ => quit .q11Internal
                   | [] =>
                      (match rhs with
                       | e :: rest =>
                          .ok (.evalE e env
                            (.rhsK rop (refs ++ [r]) [] rest body env k'), s)
                       | [] =>
                          .ok (.next (.storeK (refs ++ [r]) vals body env k'), s)))))
      | .rhsK rop refs done pending body env k' =>
          (match pending with
           | e :: rest =>
              .ok (.evalE e env (.rhsK rop refs (v :: done) rest body env k'), s)
           | [] => do
              let vals ← applyRhsOp' s rop (v :: done).reverse
              .ok (.next (.storeK refs vals body env k'), s))
      | .goCalleeK _ _ _ => quit .q7Concurrency
      | .goArgsK _ _ _ _ _ => quit .q7Concurrency
      | .syncStK _ _ _ _ _ => quit .q7Concurrency
      | .stop => quit .q11Internal
      | _ => quit .q11Internal
  | .next k =>
      match k with
      | .stop => quit .q11Internal
      | .seq (t :: rest) env k' => .ok (.exec t env (.seq rest env k'), s)
      | .seq [] _ k' => .ok (.next k', s)
      | .loop c b env k' => .ok (.exec (.while c b) env k', s)
      | .frame [] _ [] [] k' _ => .ok (.next k', s)
      | .frame [] _ (_ :: _) [] _ _ => quit .q11Internal
      | .frame ((sh, e :: ops) :: rest) tenv results [] k' _ => do
          let vs ← loadMany' s results
          .ok (.evalE e tenv
            (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s)
      | .frame ((_, []) :: _) _ _ [] _ _ => quit .q11Internal
      | .frame _ _ _ ((cv, _) :: _) _ _ =>
          (match cv with
           | .funcVal _ _ => quit .q4Program
           | .nil => quit .q6Panic
           | .atom _ => quit .q10Atom
           | _ => quit .q11Internal)
      | .panicResumeK _ _ => quit .q6Panic
      | .breakableK k' => .ok (.next k', s)
      | .labelK _ k' => .ok (.next k', s)
      | .mapIterK _ _ _ _ _ base _ _ _ k' =>
          -- BUG-005 (L): doneness needs the LIVE cell. Compute when
          -- the cell answers "no entries" (nil/empty map — exactly the
          -- windows the retired snapshot model kept computing); quit
          -- Q3 at any nonempty cell (a pick or the stop slot consumes
          -- a choice there — a quit asserts nothing).
          (match base with
           | none => .ok (.next k', s)
           | some l => do
              (match ← loadLoc' s l with
               | .mapData es =>
                  if es.isEmpty then .ok (.next k', s)
                  else quit .q3Choice
               | .atom _ => quit .q10Atom
               | _ => quit .q11Internal))
      | .storeK refs vals body env k' =>
          (match refs, vals with
           | r :: rs, val :: vrest => do
              let s' ← storeTarget' s r val
              .ok (.next (.storeK rs vrest body env k'), s')
           | [], [] => .ok (.exec body env k', s)
           | _, _ => quit .q11Internal)
      | _ => quit .q11Internal
  | .breaking k =>
      match k with
      | .seq _ _ k' => .ok (.breaking k', s)
      | .loop _ _ _ k' => .ok (.next k', s)
      | .breakableK k' => .ok (.next k', s)
      | .labelK _ k' => .ok (.breaking k', s)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => .ok (.next k', s)
      | .frame _ _ _ _ _ _ => quit .q11Internal
      | .stop => quit .q11Internal
      | _ => quit .q11Internal
  | .continuing k =>
      match k with
      | .seq _ _ k' => .ok (.continuing k', s)
      | .breakableK k' => .ok (.continuing k', s)
      | .labelK _ k' => .ok (.continuing k', s)
      | .loop c b env k' => .ok (.exec (.while c b) env k', s)
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
          .ok (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'), s)
      | .frame _ _ _ _ _ _ => quit .q11Internal
      | .stop => quit .q11Internal
      | _ => quit .q11Internal
  | .returning k =>
      match k with
      | .seq _ _ k' => .ok (.returning k', s)
      | .breakableK k' => .ok (.returning k', s)
      | .labelK _ k' => .ok (.returning k', s)
      | .loop _ _ _ k' => .ok (.returning k', s)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => .ok (.returning k', s)
      | .frame [] _ [] [] k' _ => .ok (.next k', s)
      | .frame [] _ (_ :: _) [] _ _ => quit .q11Internal
      | .frame ((sh, e :: ops) :: rest) tenv results [] k' _ => do
          let vs ← loadMany' s results
          .ok (.evalE e tenv
            (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) tenv k'), s)
      | .frame ((_, []) :: _) _ _ [] _ _ => quit .q11Internal
      | .frame _ _ _ ((cv, _) :: _) _ _ =>
          (match cv with
           | .funcVal _ _ => quit .q4Program
           | .nil => quit .q6Panic
           | .atom _ => quit .q10Atom
           | _ => quit .q11Internal)
      | .stop => quit .q11Internal
      | _ => quit .q11Internal
  | .breakingTo L k =>
      match k with
      | .seq _ _ k' => .ok (.breakingTo L k', s)
      | .loop _ _ _ k' => .ok (.breakingTo L k', s)
      | .breakableK k' => .ok (.breakingTo L k', s)
      | .mapIterK _ _ _ _ _ _ _ _ _ k' => .ok (.breakingTo L k', s)
      | .labelK name k' =>
          if name = L then .ok (.next k', s)
          else .ok (.breakingTo L k', s)
      | .frame _ _ _ _ _ _ => quit .q11Internal
      | .stop => quit .q11Internal
      | _ => quit .q11Internal
  | .continuingTo L k =>
      match k with
      | .seq _ _ k' => .ok (.continuingTo L k', s)
      | .breakableK k' => .ok (.continuingTo L k', s)
      | .labelK name k' =>
          if name = L then quit .q11Internal
          else .ok (.continuingTo L k', s)
      | .loop c b env k' =>
          if contHeadLabel' k' = some L then
            .ok (.exec (.while c b) env k', s)
          else .ok (.continuingTo L k', s)
      | .mapIterK keyVar valVar keyTy valTy body base produced start env k' =>
          if contHeadLabel' k' = some L then
            .ok (.next (.mapIterK keyVar valVar keyTy valTy body base produced start env k'), s)
          else .ok (.continuingTo L k', s)
      | .frame _ _ _ _ _ _ => quit .q11Internal
      | .stop => quit .q11Internal
      | _ => quit .q11Internal
  | .blockedSend _ _ _ => quit .q7Concurrency
  | .blockedRecv _ _ _ _ _ => quit .q7Concurrency
  | .blockedSelect _ _ _ => quit .q7Concurrency
  | .spawned _ => quit .q7Concurrency
  | .blockedSync _ _ _ _ => quit .q7Concurrency

/-! ## The symbolic instance and the window driver (design §6.1) -/

/-- The symbolic state/config shapes (design §5.1). -/
abbrev SymValue := Value symDom
abbrev SymHeapCell := HeapCell symDom
abbrev SymHeap := Heap symDom
abbrev SymState := State symDom
abbrev SymCont := Cont symDom
abbrev SymConfig := Config symDom

/-- One symbolic step — THE EVALUATOR's step (the mirror at the
symbolic domain). -/
def stepFnS (S : SymState) (C : SymConfig) : M (SymConfig × SymState) :=
  stepFn' S C

/-- Iterate to quit or budget (design §6.1): `n` = steps COMPLETED; a
quit ends the window (shorter `n`), never errors — which is why the
driver's type has no error channel and the refinement theorem no side
conditions. Total, structural on the budget; bare products (no
`Except`/`Bind` tower) per the design-for-reduction rules. -/
def symEvalWindow : Nat → SymState → SymConfig → Nat × SymState × SymConfig
  | 0, S, C => (0, S, C)
  | budget + 1, S, C =>
      match stepFnS S C with
      | .error _ => (0, S, C)
      | .ok (C', S') =>
          let (n, S'', C'') := symEvalWindow budget S' C'
          (n + 1, S'', C'')

/-- The quit site the window ends on, if any within the budget —
diagnostic companion to `symEvalWindow` (same shape, reports the
catalog entry). -/
def symEvalQuit : Nat → SymState → SymConfig → Option QuitSite
  | 0, _, _ => none
  | budget + 1, S, C =>
      match stepFnS S C with
      | .error q => some q
      | .ok (C', S') => symEvalQuit budget S' C'

/-! ## Reflection (GoCore → mirror, payloads as literals)

Total injections used to build mirror fixtures from shipped concrete
configurations (a window's closed continuation reflects verbatim;
symbolic cells are then written by hand). At the concrete domain the
reflection is the embedding's inverse. -/

def reflectV (D : ScalarDom) : GoValue → Value D
  | .unit => .unit
  | .bool b => .bool (D.litB b)
  | .int v kind => .int (D.litI v) kind
  | .float bits kind => .float bits kind
  | .string s => .string s
  | .addr loc => .addr loc
  | .nil => .nil
  | .interface dynTy inner => .interface dynTy (reflectV D inner)
  | .struct tid fields => .struct tid (fields.attach.map
      (fun ⟨(name, v), _⟩ => (name, reflectV D v)))
  | .array values => .array (values.attach.map (fun ⟨v, _⟩ => reflectV D v))
  | .slice sv => .slice sv
  | .map mv => .map mv
  | .mapData entries => .mapData (entries.attach.map
      (fun ⟨(k, v), _⟩ => (reflectV D k, reflectV D v)))
  | .chan cv => .chan cv
  | .chanData buf capacity closed =>
      .chanData (buf.attach.map (fun ⟨v, _⟩ => reflectV D v)) capacity closed
  | .funcVal fid captured =>
      .funcVal fid (captured.attach.map (fun ⟨v, _⟩ => reflectV D v))
  | .syncData p => .syncData p
termination_by v => sizeOf v
decreasing_by
  all_goals
    first
      | (rename_i h
         first
           | (have hlt := Array.sizeOf_lt_of_mem h; simp_all; omega)
           | (have hlt := List.sizeOf_lt_of_mem h; simp_all; omega))
      | (simp_all; omega)
      | omega

def reflectEntry (D : ScalarDom) (e : Machine.PanicEntry) : PanicEntry D :=
  ⟨reflectV D e.value, e.recovered⟩

def reflectRef (D : ScalarDom) : Machine.TargetRef → TargetRef D
  | .chain anchor idxs steps =>
      .chain (reflectV D anchor) (idxs.map (reflectV D)) steps
  | .mapElem b k kt vt => .mapElem (reflectV D b) (reflectV D k) kt vt

def reflectClause (D : ScalarDom) : Machine.EvClause → EvClause D
  | .sendEv chv v elem body => .sendEv (reflectV D chv) (reflectV D v) elem body
  | .recvEv chv targets elem body => .recvEv (reflectV D chv) targets elem body

def reflectCell (D : ScalarDom) (cell : GoCore.HeapCell) : HeapCell D :=
  .mk cell.declaredTy (reflectV D cell.value)

def reflectHeap (D : ScalarDom) (h : GoCore.Heap) : Heap D :=
  h.map (fun (loc, cell) => (loc, reflectCell D cell))

def reflectK (D : ScalarDom) : Machine.Cont → Cont D
  | .stop => .stop
  | .seq rest env k => .seq rest env (reflectK D k)
  | .loop c b env k => .loop c b env (reflectK D k)
  | .frame targets tenv results defers k w =>
      .frame targets tenv results
        (defers.map (fun (cv, args) => (reflectV D cv, args.map (reflectV D))))
        (reflectK D k) w
  | .deferCalleeK args env k => .deferCalleeK args env (reflectK D k)
  | .deferArgsK callee vals pending env k =>
      .deferArgsK (reflectV D callee) (vals.map (reflectV D)) pending env
        (reflectK D k)
  | .breakableK k => .breakableK (reflectK D k)
  | .labelK label k => .labelK label (reflectK D k)
  | .callValCalleeK targets args env k =>
      .callValCalleeK targets args env (reflectK D k)
  | .callValArgsK callee targets vals pending env k =>
      .callValArgsK (reflectV D callee) targets (vals.map (reflectV D))
        pending env (reflectK D k)
  | .strictK op done pending env k =>
      .strictK op (done.map (reflectV D)) pending env (reflectK D k)
  | .andK right env k => .andK right env (reflectK D k)
  | .orK right env k => .orK right env (reflectK D k)
  | .boolK k => .boolK (reflectK D k)
  | .ifK t e env k => .ifK t e env (reflectK D k)
  | .whileK c b env k => .whileK c b env (reflectK D k)
  | .callArgsK fid targets vals pending env k =>
      .callArgsK fid targets (vals.map (reflectV D)) pending env (reflectK D k)
  | .stmtOpK op nt done pending env k =>
      .stmtOpK op nt (done.map (reflectV D)) pending env (reflectK D k)
  | .mapRangeK kv vv kt vt body env k =>
      .mapRangeK kv vv kt vt body env (reflectK D k)
  | .mapIterK kv vv kt vt body base produced start env k =>
      .mapIterK kv vv kt vt body base
        (produced.map (reflectV D)) (start.map (reflectV D))
        env (reflectK D k)
  | .panicArgK k => .panicArgK (reflectK D k)
  | .panicResumeK chain k =>
      .panicResumeK (chain.map (reflectEntry D)) (reflectK D k)
  | .chanStK op done pending env k =>
      .chanStK op (done.map (reflectV D)) pending env (reflectK D k)
  | .selectOpsK clauses default? done pending env k =>
      .selectOpsK clauses default? (done.map (reflectV D)) pending env
        (reflectK D k)
  | .tgtOpK sh ops pending refs targets rop rhs vals body env k =>
      .tgtOpK sh (ops.map (reflectV D)) pending (refs.map (reflectRef D))
        targets rop rhs (vals.map (reflectV D)) body env (reflectK D k)
  | .rhsK rop refs done pending body env k =>
      .rhsK rop (refs.map (reflectRef D)) (done.map (reflectV D)) pending
        body env (reflectK D k)
  | .storeK refs vals body env k =>
      .storeK (refs.map (reflectRef D)) (vals.map (reflectV D)) body env
        (reflectK D k)
  | .goCalleeK args env k => .goCalleeK args env (reflectK D k)
  | .goArgsK callee vals pending env k =>
      .goArgsK (reflectV D callee) (vals.map (reflectV D)) pending env
        (reflectK D k)
  | .syncStK op done pending env k =>
      .syncStK op (done.map (reflectV D)) pending env (reflectK D k)

def reflectC (D : ScalarDom) : Machine.Config → Config D
  | .exec stmt env k => .exec stmt env (reflectK D k)
  | .evalE e env k => .evalE e env (reflectK D k)
  | .retV v k => .retV (reflectV D v) (reflectK D k)
  | .next k => .next (reflectK D k)
  | .breaking k => .breaking (reflectK D k)
  | .continuing k => .continuing (reflectK D k)
  | .returning k => .returning (reflectK D k)
  | .breakingTo label k => .breakingTo label (reflectK D k)
  | .continuingTo label k => .continuingTo label (reflectK D k)
  | .panicking chain k =>
      .panicking (chain.map (reflectEntry D)) (reflectK D k)
  | .panicked msg => .panicked msg
  | .blockedSend ch v k => .blockedSend ch (reflectV D v) (reflectK D k)
  | .blockedRecv ch targets elem env k =>
      .blockedRecv ch targets elem env (reflectK D k)
  | .blockedSelect clauses env k =>
      .blockedSelect (clauses.map (reflectClause D)) env (reflectK D k)
  | .spawned k => .spawned (reflectK D k)
  | .blockedSync op loc env k => .blockedSync op loc env (reflectK D k)

end GoLean.Sym
