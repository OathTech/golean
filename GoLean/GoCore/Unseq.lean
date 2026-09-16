import GoLean.GoCore.Syntax

/-!
# The `unseq` graph's scheduler functions (Stage B, 2026-09-16)

The PURE half of the evaluation-order construct (`Stmt.unseq`, Syntax.lean;
design `docs/2026-09-16_evaluation-order-model-v2.md` §1/§3.3; lane
`core/unseq-scheduler-b-0916`): the static graph checks the machine refuses
BY NAME at ENTER, and the ONE `ready` computation shared by execution
(`stepFn`), the relation's premises (`Step.unseqPick`) and the consumption
projection (`seqConsumption`) — review R5's «one `ready` calculation».
Everything here is total structural recursion over lists; the dynamic
record (statuses, target table, environment) lives in the continuation
(`Cont.unseqK`, Machine.lean), never in the value/heap universe (review R4).

The scheduler's three cases (review R2), as the machine realizes them
(`stepUnseqNext`, StepFn.lean): (i) no ACTIVE occurrence → phase 2 /
completion; (ii) `ready ≠ []` → pick any ready occurrence
(`ChoiceSite.unseqNext`, bound `|ready|`, slot `j` = the `j`-th ready
occurrence in canonical rank order); (iii) active work with no ready
occurrence → a NAMED malformed-graph refusal, never a stuck run. A value
dependency on a binder confined to a SKIPPED region (no valid join) is
another named dynamic refusal (`skippedDep?`), as is — at completion — a
phase-2 store or a completion-statement mention of a binder that was never
PRODUCED (`unproducedConsumer?`; audit F1, 2026-09-16: a skipped
producer's zero-initialised cell is no value of the sweep).
-/

namespace GoLean.GoCore

open GoLean

mutual
/-- The local NAMES an expression mentions (`.var`/`.ref`): the slot
references a body consumes (∩ the graph's binder cells = its VALUE
dependencies) and the admitted stable reads of source locals. Total; no
constructor catch-all (adding syntax requires choosing its traversal —
the `AdmissionIndices` discipline). -/
def Expr.names : Expr → List String
  | .var id | .ref id => [id]
  | .nil _ | .intLit _ _ | .floatLit _ _ _ | .stringLit _ | .boolLit _
  | .global _ | .defaultValue _ | .recoverCall | .unsupported _ => []
  | .convert _ e | .bytesFromString e | .stringFromByteSlice e | .stringFromRune e
  | .bitNeg e | .neg e | .not e | .deref e _ | .addrOfDeref e
  | .fieldGet e _ _ | .fieldAddr e _ _ | .toInterface _ _ e | .typeAssert e _ _
  | .length e _ | .capacity e _ | .runesFromString e | .stringFromRuneSlice e
  | .floatBits _ e => Expr.names e
  | .add l r | .sub l r | .mul l r | .div l r | .mod l r
  | .shiftLeft l r | .shiftRight l r | .bitAnd l r | .bitOr l r
  | .bitXor l r | .bitClear l r | .eqCmp _ l r | .neqCmp _ l r
  | .atMostCmp l r | .atLeastCmp l r | .lessCmp l r | .greaterCmp l r
  | .and l r | .or l r | .indexGet l r | .indexAddr l r | .mapGet l r _ _
  | .runeAt l r | .runeSizeAt l r => Expr.names l ++ Expr.names r
  | .funcVal _ es | .minOf es | .maxOf es => exprListNames es.toList
  | .structLit _ es => exprListNames es.toList
  | .arrayLit _ _ es => keyedExprNames es.toList
  | .slice b lo hi m => Expr.names b ++ Expr.names lo ++ Expr.names hi ++ optExprNames m
def exprListNames : List Expr → List String
  | [] => []
  | e :: es => Expr.names e ++ exprListNames es
def keyedExprNames : List (Int × Expr) → List String
  | [] => []
  | (_, e) :: es => Expr.names e ++ keyedExprNames es
def optExprNames : Option Expr → List String
  | none => []
  | some e => Expr.names e
end

/-- The names an assignee's OPERANDS mention (`targetPlan`'s operand
expressions: `x` ↦ `&x`'s name, `a[i]` ↦ the anchor and index names). -/
def Assignee.names : Assignee → List String
  | .var id => [id]
  | .addr e => Expr.names e
  | .mapElem b k _ _ => Expr.names b ++ Expr.names k
  | .unsupported _ => []

def assigneeListNames : List Assignee → List String
  | [] => []
  | a :: as => a.names ++ assigneeListNames as

def selectHeadNames : SelectClauseHead → List String
  | .send c v _ => c.names ++ v.names
  | .recv as c _ => assigneeListNames as.toList ++ c.names

/-- An occurrence's scheduler status: «completed» ≠ «produced» (review R4)
— a DONE occurrence produced every binder it binds; a SKIPPED one
(inside a disabled region) discharged its order edges and produced
nothing; ACTIVE = pending. -/
inductive UnseqStatus where
  | active
  | done
  | skipped
  deriving Repr, DecidableEq, Inhabited

/-- Where the sweep frame is: at a PICK (case (i)/(ii)/(iii)), RUNNING
occurrence `i` (the picked occurrence starts this step — its footprint is
known from the configuration, `Race.stepAccesses`), or WAITING for
occurrence `i`'s value/statement completion. -/
inductive UnseqPhase where
  | pick
  | run (i : Nat)
  | wait (i : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace UnseqBody

/-- The VALUE binders a body produces (its results). -/
def valueBinds : UnseqBody → List String
  | .eval b _ | .load b _ => [b]
  | .invoke bs _ _ => bs
  | .target _ _ | .guard _ _ _ => []

/-- The TARGET binder a body produces, if any. -/
def targetBind? : UnseqBody → Option String
  | .target b _ => some b
  | _ => none

/-- The VALUE names a body consumes: slot references and admitted
source-local reads (a guard consumes its test binder). A `load` consumes
only a TARGET (`targetMentions`). -/
def mentions : UnseqBody → List String
  | .eval _ head => head.names
  | .load _ _ => []
  | .invoke _ callee args => callee.names ++ exprListNames args
  | .target _ lhs => lhs.names
  | .guard test _ _ => [test]

/-- The TARGET binders a body reads through. -/
def targetMentions : UnseqBody → List String
  | .load _ tgt => [tgt]
  | _ => []

end UnseqBody

/-- The slot names a nested graph's bodies and stores mention (a nested
`unseq` in a completion statement is the decoder's refusal, Stage C; the
walk below stays total over it). -/
def unseqGraphNames (g : UnseqGraph) : List String :=
  g.occs.flatMap (fun o => o.body.mentions ++ o.body.targetMentions)
    ++ g.stores.flatMap (fun (t, v) => [t, v])

mutual
/-- The local NAMES a statement's expressions and assignees mention — the
reads and stores of a sweep's completion statement `thenB` (declarations
are not mentions). Total; no constructor catch-all (adding syntax requires
choosing its traversal — the `AdmissionIndices` discipline; the case list
mirrors `Admission.stmtIndices`). Consumed by `UnseqGraph.unproducedConsumer?`
(audit F1, 2026-09-16). -/
def Stmt.names : Stmt → List String
  | .seqn ss => stmtListNames ss.toList
  | .block _ ss => stmtListNames ss.toList
  | .breakable s | .labeled _ s => Stmt.names s
  | .initialization _ => []
  | .assign a e => a.names ++ e.names
  | .assignMany as es | .call as _ es | .syncStmt _ es as | .atomicStmt _ _ es as =>
      assigneeListNames as.toList ++ exprListNames es.toList
  | .allocNew a e _ => a.names ++ e.names
  | .makeSlice a _ e cap => a.names ++ e.names ++ optExprNames cap
  | .makeMap a _ _ cap => a.names ++ optExprNames cap
  | .mapAssign b i e _ _ => b.names ++ i.names ++ e.names
  | .mapDelete b i _ => b.names ++ i.names
  | .clearMap b | .closeChan b | .panicStmt b | .unseqProbe b => b.names
  | .unseq g t => unseqGraphNames g ++ Stmt.names t
  | .clearSlice b _ | .sortSlice b _ => b.names
  | .mapLookup a ok b i _ _ => a.names ++ ok.names ++ b.names ++ i.names
  | .typeAssert a ok e _ => a.names ++ ok.names ++ e.names
  | .appendSlice a _ s es => a.names ++ s.names ++ es.names
  | .copySlice a d s => a.names ++ d.names ++ s.names
  | .callValue as e es => assigneeListNames as.toList ++ e.names ++ exprListNames es.toList
  | .deferCall e es | .goStmt e es => e.names ++ exprListNames es.toList
  | .ifThenElse e t f => e.names ++ Stmt.names t ++ Stmt.names f
  | .while e s => e.names ++ Stmt.names s
  | .mapRange _ _ e _ _ s => e.names ++ Stmt.names s
  | .returnStmt | .breakStmt | .continueStmt | .breakTo _ | .continueTo _
  | .inertLabel _ | .unsupported _ => []
  | .makeChan a _ cap => a.names ++ optExprNames cap
  | .chanSend c v _ => c.names ++ v.names
  | .chanRecv as c _ => assigneeListNames as.toList ++ c.names
  | .selectStmt cs d => selectNames cs.toList ++ optStmtNames d
  | .print _ es => exprListNames es.toList
def stmtListNames : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.names s ++ stmtListNames ss
def selectNames : List (SelectClauseHead × Stmt) → List String
  | [] => []
  | (c, s) :: cs => selectHeadNames c ++ Stmt.names s ++ selectNames cs
def optStmtNames : Option Stmt → List String
  | none => []
  | some s => Stmt.names s
end

/-- Pairwise distinctness of a name list. -/
def namesDistinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && namesDistinct xs

namespace UnseqGraph

def cellNames (g : UnseqGraph) : List String := g.cells.map (·.id)

def occNames (g : UnseqGraph) : List String := g.occs.map (·.name)

/-- The index (canonical rank) of the occurrence named `name`. -/
def index? (g : UnseqGraph) (name : String) : Option Nat :=
  g.occs.findIdx? (·.name == name)

/-- The occurrence producing `slot` (a VALUE cell or a TARGET binder). -/
def producer? (g : UnseqGraph) (slot : String) : Option Nat :=
  g.occs.findIdx? fun o => o.body.valueBinds.contains slot || o.body.targetBind? == some slot

def targetBinders (g : UnseqGraph) : List String :=
  g.occs.filterMap (·.body.targetBind?)

def isCell (g : UnseqGraph) (n : String) : Bool := g.cellNames.contains n

/-- The declared type of a binder cell. -/
def cellType? (g : UnseqGraph) (n : String) : Option Ty :=
  (g.cells.find? (·.id == n)).map (·.typ)

def isTargetBinder (g : UnseqGraph) (n : String) : Bool := g.targetBinders.contains n

def isGuard (g : UnseqGraph) (n : String) : Bool :=
  g.occs.any fun o => o.name == n && match o.body with | .guard .. => true | _ => false

/-- The VALUE dependencies of an occurrence: the binder cells its body
mentions (IMPLIED by slot mentions — a name that is not a cell is an
admitted source-local read, not an edge) plus the target binders it
reads through. -/
def deps (g : UnseqGraph) (o : UnseqOcc) : List String :=
  o.body.mentions.filter g.isCell ++ o.body.targetMentions

def statusOf (g : UnseqGraph) (st : List UnseqStatus) (name : String) : Option UnseqStatus :=
  (g.index? name).bind (st[·]?)

/-- A binder is PRODUCED iff its producing occurrence is DONE — the
«assigned bitmap» of the design's runtime record, DERIVED from the
status array ([AGENT] representation choice, Stage B: one array, not
two; the alternative — an explicit bitmap beside the statuses — is
recorded in the handoff). -/
def produced (g : UnseqGraph) (st : List UnseqStatus) (slot : String) : Bool :=
  match g.producer? slot with
  | some p => st[p]? == some .done
  | none => false

/-- An ORDER prerequisite is discharged by a DONE or a SKIPPED occurrence
(review R2: a skip never invents a value, but it does release order). -/
def discharged (g : UnseqGraph) (st : List UnseqStatus) (name : String) : Bool :=
  match g.statusOf st name with
  | some .done | some .skipped => true
  | _ => false

/-- An occurrence's region is enabled iff its guard has DECIDED (DONE); a
member of a SKIPPED region is itself skipped, so it never reads as
active here. -/
def regionOk (g : UnseqGraph) (st : List UnseqStatus) (o : UnseqOcc) : Bool :=
  match o.region with
  | none => true
  | some gn => g.statusOf st gn == some .done

/-- READY: active, region enabled, every order prerequisite discharged,
every value dependency produced. -/
def readyAt (g : UnseqGraph) (st : List UnseqStatus) (i : Nat) : Bool :=
  match g.occs[i]? with
  | some o =>
      st[i]? == some .active && g.regionOk st o
        && o.after.all (g.discharged st) && (g.deps o).all (g.produced st)
  | none => false

/-- **THE ready set**, in canonical rank order — the one computation
`stepFn`, `Step.unseqPick` and `seqConsumption` share (review R5). -/
def ready (g : UnseqGraph) (st : List UnseqStatus) : List Nat :=
  (List.range g.occs.length).filter (g.readyAt st)

/-- No ACTIVE occurrence remains: scheduler case (i). -/
def allSettled (g : UnseqGraph) (st : List UnseqStatus) : Bool :=
  (List.range g.occs.length).all fun i => st[i]? != some .active

def initStatus (g : UnseqGraph) : List UnseqStatus :=
  List.replicate g.occs.length .active

/-- The invalid-join check (dynamic; review R2): an ACTIVE occurrence
whose VALUE dependency's producer was SKIPPED can never run — refused
BY NAME (the only valid join is the region's completion binder, which a
skip sets and marks DONE). -/
def skippedDep? (g : UnseqGraph) (st : List UnseqStatus) : Option String :=
  (List.range g.occs.length).findSome? fun i =>
    match g.occs[i]? with
    | some o =>
        if st[i]? == some .active then
          (g.deps o).findSome? fun d =>
            match g.producer? d with
            | some p =>
                if st[p]? == some .skipped then
                  some s!"unseq: occurrence '{o.name}' value-depends on '{d}', confined to a skipped region (no valid join) — malformed graph"
                else none
            | none => none
        else none
    | none => none

/-- The completion's CONSUMERS' production check (audit F1, 2026-09-16;
design §1 G «a value use of a region-confined binder outside its region is
REJECTED — `c` is the only join»): at completion, every VALUE binder a
phase-2 store reads and every binder cell the completion statement `thenB`
mentions must have been PRODUCED (its occurrence DONE). A cell whose
producer was SKIPPED holds only its zero-initialised allocation — no value
of this sweep; consuming it would be the absorbing default the charter
forbids. Refused BY NAME (consumer, binder, producer and its status): the
mirror, for the completion's consumers, of `skippedDep?` for the occurrence
bodies. The STATIC form of the rule (any mention of a region-confined binder
outside its region, skipped or not, other than the completion binder) is the
decoder's check (Stage C); this is the machine's own refusal at the point of
failure, which hand-built graphs cannot bypass. -/
def unproducedConsumer? (g : UnseqGraph) (st : List UnseqStatus) (thenB : Stmt) : Option String :=
  let blame (consumer v : String) : Option String :=
    if g.produced st v then none
    else
      let why := match (g.producer? v).bind (g.occs[·]?) with
        | some o =>
            let status := match g.statusOf st o.name with
              | some .skipped => "was SKIPPED (confined to a disabled region)"
              | some .active => "is still ACTIVE"
              | some .done => "is DONE without producing it"
              | none => "has no status"
            s!"its producer '{o.name}' {status}"
        | none => "it has no producer"
      some s!"unseq: {consumer} reads binder '{v}', which was not produced — {why}; the completion binder is the only join — malformed graph"
  match g.stores.findSome? (fun (t, v) => blame s!"the phase-2 store into '{t}'" v) with
  | some msg => some msg
  | none => (thenB.names.filter g.isCell).findSome? (blame "the completion statement")

/-- One propagation of skipping: an active member of a skipped guard's
region becomes skipped. -/
def skipOnce (g : UnseqGraph) (st : List UnseqStatus) : List UnseqStatus :=
  (List.range g.occs.length).map fun i =>
    match g.occs[i]?, st[i]? with
    | some o, some .active =>
        match o.region with
        | some gn => if g.statusOf st gn == some .skipped then .skipped else .active
        | none => .active
    | _, some s => s
    | _, none => .active

/-- SKIP the region of the guard at index `gi`: every occurrence whose
region chain reaches the guard becomes SKIPPED (a fixpoint bounded by the
number of occurrences — regions nest by chaining). The guard itself is
marked skipped only transiently, to seed the propagation; the caller
marks it DONE (it decided) and marks the completion occurrence DONE. -/
def skipRegion (g : UnseqGraph) (st : List UnseqStatus) (gi : Nat) : List UnseqStatus :=
  let seeded := st.set gi .skipped
  (List.range g.occs.length).foldl (fun acc _ => g.skipOnce acc) seeded

/-- The static well-formedness of a graph, refused BY NAME at ENTER
(`none` = well-formed). These are the shape checks a scheduler needs to
be total on; cycles and invalid joins are the DYNAMIC refusals (cases
(iii) and `skippedDep?`) — the decoder's full check set (v2.1 §3.1) is
Stage C's. -/
def wellFormed? (g : UnseqGraph) : Option String :=
  if !namesDistinct g.cellNames then some "duplicate binder cell"
  else if !namesDistinct g.occNames then some "duplicate occurrence name"
  else if !namesDistinct (g.occs.flatMap (·.body.valueBinds)) then some "duplicate result (a value binder produced twice)"
  else if !namesDistinct g.targetBinders then some "duplicate result (a target binder produced twice)"
  else
    -- Audit F3 (2026-09-16): every binder — cell or target — carries the
    -- frontend's `$` reservation. The cells are declared into the SOURCE
    -- scope at ENTER (the `.initialization` idiom), so a bare name would
    -- SHADOW the source local of that name for the rest of the block,
    -- silently. Refused by name, before anything else about the shape.
    match (g.cellNames ++ g.targetBinders).find? (fun n => !n.startsWith "$") with
    | some n => some s!"binder '{n}' is not a reserved `$` slot name (every binder cell and target binder is `$`-prefixed — the frontend's reservation; a bare name would shadow the source local '{n}' for the rest of the block)"
    | none =>
    match g.occs.flatMap (·.body.valueBinds) |>.find? (fun b => !g.isCell b) with
    | some b => some s!"result binder '{b}' is not a declared cell"
    | none =>
    match g.cellNames.find? (fun c => (g.producer? c).isNone) with
    | some c => some s!"cell '{c}' is produced by no occurrence"
    | none =>
    match g.targetBinders.find? g.isCell with
    | some b => some s!"sort mismatch: '{b}' is both a TARGET and a VALUE binder"
    | none =>
    match g.occs.findSome? (fun o =>
        (o.body.mentions.find? g.isTargetBinder).map fun t =>
          s!"sort mismatch: TARGET binder '{t}' used as a value in occurrence '{o.name}'") with
    | some msg => some msg
    | none =>
    -- A `$`-prefixed name is a SLOT by the frontend's reservation (its temps
    -- and binders); one that is neither a cell nor a target binder is
    -- unknown, never an admitted source-local read.
    match g.occs.findSome? (fun o =>
        (o.body.mentions.find? (fun n => n.startsWith "$" && !g.isCell n && !g.isTargetBinder n)).map fun n =>
          s!"unknown slot '{n}' mentioned by occurrence '{o.name}'") with
    | some msg => some msg
    | none =>
    match g.occs.findSome? (fun o =>
        (o.body.targetMentions.find? (fun t => !g.isTargetBinder t)).map fun t =>
          s!"sort mismatch: occurrence '{o.name}' loads through '{t}', not a TARGET binder") with
    | some msg => some msg
    | none =>
    match g.occs.findSome? (fun o =>
        (o.after.find? (fun a => (g.index? a).isNone)).map fun a =>
          s!"unknown occurrence reference '{a}' in the order prerequisites of '{o.name}'") with
    | some msg => some msg
    | none =>
    match g.occs.findSome? (fun o =>
        match o.region with
        | some gn => if g.isGuard gn then none
            else some s!"region of '{o.name}' names '{gn}', which is not a guard occurrence"
        | none => none) with
    | some msg => some msg
    | none =>
    match g.occs.findSome? (fun o =>
        match o.body with
        | .guard test _ out =>
            if !g.isCell test then some s!"guard '{o.name}' tests '{test}', not a VALUE binder"
            else if !g.isCell out then some s!"guard '{o.name}' completion '{out}' is not a VALUE binder"
            else
              -- Audit N3 (2026-09-16): both cells are bool — the test is read
              -- as a bool, the skip STORES the short-circuit constant (a
              -- bool) into the completion cell; a mistyped cell was a
              -- run-time `.stuck` with a generic text, now a refusal by
              -- name at ENTER.
              match g.cellType? test, g.cellType? out with
              | some .bool, some .bool =>
                  match g.producer? out with
                  | some ci =>
                      match g.occs[ci]? with
                      | some c =>
                          if c.region == some o.name then none
                          else some s!"guard '{o.name}' completion '{out}' is not produced inside its region"
                      | none => some s!"guard '{o.name}' completion '{out}' has no producer"
                  | none => some s!"guard '{o.name}' completion '{out}' has no producer"
              | some .bool, some ty =>
                  some s!"guard '{o.name}' completion '{out}' is a cell of type {repr ty}, not a bool cell (the skip stores the short-circuit constant, a bool)"
              | some ty, _ =>
                  some s!"guard '{o.name}' tests '{test}', a cell of type {repr ty}, not a bool cell"
              | none, _ => some s!"guard '{o.name}' tests '{test}', a cell without a declared type"
        | .invoke binds _ _ =>
            if binds.length > 2 then
              some s!"invocation '{o.name}' with {binds.length} results is outside the Stage B fragment (0, 1 or 2)"
            else none
        | _ => none) with
    | some msg => some msg
    | none =>
    match g.stores.findSome? (fun (t, v) =>
        if !g.isTargetBinder t then some s!"store target '{t}' is not a TARGET binder"
        else if !g.isCell v then some s!"store value '{v}' is not a VALUE binder"
        else none) with
    | some msg => some msg
    | none => none

/-! ### The scheduler's readiness facts (proof interfaces for the coherence
theorems: `step_complete`, `stepFn_consumption_*`). -/

/-- A ready occurrence is an ACTIVE occurrence of the graph. -/
theorem ready_active {g : UnseqGraph} {st : List UnseqStatus} {j i : Nat}
    (h : (g.ready st)[j]? = some i) : i < g.occs.length ∧ st[i]? = some .active := by
  have hmem : i ∈ g.ready st := List.mem_of_getElem? h
  simp only [ready, List.mem_filter, List.mem_range] at hmem
  obtain ⟨hlt, hr⟩ := hmem
  refine ⟨hlt, ?_⟩
  unfold readyAt at hr
  split at hr
  · simp only [Bool.and_eq_true] at hr
    exact eq_of_beq hr.1.1.1
  · exact absurd hr (by simp)

/-- An active occurrence refutes «all settled». -/
theorem allSettled_false {g : UnseqGraph} {st : List UnseqStatus} {i : Nat}
    (hi : i < g.occs.length) (ha : st[i]? = some .active) : g.allSettled st = false := by
  unfold allSettled
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  have := hall i (List.mem_range.mpr hi)
  rw [ha] at this
  exact absurd this (by decide)

/-- «All settled» leaves nothing ready. -/
theorem ready_nil_of_allSettled {g : UnseqGraph} {st : List UnseqStatus}
    (h : g.allSettled st = true) : g.ready st = [] := by
  unfold ready
  rw [List.filter_eq_nil_iff]
  intro i hi
  unfold allSettled at h
  rw [List.all_eq_true] at h
  have hs := h i hi
  unfold readyAt
  split
  · intro hc
    simp only [Bool.and_eq_true] at hc
    have hact := eq_of_beq hc.1.1.1
    rw [hact] at hs
    exact absurd hs (by decide)
  · exact Bool.false_ne_true

end UnseqGraph

end GoLean.GoCore
