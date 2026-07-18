import GoLean.GoCore.Ops

/-!
# GoCore relational semantics skeleton

This module is the first proof-facing semantics for GoCore, per
`docs/gocore-semantics-upgrade-goal.md` Phase 6 and the small-step design
note in `docs/gocore-semantics-upgrade-handoff.md`.

Reading of outcomes:

- **Panics are behavior**: they appear as explicit rules producing panic
  outcomes or the `panicked` terminal configuration.
- **Stuck and unsupported are the absence of rules**: malformed GoCore,
  violated invariants, and unmodeled features simply have no derivation.
  This is deliberately different from the executable interpreter, which
  must report *why* it stopped; the relation only says what well-formed
  programs may do.

Layering: this module imports the shared semantic substrate
(`Syntax`/`Value`/`State`/`Ops` — types, values, locations, state, typed
load/store/default/equality) but not the interpreter (`Eval`). Atomic state
operations appear as function premises (`loadLoc … = .ok v`); evaluation
order and control flow are relational rules. The correspondence between
this relation and the interpreter is stated in
`GoLean.GoCore.Correspondence`.

Iris-facing shape: `Step` is a binary relation on sequential
configurations. The eventual Iris-Lean `PrimStep` instance extends a step
to `Config → Obs → Config × List Config`, where the list is forked
goroutines; the sequential skeleton forks nothing, so the embedding is
`c ↦ (c', [])`. Observations are unit until prophecy-style reasoning is
needed.

Covered subset: scalar expressions and comparisons on integers and
booleans, pointer `ref`/`deref` (with the Go nil-dereference panic), struct
field access, array indexing (with the Go bounds panic), local declaration,
assignment, sequencing, blocks with lexical scope extent, `if`, `while`,
`return`/`break`/`continue`, and direct function calls with fresh frames
over a shared heap. Everything else (slices, maps, interfaces, effectful
builtins, multi-assignment) is intentionally outside the skeleton and has
no rules yet.
-/

namespace GoLean.GoCore.Rel

open GoLean

/-- Outcome of relational expression evaluation: a value with the updated
state, or a Go panic. Stuck/unsupported evaluation has no outcome. -/
inductive ExprOut where
  | value (v : GoValue) (s : ExecState)
  | panic (msg : String)

/-- Big-step expression evaluation relation. Expressions in the current
GoCore subset contain no calls, so big-step here composes with the
small-step statement relation without hiding interleaving points; if
calls-in-expressions land, expression evaluation must be refactored into
the configuration language. -/
inductive ExprR : ExecState → Expr → ExprOut → Prop where
  | var {s id v} :
      lookup s id = .ok v →
      ExprR s (.var id) (.value v s)
  | intLit {s value kind} :
      ExprR s (.intLit value kind) (.value (.int (kind.normalize value) kind) s)
  | boolLit {s value} :
      ExprR s (.boolLit value) (.value (.bool value) s)
  | stringLit {s value} :
      ExprR s (.stringLit value) (.value (.string value) s)
  | addInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR s l (.value (.int lv lk) s₁) →
      ExprR s₁ r (.value (.int rv rk) s₂) →
      IntKind.compatibleResult lk rk = some k →
      ExprR s (.add l r) (.value (.int (k.normalize (lv + rv)) k) s₂)
  | subInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR s l (.value (.int lv lk) s₁) →
      ExprR s₁ r (.value (.int rv rk) s₂) →
      IntKind.compatibleResult lk rk = some k →
      ExprR s (.sub l r) (.value (.int (k.normalize (lv - rv)) k) s₂)
  | mulInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR s l (.value (.int lv lk) s₁) →
      ExprR s₁ r (.value (.int rv rk) s₂) →
      IntKind.compatibleResult lk rk = some k →
      ExprR s (.mul l r) (.value (.int (k.normalize (lv * rv)) k) s₂)
  | divInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR s l (.value (.int lv lk) s₁) →
      ExprR s₁ r (.value (.int rv rk) s₂) →
      rv ≠ 0 →
      IntKind.compatibleResult lk rk = some k →
      ExprR s (.div l r) (.value (.int (k.normalize (Int.tdiv lv rv)) k) s₂)
  | divByZero {s s₁ s₂ l r lv lk rk} :
      ExprR s l (.value (.int lv lk) s₁) →
      ExprR s₁ r (.value (.int 0 rk) s₂) →
      ExprR s (.div l r) (.panic "integer divide by zero")
  | eqCmp {s s₁ s₂ ty l r lv rv b} :
      ExprR s l (.value lv s₁) →
      ExprR s₁ r (.value rv s₂) →
      valueEq s₂ ty lv rv = .ok b →
      ExprR s (.eqCmp ty l r) (.value (.bool b) s₂)
  | ref {s id loc} :
      lookupLoc s id = .ok loc →
      ExprR s (.ref id) (.value (.addr loc) s)
  | deref {s s₁ e ty loc v} :
      ExprR s e (.value (.addr loc) s₁) →
      loadLoc s₁ loc = .ok v →
      ExprR s (.deref e ty) (.value v s₁)
  | derefNil {s s₁ e ty} :
      ExprR s e (.value .nil s₁) →
      ExprR s (.deref e ty)
        (.panic "runtime error: invalid memory address or nil pointer dereference")
  | fieldGet {s s₁ recv typeId fieldName fields v} :
      ExprR s recv (.value (.struct typeId fields) s₁) →
      StructFields.lookup fields fieldName = some v →
      ExprR s (.fieldGet recv typeId fieldName) (.value v s₁)
  | indexGet {s s₁ s₂ base index values iv ik v} :
      ExprR s base (.value (.array values) s₁) →
      ExprR s₁ index (.value (.int iv ik) s₂) →
      arrayGet values iv = .ok v →
      ExprR s (.indexGet base index) (.value v s₂)
  | indexGetPanic {s s₁ s₂ base index values iv ik msg} :
      ExprR s base (.value (.array values) s₁) →
      ExprR s₁ index (.value (.int iv ik) s₂) →
      arrayGet values iv = .error (.panic msg) →
      ExprR s (.indexGet base index) (.panic msg)
  -- Panic propagation through strict binary arithmetic. Short-circuit
  -- operators (`and`/`or`) must not use these; they get their own rules
  -- when added.
  | binPanicLeft {s l r msg}
      (mk : Expr → Expr → Expr)
      (_ : mk = Expr.add ∨ mk = Expr.sub ∨ mk = Expr.mul ∨ mk = Expr.div) :
      ExprR s l (.panic msg) →
      ExprR s (mk l r) (.panic msg)
  | binPanicRight {s s₁ l r lv msg}
      (mk : Expr → Expr → Expr)
      (_ : mk = Expr.add ∨ mk = Expr.sub ∨ mk = Expr.mul ∨ mk = Expr.div) :
      ExprR s l (.value lv s₁) →
      ExprR s₁ r (.panic msg) →
      ExprR s (mk l r) (.panic msg)

/-- Outcome of resolving an assignee to a location. -/
inductive LocOut where
  | loc (l : Loc) (s : ExecState)
  | panic (msg : String)

inductive AssigneeR : ExecState → Assignee → LocOut → Prop where
  | var {s id loc} :
      lookupLoc s id = .ok loc →
      AssigneeR s (.var id) (.loc loc s)
  | addr {s s₁ e loc} :
      ExprR s e (.value (.addr loc) s₁) →
      AssigneeR s (.addr e) (.loc loc s₁)
  | addrNil {s s₁ e} :
      ExprR s e (.value .nil s₁) →
      AssigneeR s (.addr e)
        (.panic "runtime error: invalid memory address or nil pointer dereference")
  | addrPanic {s e msg} :
      ExprR s e (.panic msg) →
      AssigneeR s (.addr e) (.panic msg)

/-- Declaring a list of typed locals (block declarations, call frames). -/
inductive DeclsR : ExecState → List Param → ExecState → Prop where
  | nil {s} : DeclsR s [] s
  | cons {s s' p rest v} :
      defaultValue s p.typ = .ok v →
      DeclsR (s.declareLocal p.id (some p.typ) v) rest s' →
      DeclsR s (p :: rest) s'

/-- Left-to-right argument evaluation. -/
inductive ArgsR : ExecState → List Expr → List GoValue → ExecState → Prop where
  | nil {s} : ArgsR s [] [] s
  | cons {s s₁ s' e rest v vs} :
      ExprR s e (.value v s₁) →
      ArgsR s₁ rest vs s' →
      ArgsR s (e :: rest) (v :: vs) s'

/-- Binding call parameters into a fresh frame, normalized at declared
type. -/
inductive BindParamsR : ExecState → List Param → List GoValue → ExecState → Prop where
  | nil {s} : BindParamsR s [] [] s
  | cons {s s' p ps v v' vs} :
      normalizeValueForTy s p.typ v = .ok v' →
      BindParamsR (s.declareLocal p.id (some p.typ) v') ps vs s' →
      BindParamsR s (p :: ps) (v :: vs) s'

/-- Reading a function's named results at frame exit. -/
inductive ResultsR : ExecState → List Param → List GoValue → Prop where
  | nil {s} : ResultsR s [] []
  | cons {s p ps v vs} :
      lookup s p.id = .ok v →
      ResultsR s ps vs →
      ResultsR s (p :: ps) (v :: vs)

/-- Writing call results back to caller target locations. -/
inductive StoreManyR : ExecState → List Loc → List GoValue → ExecState → Prop where
  | nil {s} : StoreManyR s [] [] s
  | cons {s s₁ s' loc locs v vs} :
      storeLoc s loc v = .ok s₁ →
      StoreManyR s₁ locs vs s' →
      StoreManyR s (loc :: locs) (v :: vs) s'

/-- Resolving caller target assignees to locations, left to right. -/
inductive AssigneesR : ExecState → List Assignee → List Loc → ExecState → Prop where
  | nil {s} : AssigneesR s [] [] s
  | cons {s s₁ s' a rest loc locs} :
      AssigneeR s a (.loc loc s₁) →
      AssigneesR s₁ rest locs s' →
      AssigneesR s (a :: rest) (loc :: locs) s'

/-- Continuations for the small-step statement relation. -/
inductive Cont where
  | stop
  /-- Remaining statements of a sequence. -/
  | seq (rest : List Stmt) (k : Cont)
  /-- Pop one lexical scope when control leaves a block, on every path. -/
  | scope (k : Cont)
  /-- Loop context: normal completion and `continue` retest the condition,
  `break` resumes after the loop, `return` keeps unwinding. -/
  | loop (cond : Expr) (body : Stmt) (k : Cont)
  /-- Call frame: on return or fall-through, read `results`, restore
  `callerLocals`, and store into `targets`. -/
  | frame (callerLocals : LocalEnv) (targets : List Loc) (results : List Param) (k : Cont)

/-- Sequential configurations. `panicked` is terminal program behavior. -/
inductive Config where
  | exec (stmt : Stmt) (k : Cont) (s : ExecState)
  /-- The current statement completed normally. -/
  | next (k : Cont) (s : ExecState)
  | breaking (k : Cont) (s : ExecState)
  | continuing (k : Cont) (s : ExecState)
  | returning (k : Cont) (s : ExecState)
  | panicked (msg : String)

/-- One small step. No rule applies to malformed or unmodeled
configurations: they are stuck. -/
inductive Step : Config → Config → Prop where
  -- Sequencing.
  | seqn {ss k s} :
      Step (.exec (.seqn ss) k s) (.next (.seq ss.toList k) s)
  | seqNext {t rest k s} :
      Step (.next (.seq (t :: rest) k) s) (.exec t (.seq rest k) s)
  | seqDone {k s} :
      Step (.next (.seq [] k) s) (.next k s)
  | seqBreak {rest k s} :
      Step (.breaking (.seq rest k) s) (.breaking k s)
  | seqContinue {rest k s} :
      Step (.continuing (.seq rest k) s) (.continuing k s)
  | seqReturn {rest k s} :
      Step (.returning (.seq rest k) s) (.returning k s)
  -- Blocks and lexical scope extent.
  | block {decls ss k s s'} :
      DeclsR { s with locals := s.locals.pushScope } decls.toList s' →
      Step (.exec (.block decls ss) k s) (.next (.seq ss.toList (.scope k)) s')
  | scopeNext {k s} :
      Step (.next (.scope k) s) (.next k { s with locals := s.locals.popScope })
  | scopeBreak {k s} :
      Step (.breaking (.scope k) s) (.breaking k { s with locals := s.locals.popScope })
  | scopeContinue {k s} :
      Step (.continuing (.scope k) s) (.continuing k { s with locals := s.locals.popScope })
  | scopeReturn {k s} :
      Step (.returning (.scope k) s) (.returning k { s with locals := s.locals.popScope })
  -- Declaration and assignment.
  | initialization {p v k s} :
      defaultValue s p.typ = .ok v →
      Step (.exec (.initialization p) k s)
        (.next k (s.declareLocal p.id (some p.typ) v))
  | assign {lhs rhs loc v k s s₁ s₂ s₃} :
      AssigneeR s lhs (.loc loc s₁) →
      ExprR s₁ rhs (.value v s₂) →
      storeLoc s₂ loc v = .ok s₃ →
      Step (.exec (.assign lhs rhs) k s) (.next k s₃)
  | assignTargetPanic {lhs rhs msg k s} :
      AssigneeR s lhs (.panic msg) →
      Step (.exec (.assign lhs rhs) k s) (.panicked msg)
  | assignValuePanic {lhs rhs loc msg k s s₁} :
      AssigneeR s lhs (.loc loc s₁) →
      ExprR s₁ rhs (.panic msg) →
      Step (.exec (.assign lhs rhs) k s) (.panicked msg)
  | assignStorePanic {lhs rhs loc v msg k s s₁ s₂} :
      AssigneeR s lhs (.loc loc s₁) →
      ExprR s₁ rhs (.value v s₂) →
      storeLoc s₂ loc v = .error (.panic msg) →
      Step (.exec (.assign lhs rhs) k s) (.panicked msg)
  -- Conditionals.
  | ifTrue {c t e k s s'} :
      ExprR s c (.value (.bool true) s') →
      Step (.exec (.ifThenElse c t e) k s) (.exec t k s')
  | ifFalse {c t e k s s'} :
      ExprR s c (.value (.bool false) s') →
      Step (.exec (.ifThenElse c t e) k s) (.exec e k s')
  | ifPanic {c t e msg k s} :
      ExprR s c (.panic msg) →
      Step (.exec (.ifThenElse c t e) k s) (.panicked msg)
  -- Loops.
  | whileTrue {c b k s s'} :
      ExprR s c (.value (.bool true) s') →
      Step (.exec (.while c b) k s) (.exec b (.loop c b k) s')
  | whileFalse {c b k s s'} :
      ExprR s c (.value (.bool false) s') →
      Step (.exec (.while c b) k s) (.next k s')
  | whilePanic {c b msg k s} :
      ExprR s c (.panic msg) →
      Step (.exec (.while c b) k s) (.panicked msg)
  | loopNext {c b k s} :
      Step (.next (.loop c b k) s) (.exec (.while c b) k s)
  | loopContinue {c b k s} :
      Step (.continuing (.loop c b k) s) (.exec (.while c b) k s)
  | loopBreak {c b k s} :
      Step (.breaking (.loop c b k) s) (.next k s)
  | loopReturn {c b k s} :
      Step (.returning (.loop c b k) s) (.returning k s)
  -- Control transfer statements.
  | returnStmt {k s} :
      Step (.exec .returnStmt k s) (.returning k s)
  | breakStmt {k s} :
      Step (.exec .breakStmt k s) (.breaking k s)
  | continueStmt {k s} :
      Step (.exec .continueStmt k s) (.continuing k s)
  -- Direct calls: resolve targets and arguments in the caller, then enter
  -- a fresh frame sharing the heap. Dynamic dispatch is outside the
  -- skeleton (no rule when the callee expects an interface receiver).
  | call {targets funcId args func targetLocs argVals k s s₁ s₂ frameState} :
      AssigneesR s targets.toList targetLocs s₁ →
      ArgsR s₁ args.toList argVals s₂ →
      findFunctionIn? s₂.functions funcId = some func →
      BindParamsR { s₂ with locals := [] } func.args.toList argVals frameState →
      Step (.exec (.call targets funcId args) k s)
        (.exec func.body
          (.frame s₂.locals targetLocs func.results.toList k)
          frameState)
  | frameReturn {callerLocals targets results k s vs s'} :
      ResultsR s results vs →
      StoreManyR { s with locals := callerLocals } targets vs s' →
      Step (.returning (.frame callerLocals targets results k) s) (.next k s')
  | frameFall {callerLocals targets results k s vs s'} :
      ResultsR s results vs →
      StoreManyR { s with locals := callerLocals } targets vs s' →
      Step (.next (.frame callerLocals targets results k) s) (.next k s')

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Config → Config → Prop where
  | refl (c : Config) : Steps c c
  | tail {a b c} : Steps a b → Step b c → Steps a c

theorem Steps.single {a b : Config} (h : Step a b) : Steps a b :=
  .tail (.refl a) h

theorem Steps.trans {a b c : Config} : Steps a b → Steps b c → Steps a c := by
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

/-- A configuration the sequential relation considers finished. -/
def Config.terminal : Config → Prop
  | .next .stop _ => True
  | .panicked _ => True
  | _ => False

end GoLean.GoCore.Rel
