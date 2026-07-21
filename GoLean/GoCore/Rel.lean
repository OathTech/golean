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

## Locals live in the control (CEK), not the state

Per `docs/2026-07-19_env-in-config-cek.md` and the execution plan
`docs/2026-07-19_cek-reshape-plan.md`, the relation carries the current
frame's local environment `env : LocalEnv` (name → `Loc`) **in the control
configuration**, not in the `ExecState`. This is the textbook CEK-machine
representation: an abstract machine resolves variables through an
environment rather than substitution. The consequence for the Iris layer is
decisive — `env` sits in the fixed `Config` (the Iris *expression*), so a
variable's location `env[x] = some loc` is a pure fact about the goal,
discharged with no state camera and no `∀σ` quantification. The state
interpretation stays heap-only. Contrast the rejected env-in-state design,
which would have needed a camera on `σ.locals` (`docs/2026-07-19_locals-in-state-interp-design.md`).

Scope discipline is carried by the continuation, not by mutating state:
each `Cont.seq`/`Cont.loop` carries the `env` active for its statements, and
a scope simply ends when its `seq` continuation is exhausted (its `env` is
discarded — there is no `popScope` on the state). Blocks push a fresh scope
into the `env` they hand to their `seq` continuation. Mid-sequence
declarations (`x := 0`) extend the `env` of the *rest* of the enclosing
sequence — the case that makes substitution painful and an environment
trivial. The executable interpreter keeps `ExecState.locals` (it resolves
names against the state); that field is the correspondence bridge
`σ.locals ≈ Config.env`, not something the relation reads.

Iris-facing shape: `Step` is a binary relation on sequential
configurations paired with the `ExecState`. The eventual Iris-Lean
`PrimStep` instance extends a step to `Config → Obs → Config × List Config`,
where the list is forked goroutines; the sequential skeleton forks nothing,
so the embedding is `c ↦ (c', [])`. Observations are unit until
prophecy-style reasoning is needed. Env-in-control is also the prerequisite
for goroutine concurrency: each goroutine's `Config` carries its own `env`
(thread-local locals) over the shared heap, matching Iris/HeapLang.

Covered subset: scalar expressions and comparisons on integers and
booleans, pointer `ref`/`deref` (with the Go nil-dereference panic), struct
field access, array indexing (with the Go bounds panic), local declaration,
assignment, sequencing, blocks with lexical scope extent, `if`, `while`,
`return`/`break`/`continue`, and direct function calls with fresh frames
over a shared heap. Everything else (slices, maps, interfaces, effectful
builtins, multi-assignment) is intentionally outside the skeleton and has
no rules yet.

Known skeleton gaps (tracked, unexercised by the proven instances):
- **Results-allocation gap — CLOSED** (arc `slice-call-frame` item 4,
  2026-07-20): `Step.call` now allocates `func.results` at their default
  values into the frame env after binding `func.args` (via `DeclsR`),
  mirroring the interpreter's `execFunctionWithValues`. `return x` assigns
  the result local, which `frameReturn`'s `ResultsR` reads at frame exit.
- **Fall-through results.** A function body that completes normally
  (`frameFall`) stores no results — normal-completion configs (`.next`) are
  env-free by design (the Iris `ToVal` law forbids the terminal `.next .stop`
  from carrying an env), so the callee env is unavailable there. Explicit
  `return` (`frameReturn`) does read results, because `.returning` carries
  the callee env. Void functions are correct either way; Go's own semantics
  require an explicit `return` in any function with results (a missing
  return is a compile error), so named-result fall-through is unreachable
  from real Go — recorded here because the *relation* does not forbid it.
-/

namespace GoLean.GoCore.Rel

open GoLean

/-- Outcome of relational expression evaluation: a value with the updated
state, or a Go panic. Stuck/unsupported evaluation has no outcome. -/
inductive ExprOut where
  | value (v : GoValue) (s : ExecState)
  | panic (msg : String)

/-- Big-step expression evaluation relation, resolving variables against the
control-side environment `env` (CEK). Expressions in the current GoCore
subset contain no calls, so big-step here composes with the small-step
statement relation without hiding interleaving points; if
calls-in-expressions land, expression evaluation must be refactored into
the configuration language. -/
inductive ExprR (env : LocalEnv) : ExecState → Expr → ExprOut → Prop where
  | var {s id loc v} :
      LocalEnv.lookup env id = some loc →
      loadLoc s loc = .ok v →
      ExprR env s (.var id) (.value v s)
  | intLit {s value kind} :
      ExprR env s (.intLit value kind) (.value (.int (kind.normalize value) kind) s)
  | boolLit {s value} :
      ExprR env s (.boolLit value) (.value (.bool value) s)
  | stringLit {s value} :
      ExprR env s (.stringLit value) (.value (.string value) s)
  | addInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR env s l (.value (.int lv lk) s₁) →
      ExprR env s₁ r (.value (.int rv rk) s₂) →
      IntKind.compatibleResult lk rk = some k →
      ExprR env s (.add l r) (.value (.int (k.normalize (lv + rv)) k) s₂)
  | subInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR env s l (.value (.int lv lk) s₁) →
      ExprR env s₁ r (.value (.int rv rk) s₂) →
      IntKind.compatibleResult lk rk = some k →
      ExprR env s (.sub l r) (.value (.int (k.normalize (lv - rv)) k) s₂)
  | mulInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR env s l (.value (.int lv lk) s₁) →
      ExprR env s₁ r (.value (.int rv rk) s₂) →
      IntKind.compatibleResult lk rk = some k →
      ExprR env s (.mul l r) (.value (.int (k.normalize (lv * rv)) k) s₂)
  | divInt {s s₁ s₂ l r lv rv lk rk k} :
      ExprR env s l (.value (.int lv lk) s₁) →
      ExprR env s₁ r (.value (.int rv rk) s₂) →
      rv ≠ 0 →
      IntKind.compatibleResult lk rk = some k →
      ExprR env s (.div l r) (.value (.int (k.normalize (Int.tdiv lv rv)) k) s₂)
  | divByZero {s s₁ s₂ l r lv lk rk} :
      ExprR env s l (.value (.int lv lk) s₁) →
      ExprR env s₁ r (.value (.int 0 rk) s₂) →
      ExprR env s (.div l r) (.panic "runtime error: integer divide by zero")
  | eqCmp {s s₁ s₂ ty l r lv rv b} :
      ExprR env s l (.value lv s₁) →
      ExprR env s₁ r (.value rv s₂) →
      valueEq s₂ ty lv rv = .ok b →
      ExprR env s (.eqCmp ty l r) (.value (.bool b) s₂)
  | ref {s id loc} :
      LocalEnv.lookup env id = some loc →
      ExprR env s (.ref id) (.value (.addr loc) s)
  | locLit {s l} :
      ExprR env s (.locLit l) (.value (.addr l) s)
  | deref {s s₁ e ty loc v} :
      ExprR env s e (.value (.addr loc) s₁) →
      loadLoc s₁ loc = .ok v →
      ExprR env s (.deref e ty) (.value v s₁)
  | derefNil {s s₁ e ty} :
      ExprR env s e (.value .nil s₁) →
      ExprR env s (.deref e ty)
        (.panic "runtime error: invalid memory address or nil pointer dereference")
  | fieldGet {s s₁ recv typeId fieldName fields v} :
      ExprR env s recv (.value (.struct typeId fields) s₁) →
      StructFields.lookup fields fieldName = some v →
      ExprR env s (.fieldGet recv typeId fieldName) (.value v s₁)
  | indexGet {s s₁ s₂ base index values iv ik v} :
      ExprR env s base (.value (.array values) s₁) →
      ExprR env s₁ index (.value (.int iv ik) s₂) →
      arrayGet values iv = .ok v →
      ExprR env s (.indexGet base index) (.value v s₂)
  | indexGetPanic {s s₁ s₂ base index values iv ik msg} :
      ExprR env s base (.value (.array values) s₁) →
      ExprR env s₁ index (.value (.int iv ik) s₂) →
      arrayGet values iv = .error (.panic msg) →
      ExprR env s (.indexGet base index) (.panic msg)
  -- Panic propagation through strict binary arithmetic. Short-circuit
  -- operators (`and`/`or`) must not use these; they get their own rules
  -- when added.
  | binPanicLeft {s l r msg}
      (mk : Expr → Expr → Expr)
      (_ : mk = Expr.add ∨ mk = Expr.sub ∨ mk = Expr.mul ∨ mk = Expr.div) :
      ExprR env s l (.panic msg) →
      ExprR env s (mk l r) (.panic msg)
  | binPanicRight {s s₁ l r lv msg}
      (mk : Expr → Expr → Expr)
      (_ : mk = Expr.add ∨ mk = Expr.sub ∨ mk = Expr.mul ∨ mk = Expr.div) :
      ExprR env s l (.value lv s₁) →
      ExprR env s₁ r (.panic msg) →
      ExprR env s (mk l r) (.panic msg)

/-- Outcome of resolving an assignee to a location. -/
inductive LocOut where
  | loc (l : Loc) (s : ExecState)
  | panic (msg : String)

inductive AssigneeR (env : LocalEnv) : ExecState → Assignee → LocOut → Prop where
  | var {s id loc} :
      LocalEnv.lookup env id = some loc →
      AssigneeR env s (.var id) (.loc loc s)
  | addr {s s₁ e loc} :
      ExprR env s e (.value (.addr loc) s₁) →
      AssigneeR env s (.addr e) (.loc loc s₁)
  | addrNil {s s₁ e} :
      ExprR env s e (.value .nil s₁) →
      AssigneeR env s (.addr e)
        (.panic "runtime error: invalid memory address or nil pointer dereference")
  | addrPanic {s e msg} :
      ExprR env s e (.panic msg) →
      AssigneeR env s (.addr e) (.panic msg)

/-- Declaring a list of typed locals (block declarations). Threads the
control-side environment: each declaration allocates a fresh heap cell
(`ExecState.alloc`, heap-only) and extends the environment with the new
name→location binding, producing the final `env'`. -/
inductive DeclsR : LocalEnv → ExecState → List Param → LocalEnv → ExecState → Prop where
  | nil {env s} : DeclsR env s [] env s
  | cons {env env' s s₁ s' p rest v loc} :
      defaultValue s p.typ = .ok v →
      s.alloc v (some p.typ) = (loc, s₁) →
      DeclsR (env.declare p.id loc) s₁ rest env' s' →
      DeclsR env s (p :: rest) env' s'

/-- Left-to-right argument evaluation against the caller environment. -/
inductive ArgsR (env : LocalEnv) : ExecState → List Expr → List GoValue → ExecState → Prop where
  | nil {s} : ArgsR env s [] [] s
  | cons {s s₁ s' e rest v vs} :
      ExprR env s e (.value v s₁) →
      ArgsR env s₁ rest vs s' →
      ArgsR env s (e :: rest) (v :: vs) s'

/-- Binding call parameters into a fresh frame environment, normalized at
declared type. Starts from an empty environment `[]` (the callee's fresh
scope) and produces the frame environment `env'`; each parameter allocates a
heap cell over the shared heap. -/
inductive BindParamsR : LocalEnv → ExecState → List Param → List GoValue → LocalEnv → ExecState → Prop where
  | nil {env s} : BindParamsR env s [] [] env s
  | cons {env env' s s₁ s' p ps v v' vs loc} :
      normalizeValueForTy s p.typ v = .ok v' →
      s.alloc v' (some p.typ) = (loc, s₁) →
      BindParamsR (env.declare p.id loc) s₁ ps vs env' s' →
      BindParamsR env s (p :: ps) (v :: vs) env' s'

/-- Reading a function's named results at frame exit, resolved against the
callee frame environment `env`. -/
inductive ResultsR (env : LocalEnv) : ExecState → List Param → List GoValue → Prop where
  | nil {s} : ResultsR env s [] []
  | cons {s p ps v vs loc} :
      LocalEnv.lookup env p.id = some loc →
      loadLoc s loc = .ok v →
      ResultsR env s ps vs →
      ResultsR env s (p :: ps) (v :: vs)

/-- Writing call results back to caller target locations. Heap-only; no
environment. -/
inductive StoreManyR : ExecState → List Loc → List GoValue → ExecState → Prop where
  | nil {s} : StoreManyR s [] [] s
  | cons {s s₁ s' loc locs v vs} :
      storeLoc s loc v = .ok s₁ →
      StoreManyR s₁ locs vs s' →
      StoreManyR s (loc :: locs) (v :: vs) s'

/-- Resolving caller target assignees to locations, left to right, against
the caller environment. -/
inductive AssigneesR (env : LocalEnv) : ExecState → List Assignee → List Loc → ExecState → Prop where
  | nil {s} : AssigneesR env s [] [] s
  | cons {s s₁ s' a rest loc locs} :
      AssigneeR env s a (.loc loc s₁) →
      AssigneesR env s₁ rest locs s' →
      AssigneesR env s (a :: rest) (loc :: locs) s'

/-- Continuations for the small-step statement relation. Each continuation
that resumes statement execution carries the `env` active for those
statements (CEK): the environment is scope, so scope exit is just discarding
a continuation's `env`. -/
inductive Cont where
  | stop
  /-- Remaining statements of a sequence, with the environment active for
  them. Exhausting the sequence discards this `env` (scope exit). -/
  | seq (rest : List Stmt) (env : LocalEnv) (k : Cont)
  /-- Loop context, carrying the environment to re-enter the loop with.
  Normal completion and `continue` retest the condition, `break` resumes
  after the loop, `return` keeps unwinding. -/
  | loop (cond : Expr) (body : Stmt) (env : LocalEnv) (k : Cont)
  /-- Call frame: on `return`, read `results` from the callee environment
  (carried by the `returning` config) and store into `targets`. The caller
  environment is already carried by `k` (the caller's `seq`/`loop`
  continuation), so nothing is restored here. -/
  | frame (targets : List Loc) (results : List Param) (k : Cont)

/-- Sequential **control** configurations — the Iris `Expr` projection.

Reshape A (`docs/2026-07-18_reshape-a-design.md`): `Config` does not embed the
`ExecState`; the state is the paired component of `Step`, so `Config` is a valid
Iris `Expr` (`ToVal`'s round-trip law forbids the term carrying the heap).

CEK (`docs/2026-07-19_cek-reshape-plan.md`): the executing configuration
`exec` carries the current `env`, and `returning` carries the callee `env`
(so named results are readable at frame exit). Normal/loop-control
completion configs (`next`/`breaking`/`continuing`) are env-free — the Iris
`ToVal` law constrains the terminal `.next .stop`, so it must not carry an
`env`; the active environment for what follows lives in the continuation.
`panicked` is terminal program behavior. -/
inductive Config where
  | exec (stmt : Stmt) (env : LocalEnv) (k : Cont)
  /-- The current statement completed normally. Env-free (see above). -/
  | next (k : Cont)
  | breaking (k : Cont)
  | continuing (k : Cont)
  /-- Unwinding a `return`; carries the callee environment so `frame` can
  read named results. -/
  | returning (env : LocalEnv) (k : Cont)
  | panicked (msg : String)

/-- One small step over `(control, state)` pairs (`ExecState` is the Iris
`State` projection). No rule applies to malformed or unmodeled configurations:
they are stuck. `panicked` carries the state at the fault (terminal; the
post-state is inert). -/
inductive Step : Config → ExecState → Config → ExecState → Prop where
  -- Sequencing. Each `seq` continuation carries the environment active for
  -- its statements; exhausting it discards that environment (scope exit).
  | seqn {ss env k s} :
      Step (.exec (.seqn ss) env k) s (.next (.seq ss.toList env k)) s
  | seqNext {t rest env k s} :
      Step (.next (.seq (t :: rest) env k)) s (.exec t env (.seq rest env k)) s
  | seqDone {env k s} :
      Step (.next (.seq [] env k)) s (.next k) s
  | seqBreak {rest env k s} :
      Step (.breaking (.seq rest env k)) s (.breaking k) s
  | seqContinue {rest env k s} :
      Step (.continuing (.seq rest env k)) s (.continuing k) s
  | seqReturn {retEnv rest env k s} :
      Step (.returning retEnv (.seq rest env k)) s (.returning retEnv k) s
  -- Blocks: push a fresh scope, declare block locals into it, and hand the
  -- extended environment to the block's sequence continuation. There is no
  -- separate `scope` continuation — the block's environment is discarded
  -- when its `seq` continuation is exhausted.
  | block {decls ss env env' k s s'} :
      DeclsR env.pushScope s decls.toList env' s' →
      Step (.exec (.block decls ss) env k) s (.next (.seq ss.toList env' k)) s'
  -- Declaration and assignment. A mid-sequence declaration extends the
  -- environment of the *rest* of the enclosing sequence (its `seq`
  -- continuation) — the environment is the scope, so this is a local edit,
  -- not a reach into the continuation.
  | initialization {p v loc rest env k s s'} :
      defaultValue s p.typ = .ok v →
      s.alloc v (some p.typ) = (loc, s') →
      Step (.exec (.initialization p) env (.seq rest env k)) s
        (.next (.seq rest (env.declare p.id loc) k)) s'
  | assign {lhs rhs loc v env k s s₁ s₂ s₃} :
      AssigneeR env s lhs (.loc loc s₁) →
      ExprR env s₁ rhs (.value v s₂) →
      storeLoc s₂ loc v = .ok s₃ →
      Step (.exec (.assign lhs rhs) env k) s (.next k) s₃
  | assignTargetPanic {lhs rhs msg env k s} :
      AssigneeR env s lhs (.panic msg) →
      Step (.exec (.assign lhs rhs) env k) s (.panicked msg) s
  | assignValuePanic {lhs rhs loc msg env k s s₁} :
      AssigneeR env s lhs (.loc loc s₁) →
      ExprR env s₁ rhs (.panic msg) →
      Step (.exec (.assign lhs rhs) env k) s (.panicked msg) s₁
  | assignStorePanic {lhs rhs loc v msg env k s s₁ s₂} :
      AssigneeR env s lhs (.loc loc s₁) →
      ExprR env s₁ rhs (.value v s₂) →
      storeLoc s₂ loc v = .error (.panic msg) →
      Step (.exec (.assign lhs rhs) env k) s (.panicked msg) s₂
  -- Conditionals. Branch statements execute under the same environment;
  -- a `block` branch pushes its own scope.
  | ifTrue {c t e env k s s'} :
      ExprR env s c (.value (.bool true) s') →
      Step (.exec (.ifThenElse c t e) env k) s (.exec t env k) s'
  | ifFalse {c t e env k s s'} :
      ExprR env s c (.value (.bool false) s') →
      Step (.exec (.ifThenElse c t e) env k) s (.exec e env k) s'
  | ifPanic {c t e msg env k s} :
      ExprR env s c (.panic msg) →
      Step (.exec (.ifThenElse c t e) env k) s (.panicked msg) s
  -- Loops. The loop continuation carries the environment to re-enter with.
  | whileTrue {c b env k s s'} :
      ExprR env s c (.value (.bool true) s') →
      Step (.exec (.while c b) env k) s (.exec b env (.loop c b env k)) s'
  | whileFalse {c b env k s s'} :
      ExprR env s c (.value (.bool false) s') →
      Step (.exec (.while c b) env k) s (.next k) s'
  | whilePanic {c b msg env k s} :
      ExprR env s c (.panic msg) →
      Step (.exec (.while c b) env k) s (.panicked msg) s
  | loopNext {c b env k s} :
      Step (.next (.loop c b env k)) s (.exec (.while c b) env k) s
  | loopContinue {c b env k s} :
      Step (.continuing (.loop c b env k)) s (.exec (.while c b) env k) s
  | loopBreak {c b env k s} :
      Step (.breaking (.loop c b env k)) s (.next k) s
  | loopReturn {retEnv c b env k s} :
      Step (.returning retEnv (.loop c b env k)) s (.returning retEnv k) s
  -- Control transfer statements. `return` carries the current environment
  -- into `returning` so the frame can read named results; `break`/`continue`
  -- target a loop continuation and need no environment.
  | returnStmt {env k s} :
      Step (.exec .returnStmt env k) s (.returning env k) s
  | breakStmt {env k s} :
      Step (.exec .breakStmt env k) s (.breaking k) s
  | continueStmt {env k s} :
      Step (.exec .continueStmt env k) s (.continuing k) s
  -- Direct calls: resolve targets and arguments in the caller, then enter a
  -- fresh frame (env `[]` extended by the parameters, then the named results
  -- allocated at their default values — mirroring the interpreter's
  -- `execFunctionWithValues`, which binds params then declares results) over
  -- the shared heap. Dynamic dispatch is outside the skeleton (no rule when
  -- the callee expects an interface receiver). (Arc slice-call-frame item 4:
  -- this closes the results-allocation gap — `return x` assigns the result
  -- local, which now exists in the frame env for `frameReturn` to read.)
  | call {targets funcId args func targetLocs argVals argsEnv frameEnv env k s s₁ s₂ s₃ frameState} :
      AssigneesR env s targets.toList targetLocs s₁ →
      ArgsR env s₁ args.toList argVals s₂ →
      findFunctionIn? s₂.functions funcId = some func →
      BindParamsR [] s₂ func.args.toList argVals argsEnv s₃ →
      DeclsR argsEnv s₃ func.results.toList frameEnv frameState →
      Step (.exec (.call targets funcId args) env k) s
        (.exec func.body frameEnv (.frame targetLocs func.results.toList k)) frameState
  -- Explicit return: read named results from the callee environment carried
  -- by `returning`, store into caller targets, resume the caller (whose
  -- environment is carried by `k`).
  | frameReturn {calleeEnv targets results k s vs s'} :
      ResultsR calleeEnv s results vs →
      StoreManyR s targets vs s' →
      Step (.returning calleeEnv (.frame targets results k)) s (.next k) s'
  -- Fall-through (normal completion of a function body). Normal-completion
  -- configs are env-free, so no results are read here (fall-through results
  -- gap — see the module header); correct for void functions.
  | frameFall {targets results k s} :
      Step (.next (.frame targets results k)) s (.next k) s

/-- Reflexive-transitive closure of `Step` over `(control, state)` pairs. -/
inductive Steps : Config → ExecState → Config → ExecState → Prop where
  | refl (c : Config) (s : ExecState) : Steps c s c s
  | tail {a sa b sb c sc} : Steps a sa b sb → Step b sb c sc → Steps a sa c sc

theorem Steps.single {a b : Config} {sa sb : ExecState} (h : Step a sa b sb) :
    Steps a sa b sb :=
  .tail (.refl a sa) h

theorem Steps.trans {a b c : Config} {sa sb sc : ExecState} :
    Steps a sa b sb → Steps b sb c sc → Steps a sa c sc := by
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact .tail ih hstep

/-- A configuration the sequential relation considers finished. -/
def Config.terminal : Config → Prop
  | .next .stop => True
  | .panicked _ => True
  | _ => False

end GoLean.GoCore.Rel
