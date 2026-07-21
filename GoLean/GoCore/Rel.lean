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
- **Fall-through results — CLOSED** (arc `rel-completion` D2-proper,
  2026-07-21): frame exits (return AND fall-through) read result values from
  locations pinned at call time (`LookupsR` in `Step.call`, `LoadsR` at
  exit), so no exit path consults an environment. `.returning` is env-free
  like the other unwinding configs. This also makes the frame exit correct
  under Go-legal block-scoped shadowing of result names (bare `return`
  reads the *result variable*, not the innermost binding), which the old
  env-carried read got wrong.
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

/-- Resolving the freshly-declared result ids to their frame locations, at
call time — immediately after `DeclsR` declares them, when the resolution is
unambiguous (D2-proper, arc rel-completion: the frame exit no longer consults
any environment, so later shadowing cannot redirect the read). -/
inductive LookupsR (env : LocalEnv) : List Param → List Loc → Prop where
  | nil : LookupsR env [] []
  | cons {p ps loc locs} :
      LocalEnv.lookup env p.id = some loc →
      LookupsR env ps locs →
      LookupsR env (p :: ps) (loc :: locs)

/-- Reading call results at frame exit from their call-time-pinned locations.
State-only; no environment. -/
inductive LoadsR (s : ExecState) : List Loc → List GoValue → Prop where
  | nil : LoadsR s [] []
  | cons {loc locs v vs} :
      loadLoc s loc = .ok v →
      LoadsR s locs vs →
      LoadsR s (loc :: locs) (v :: vs)

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
  /-- Call frame: at frame exit (return OR fall-through), read the result
  values from `results` — the frame cells' *locations*, pinned at call time
  (D2-proper) — and store into `targets`. The caller environment is already
  carried by `k` (the caller's `seq`/`loop` continuation), so nothing is
  restored here. -/
  | frame (targets : List Loc) (results : List Loc) (k : Cont)

/-- The continuation for entering a `.seqn`: under a *same-env* governing
sequence, SPLICE the statements into it (D1, arc rel-completion) — Go
statement lists splice and only blocks scope, so a frontend-lowered nested
declaration group (`x := 1` → `.seqn #[init x, assign x 1]`) extends the env
of the *enclosing* rest, exactly like the interpreter's scope-transparent
`.seqn`. Any other continuation (or an env-mismatched seq, unreachable from
real programs — the fallback is the old wrap behavior, never a new claim)
wraps in a fresh seq node. A total function, so the `seqn` rule stays
single-conclusion and deterministic. -/
def seqCont (ss : List Stmt) (env : LocalEnv) : Cont → Cont
  | .seq rest env' k => if env' = env then .seq (ss ++ rest) env k
                        else .seq ss env (.seq rest env' k)
  | k => .seq ss env k

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
  /-- Unwinding a `return`. Env-free like the other completion configs
  (D2-proper): the frame reads results from call-time-pinned locations, so
  nothing needs the return-point environment. -/
  | returning (k : Cont)
  | panicked (msg : String)

/-- One small step over `(control, state)` pairs (`ExecState` is the Iris
`State` projection). No rule applies to malformed or unmodeled configurations:
they are stuck. `panicked` carries the state at the fault (terminal; the
post-state is inert). -/
inductive Step : Config → ExecState → Config → ExecState → Prop where
  -- Sequencing. Each `seq` continuation carries the environment active for
  -- its statements; exhausting it discards that environment (scope exit).
  -- Entering a nested `.seqn` under a same-env governing seq SPLICES (D1;
  -- see `seqCont`), so mid-list declarations extend the enclosing rest.
  | seqn {ss env k s} :
      Step (.exec (.seqn ss) env k) s (.next (seqCont ss.toList env k)) s
  | seqNext {t rest env k s} :
      Step (.next (.seq (t :: rest) env k)) s (.exec t env (.seq rest env k)) s
  | seqDone {env k s} :
      Step (.next (.seq [] env k)) s (.next k) s
  | seqBreak {rest env k s} :
      Step (.breaking (.seq rest env k)) s (.breaking k) s
  | seqContinue {rest env k s} :
      Step (.continuing (.seq rest env k)) s (.continuing k) s
  | seqReturn {rest env k s} :
      Step (.returning (.seq rest env k)) s (.returning k) s
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
  | loopReturn {c b env k s} :
      Step (.returning (.loop c b env k)) s (.returning k) s
  -- Control transfer statements. All three are env-free unwinding signals;
  -- the frame's result read uses call-time-pinned locations (D2-proper).
  | returnStmt {env k s} :
      Step (.exec .returnStmt env k) s (.returning k) s
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
  | call {targets funcId args func targetLocs argVals argsEnv frameEnv resultLocs env k s s₁ s₂ s₃ frameState} :
      AssigneesR env s targets.toList targetLocs s₁ →
      ArgsR env s₁ args.toList argVals s₂ →
      findFunctionIn? s₂.functions funcId = some func →
      BindParamsR [] s₂ func.args.toList argVals argsEnv s₃ →
      DeclsR argsEnv s₃ func.results.toList frameEnv frameState →
      LookupsR frameEnv func.results.toList resultLocs →
      Step (.exec (.call targets funcId args) env k) s
        (.exec func.body frameEnv (.frame targetLocs resultLocs k)) frameState
  -- Frame exit, explicit return: read the result values from the call-time
  -- pinned locations, store into caller targets, resume the caller (whose
  -- environment is carried by `k`).
  | frameReturn {targets results k s vs s'} :
      LoadsR s results vs →
      StoreManyR s targets vs s' →
      Step (.returning (.frame targets results k)) s (.next k) s'
  -- Frame exit, fall-through (normal completion of a function body): the
  -- SAME read/store as `frameReturn` (D2-proper — the fall-through results
  -- gap is closed; a value-returning fall-through stores the declared
  -- defaults, exactly as the interpreter does; for void frames both lists
  -- are empty and the step is pure).
  | frameFall {targets results k s vs s'} :
      LoadsR s results vs →
      StoreManyR s targets vs s' →
      Step (.next (.frame targets results k)) s (.next k) s'

/-- Strip leading sequence frames from a continuation — the stable form the
unwinding configurations (`breaking`/`continuing`/`returning`) reach after
the `seqBreak`/`seqContinue`/`seqReturn` steps discharge pending sequence
nodes. Loops and frames are barriers (their unwinding rules are semantic:
loop re-entry / frame result stores). With the D1 splice rule the machine
may skip intermediate wrapped forms, so simulation targets are stated at
the stripped continuation. -/
def Cont.stripSeqs : Cont → Cont
  | .seq _ _ k => k.stripSeqs
  | k => k

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

theorem Steps.breaking_strip (k : Cont) (s : ExecState) :
    Steps (.breaking k) s (.breaking k.stripSeqs) s := by
  induction k with
  | seq rest env k ih => exact (Steps.single Step.seqBreak).trans ih
  | stop => exact .refl _ _
  | loop c b env k ih => exact .refl _ _
  | frame t r k ih => exact .refl _ _

theorem Steps.continuing_strip (k : Cont) (s : ExecState) :
    Steps (.continuing k) s (.continuing k.stripSeqs) s := by
  induction k with
  | seq rest env k ih => exact (Steps.single Step.seqContinue).trans ih
  | stop => exact .refl _ _
  | loop c b env k ih => exact .refl _ _
  | frame t r k ih => exact .refl _ _

theorem Steps.returning_strip (k : Cont) (s : ExecState) :
    Steps (.returning k) s (.returning k.stripSeqs) s := by
  induction k with
  | seq rest env k ih => exact (Steps.single Step.seqReturn).trans ih
  | stop => exact .refl _ _
  | loop c b env k ih => exact .refl _ _
  | frame t r k ih => exact .refl _ _

/-- A configuration the sequential relation considers finished. -/
def Config.terminal : Config → Prop
  | .next .stop => True
  | .panicked _ => True
  | _ => False

end GoLean.GoCore.Rel
