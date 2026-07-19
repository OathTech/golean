# CEK reshape — execution plan (2026-07-19)

Relocate locals from `ExecState` (state) to the relation's **control** so the WP
resolves against a Config-side environment (`docs/2026-07-19_env-in-config-cek.md`).
Atomic across `Rel.lean` + `Correspondence.lean` + `GoLeanProofs.lean`; the
**interpreter is untouched** (`ExecState.locals` stays — the interpreter uses it,
and it becomes the correspondence bridge), so the differential corpus is
unaffected. This is the plan; execution is the next (separate) phase.

## CRITICAL DECISION for the check-in: where does `env` live?

The Iris `ToVal` law forces this. `ToVal Config Unit` requires the terminal value
config to be **unique**: `toVal e = some () → ofVal () = e`, and `ofVal () = .next
.stop`. **If `env` sits on `.next`, then `.next env .stop` for `env ≠ []` all have
`toVal = some ()` but `≠ ofVal ()` — the law breaks.** So `env` must not be on the
terminal `.next .stop`. Candidates:

- **(i) env on every control config (`exec/next/breaking/…`), canonical-empty
  terminal.** Requires forcing the final `env` to `[]`, which the operational
  semantics doesn't naturally guarantee (a function ends with its params still in
  scope). Fragile — rejected.
- **(ii) env on `.exec` only; threaded through the `Cont` for continuations
  (`Cont.seq` carries `env`); `.next`/`.breaking`/… and the terminal are
  env-free.** `ToVal` is clean (terminal has no env). Bonus: the `Cont` structure
  now carries scope, so `.scope` becomes a near-noop and **`env` can be a flat
  `List (String × Loc)`** (the cont nesting handles lexical scope) — a
  simplification over the `LocalEnv` scope stack. **← recommended.**
- **(iii) env entirely in the `Cont`.** Similar to (ii); more `Cont` churn.

**Recommendation: (ii).** The rest of this plan assumes it. Settle this at the
check-in — it shapes every `Step` rule.

## The `declareLocal` split (the core mechanic)

Today `ExecState.declareLocal` = `freshLoc` + `Heap.set` (heap) **+**
`LocalEnv.declare` (locals). The relation splits it:
- **heap side:** `ExecState.alloc value (some ty) = (loc, s')` — *already exists*,
  heap-only. Use it.
- **env side:** `env.declare name loc` (or flat `(name, loc) :: env`).
The interpreter keeps `declareLocal` unchanged.

## Ordered edits (assuming (ii))

### 1. `Rel.lean` — expression/assignee relations gain `env` (fixed param)
- `inductive ExprR (env : LocalEnv) : ExecState → Expr → ExprOut → Prop`
  - `var`: `LocalEnv.lookup env id = some loc → loadLoc s loc = .ok v → ExprR env s (.var id) (.value v s)` (was `lookup s id`).
  - `ref`: `LocalEnv.lookup env id = some loc → ExprR env s (.ref id) (.value (.addr loc) s)` (was `lookupLoc s id`).
  - `locLit`: unchanged (vestigial, task #25).
  - every other rule: prefix `ExprR env` (env fixed, same in all recursive premises; no body change).
- `inductive AssigneeR (env : LocalEnv) : ExecState → Assignee → LocOut → Prop`
  - `var`: `LocalEnv.lookup env id = some loc → AssigneeR env s (.var id) (.loc loc s)`.
  - `addr`/`addrNil`/`addrPanic`: `ExprR env` in premises; prefix `env`.
- `ArgsR`, `AssigneesR`: add `env` fixed param (they call `ExprR`/`AssigneeR env`).
- `ResultsR (env)`: `LocalEnv.lookup env p.id = some loc → loadLoc s loc = .ok v` (was `lookup s p.id`).

### 2. `Rel.lean` — declaration relations produce a new `env`
- `DeclsR : LocalEnv → ExecState → List Param → LocalEnv → ExecState → Prop`
  - `nil`: `DeclsR env s [] env s`.
  - `cons`: `defaultValue s p.typ = .ok v → s.alloc v (some p.typ) = (loc, s₁) → DeclsR (env.declare p.id loc) s₁ rest env' s' → DeclsR env s (p::rest) env' s'`.
- `BindParamsR : LocalEnv → ExecState → List Param → List GoValue → LocalEnv → ExecState → Prop` (starts from `[]`): analogous, `normalizeValueForTy` + `alloc` + `env.declare`.
- `StoreManyR`: unchanged (uses `storeLoc`, heap-only, no env).

### 3. `Rel.lean` — `Cont`, `Config`, `Step`
- `Cont.seq (rest : List Stmt) (env : LocalEnv) (k : Cont)` — carries the env for
  `rest`. `Cont.frame` keeps the caller `env` (was `callerLocals`); `scope`/`loop`
  unchanged in shape.
- `Config.exec (stmt) (env : LocalEnv) (k)`; `next/breaking/continuing/returning
  (k)` **env-free**; `panicked (msg)`.
- `Step` (~30 rules), env-threaded per (ii). Highlights:
  - `seqn`: `.exec (.seqn ss) env k → .next (.seq ss.toList env k)`.
  - `seqNext`: `.next (.seq (t::rest) env k) → .exec t env (.seq rest env k)`.
  - `seqDone`: `.next (.seq [] _ k) → .next k`.
  - `initialization`: `defaultValue s p.typ = .ok v → s.alloc v (some p.typ) = (loc,s') → .exec (.initialization p) env k s → .next (.seq [] (env.declare p.id loc) k) s'` **or** carry the extended env into the enclosing seq — *resolve exact wiring with the (ii) `Cont.seq`-env at execution*. (Inline-decl-extends-env is the case (ii) makes trivial; pin the precise transition when coding.)
  - `block`: `DeclsR (env.pushScope-or-flat) s decls.toList env' s' → .exec (.block decls ss) env k s → .next (.seq ss.toList env' (.scope k)) s'`.
  - `scopeNext`: `.next (.scope k) s → .next k s` (env lives in k's cont; **no `s`
    mutation** — the old `popScope` on `s.locals` is gone).
  - `assign`: `AssigneeR env s lhs (.loc loc s₁) → ExprR env s₁ rhs (.value v s₂) →
    storeLoc s₂ loc v = .ok s₃ → .exec (.assign lhs rhs) env k s → .next k s₃`.
  - `if/while/loop/return/break/continue`: `ExprR env`; env threaded into the body
    exec / loop cont; control-completion configs env-free.
  - `call`: `AssigneesR env s targets → ArgsR env s₁ args → findFunctionIn? … →
    BindParamsR [] s₂ func.args argVals frameEnv frameState → .exec (.call …) env k s
    → .exec func.body frameEnv (.frame env targetLocs func.results k) frameState`
    (**no `{s with locals := []}`** — the callee's fresh scope is `env=[]`, state
    shared).
  - `frameReturn`/`frameFall`: `ResultsR env s results vs → StoreManyR s targetLocs
    vs s' → .returning/.next (.frame callerEnv targetLocs results k) s → .next k s'`
    with `k` carrying `callerEnv` (**no `{s with locals := callerLocals}`**).
- `Config.terminal`: `| .next .stop => True` (unchanged shape; terminal is env-free
  under (ii)).
- `Steps`/`Steps.trans`/`.single`: unchanged (env is inside `Config`).

### 4. `Correspondence.lean`
- `interpreterSound/PanicStatement`: start from `.exec stmt s.locals .stop`
  (interp's `s.locals` is the initial `env` — the bridge). Thread env in the
  terminal/panicked configs per (ii).
- Proven instances (`seqnNilSteps`, `whileFalseSteps`, `ifTrueReturnSteps`,
  `whileTrueBreakSteps`, `divByZeroPanics`): add an `env` param; the `Step`
  constructors now thread env, so the derivations update mechanically.
  `divByZeroPanics`'s `lookupLoc s "x"` becomes `LocalEnv.lookup env "x" = some loc`.

### 5. `GoLeanProofs.lean`
- `ToVal Config Unit`: unchanged and clean under (ii) (`.next .stop` env-free).
  `PrimStep`/`Language`/`GoPrimStep` unchanged. State interp **unchanged**
  (heap-only) — this is the whole point.
- `wp_seqn`: re-prove with env-threaded `.exec (.seqn ss) env k` → `.next (.seq …
  env k)` (mechanical).
- **`wp_assign` → the usable law.** Restate over `.exec (.assign (.var id) rhs)
  env k` with a **pure premise `⌜LocalEnv.lookup env id = some (.base a)⌝`**
  (dischargeable — `env` is fixed in the goal) in place of `hred`. The heap core is
  the spike's `wp_store`. This is the payoff: hred is gone.
- `go_adequacy`: re-prove (functor bundle unchanged; only the `Config` shape
  threads env). `pointsTo_loadLoc` unaffected (pure heap).

## Validation
- `lake build` (core) + `lake --dir=proofs build` green.
- `#print axioms` clean for `wp_seqn`, `wp_assign` (now unconditional-modulo-env),
  `go_adequacy`, `pointsTo_loadLoc`, bridges.
- Differential: **not re-run-critical** (interpreter untouched); one smoke slice to
  confirm behavior identical.
- Payoff check: instantiate `wp_assign` on the slice's `x = e` with a concrete
  `env` — the env premise discharges, so the law is genuinely usable (what #23
  was blocked on).

## Execution order & risk
- Order: `Rel.lean` (Cont → Config → Step → ExprR/AssigneeR/aux) → build (expect
  red) → `Correspondence.lean` → `GoLeanProofs.lean` → green. Atomic; compiler-first.
- Biggest effort: re-greening `GoLeanProofs.lean` (Language/wp_seqn/wp_assign/
  adequacy all touch `Config`). Biggest risk already retired by the spike (the WP
  shape) and by decision (ii) (ToVal). Only-commit-when-green; clean fallback is
  the current HEAD.
- Open wiring to pin while coding: the exact `initialization`/inline-decl
  transition under (ii)'s `Cont.seq`-env (whether the extended env rides in the
  seq cont or a one-step `.next (.seq [] env' k)`), and whether `env` is a flat
  list or keeps the `LocalEnv` scope stack (flat is viable under (ii); scope stack
  is a safe conservative choice).
