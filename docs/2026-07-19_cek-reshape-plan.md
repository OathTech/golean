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

## (ii) wiring pinned during execution (2026-07-19)

Resolved while coding the `Step` rules:
- **`.returning` carries env; `.next`/`.breaking`/`.continuing` do not.** `ToVal`
  only constrains the terminal `.next .stop`, so non-`.next` control configs may
  carry env freely. `return e` lowers to *assign the result local, then
  `.returnStmt`*, so results are named locals read from the **callee** env at
  frame exit — hence `.returning env k` must carry that env (threaded up through
  `seq`/`loop` conts, discarding their envs, until it hits `.frame`). `.breaking`/
  `.continuing` target the `loop` cont (which carries env) so they stay env-free.
- **`.scope` cont removed.** Under (ii) a block's env lives in its `seq` cont and
  is discarded at `seqDone`/`seqBreak`/… on every path, so `.scope` (which existed
  only to `popScope` `s.locals`) is vestigial. Block: `.exec (.block decls ss) env
  k → .next (.seq ss.toList env' k)` (no `.scope`), `DeclsR (env.pushScope) …`.
- **`.frame` drops `callerLocals`.** On return, `.next k` resumes and `k` (the
  caller's `seq`/frame cont) already carries the caller env — nothing to restore.
  `Cont.frame (targets) (results) (k)`.
- **Inline `.initialization` rebuilds its `seq` cont with the extended env:**
  `.exec (.initialization p) env (.seq rest env k)` (exec-env = seq-cont-env by
  `seqNext`) `→ .next (.seq rest (env.declare p.id loc) k)` after `s.alloc`. This
  is how mid-sequence `x := 0` scopes over the rest — the case that killed
  substitution, trivial here.
- **Results-allocation gap preserved, not fixed.** The current `Step.call` binds
  only `func.args`, not `func.results` (the interpreter declares results, the
  relation does not — a pre-existing skeleton gap, untested by the proven
  instances). This reshape *relocates locals→env only*; it does not close that
  gap. Track separately.

## Validation
- `lake build` (core) + `lake --dir=proofs build` green.
- `#print axioms` clean for `wp_seqn`, `wp_assign` (now unconditional-modulo-env),
  `go_adequacy`, `pointsTo_loadLoc`, bridges.
- Differential: **not re-run-critical** (interpreter untouched); one smoke slice to
  confirm behavior identical.
- Payoff check: instantiate `wp_assign` on the slice's `x = e` with a concrete
  `env` — the env premise discharges, so the law is genuinely usable (what #23
  was blocked on).

## Blast radius & future-compatibility (checked before go/no-go)

**Does env-in-control / option (ii) block later work? No — it enables the hard part.**
- **Concurrency (raft's core):** Go locals are per-goroutine; env-in-*control*
  gives thread-local locals for free (each goroutine's `Config` carries its own
  `env`), matching Iris/HeapLang (per-thread expr, shared heap). Env-in-*state*
  (rejected Option A) would have been a concurrency **blocker**. So this reshape
  is a prerequisite for concurrency, not an obstacle.
- **Closures:** capture the `env` at creation; locals are boxed heap cells, so
  capture-by-reference works via the captured locs. Fine under (ii).
- **Calls-in-expressions:** a known, already-flagged future refactor (`ExprR`
  big-step → Config-level), **independent** of env placement; (ii) extends cleanly.
- **Defer/recover, interface dispatch, the typed/field-granular heap upgrade:**
  orthogonal; no interaction.

**Blast radius:** touched = `Rel.lean` + `Correspondence.lean` + `GoLeanProofs.lean`
(proof-facing only). Untouched = interpreter (`Eval.lean`), `ExecState` fields
(`locals` stays for the interpreter), `NativeToIR`, frontend, differential corpus
→ **no possible behavioral regression**. Throwaway collateral: `SliceSpike.lean`'s
`env_bridge` and untracked `Probe.lean` need a trivial `env` update or deletion.

**De-risking refinement:** keep `env : LocalEnv` (the existing scope-stack type) —
the reshape then changes *where* locals live, not *how* they're represented (flat
env is a separate later simplification). One change, not two.

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

## DONE — executed 2026-07-19 (all green, all axiom-clean)

The reshape landed atomically across `Rel.lean` + `Correspondence.lean` +
`GoLeanProofs.lean` (+ the throwaway `SliceSpike.lean` bridge lemmas). Core
`lake build` green, proofs `lake build GoLeanProofs` green, `gocore-eval-tests`
40/40, differential unaffected (interpreter untouched). `#print axioms` for
`wp_seqn`, `wp_assign`, `wp_assign_lit`, `pointsTo_loadLoc`, `go_adequacy` =
`[propext, Classical.choice, Quot.sound]` (no `sorry`, no `native_decide`).

**Decisions pinned during execution (resolving the "open wiring" above):**
- **`env : LocalEnv`** kept (the existing scope-stack type) — reshape changes
  *where* locals live, not *how* represented. Flat-list simplification deferred.
- **Inline `.initialization` rides the seq cont:** `.exec (.initialization p) env
  (.seq rest env k) → .next (.seq rest (env.declare p.id loc) k)` after `s.alloc`
  (exec-env = seq-cont-env by `seqNext`). Matches option (ii)'s pinned wiring.
- **Fall-through vs return (the one point the plan left to pin):** `.returning`
  carries the callee `env` and `frameReturn` reads named results from it;
  fall-through `frameFall` (`.next (.frame …) → .next k`) stores *no* results.
  This avoids any `seqDone`-vs-frame rule overlap (they match different cont
  heads) with **no env on `.next`** (needed for the `ToVal` terminal). Rules
  `frameReturn`/`frameFall` are correct for void frames; named-result frames are
  gated by the **pre-existing results-allocation gap** (`Step.call` binds only
  `func.args`), which this reshape deliberately does *not* close. Both gaps are
  documented in `Rel.lean`'s module header.
- **`.scope` cont removed** — block env lives in its `seq` cont, discarded at
  `seqDone`; no `popScope`-on-state anywhere.

**`wp_assign` is now a usable law.** The unsatisfiable `hred` is replaced by the
pure resolution premise `LocalEnv.lookup env id = some (.base a)` (dischargeable —
`env` is fixed in the goal) plus ordinary rhs/store operational facts (`hrhs`,
`hrhs_det`, `hstore`). Determinism is derived by inverting the four assign
step-rules (the panic variants are refuted via `hrhs_det`, i.e. rhs
determinism). **`wp_assign_lit`** is the payoff check: for `x = intLit n` against
a concrete env binding `x ↦ .base a`, the resolution premise discharges by
`simp`, and `hrhs`/`hrhs_det` discharge outright (the latter via
`exprR_intLit_det`, which inverts `ExprR` on a literal past the function-valued
`binPanic*` indices using `generalize`). Only `hstore` (store-typing normalization)
remains — orthogonal to the resolution fix. This closes task #23.
