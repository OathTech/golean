# Reshape mechanics — where name→Loc resolution lives (2026-07-19)

Design for the location-resolved relation (foundation decided:
`docs/2026-07-19_goose-perennial-mapping.md`; de-risked:
`proofs/SliceSpike.lean`). The open question was: *where does name→`Loc`
resolution happen in the reshaped relation* — substitution at declaration, or a
resolve-step. Worked through the WP-provability constraint, the fork largely
collapses.

## The governing constraint

The whole reason for the reshape: `wp_assign`'s `hred` was unsatisfiable because
the state interpretation can't pin `σ.locals`. So the invariant we must preserve
is: **the relation must never perform a name→`Loc` lookup that the WP would have
to discharge against an unconstrained `σ`.** Any resolution the *relation* does
at a point where `σ` is WP-quantified re-creates exactly the `hred`/env-camera
problem.

## Fork analysis (it collapses)

- **Resolve-step-with-env (rejected).** A relation step that resolves `.var x` →
  `Loc` must read a name environment. If that env is in the state, the resolve
  step's WP needs it *pinned* — the env camera (Option A) we already rejected.
  So a runtime resolve-step does not escape the problem; it *is* Option A wearing
  a different hat.
- **"Resolve once and thread the `Loc` into the continuation."** The only way to
  resolve without a persistent env is to compute the `Loc` at the *binder* and
  carry it forward in the term/continuation — i.e. **substitution**. So a
  well-posed resolve-step converges to substitution-at-declaration.
- **Static stack slots + a frame base (VST / CompCert).** A genuine alternative:
  locals are frame-relative offsets resolved statically at lowering, with a
  frame-base pointer in the state. But that reintroduces a (lighter) environment
  — the frame base — into the state interpretation, and it diverges from the
  Goose/Perennial model the mapping endorsed (per-variable heap `Loc`s, first-
  class ownable, which closures/receivers will want). Kept as a fallback, not the
  plan.

**Conclusion: substitution at declaration.** It is the only mechanism that keeps
the relation's WP hred-free while matching the endorsed foundation.

## The concrete mechanism (minimal in GoLean's CK machine)

The key economy: GoLean already has the pointer machinery (`.ref`/`.deref`/
`.addr`, `ExprR`/`AssigneeR`). A resolved local **is just its address**, so we
reuse all of it and add exactly **one node**.

1. **One new expression node — `Expr.locLit (l : Loc)`** (a resolved location =
   an address constant). Its only rule:
   `ExprR.locLit : ExprR s (.locLit l) (.value (.addr l) s)` — no lookup.
2. **Capture-avoiding substitution `substLoc (name) (l : Loc)` over
   `Stmt`/`Expr`/`Assignee`/`Cont`.** It rewrites the *name-referencing* forms
   into location forms, and stops descending at any re-declaration of `name`
   (shadowing → the inner binder substitutes its own `Loc`):
   - `Expr.var name`      → `Expr.deref (.locLit l) tyₓ`  (a local read = load its cell)
   - `Expr.ref name`      → `Expr.locLit l`               (`&x` = the address)
   - `Assignee.var name`  → `Assignee.addr (.locLit l)`   (`x = e` = store at `l`)
3. **Declaration steps substitute instead of binding into `LocalEnv`.**
   `Step.initialization` / `Step.block` / param-binding allocate the fresh `Loc`
   (`freshLoc`, as now — a heap allocation, à la `GoAlloc`) and **`substLoc name
   l` into the continuation** (the block body / remaining statements), rather than
   recording `name→l` in `σ.locals`.
4. **`σ.locals` becomes dead in the relation.** The reshaped relation never reads
   it, so the state interpretation stays heap-only *without removing the field*
   (it's simply unused; the WP can't be forced to pin what the relation never
   reads). Removing it from the relation's state projection is optional cleanup,
   not a prerequisite.
5. **Everything downstream is reused unchanged.** After substitution, a read is
   `.deref (.locLit l)` (existing deref rule → `loadLoc`), an address is
   `.locLit l`, and an assign is `.addr (.locLit l)` (existing `AssigneeR.addr` →
   `storeLoc`). So `wp_assign` becomes the resolved `wp_store` the spike already
   proved hred-free; `wp_deref`/`wp_ref` fall out of the existing pointer rules.

Faithfulness: GoLean locals are already heap cells (`declareLocal` allocates),
and `lookup s x = loadLoc (lookupLoc s x)`, so rewriting `.var x` to `.deref
(.locLit l)` loads the *same* cell — the substitution changes representation, not
behavior. (This is exactly Goose's "box every local; read = `Deref`" model.)

## Correspondence (unchanged plan, now concrete)

Interpreter keeps names + `LocalEnv` (the differentiator, diff-tested). The
substitution IS the correspondence witness: where the interpreter has `lookupLoc
σ x = l`, the reshaped relation has `.locLit l` substituted for `x`. `env_bridge`
/ `env_bridge_inv` (spike) are the assign-case instances of this general fact.

## Scope: the slice first

Reshape only what the pointer+call slice needs, validated per step against the
differential baseline (interpreter untouched, so the corpus is unaffected):
1. Add `Expr.locLit` + `ExprR.locLit`.
2. Add `substLoc` for the slice's forms (`var`/`ref`/`addr`/`assign`/`deref`/
   `call`), with capture-avoidance; unit-test it.
3. Rewrite `Step.initialization` (and the call's param-binding) to substitute.
4. Re-target the WP layer: `wp_store`/`wp_deref`/`wp_ref`/`wp_call` over the
   resolved forms (the spike's `wp_store` is the template), then compose the
   `inc`/`main` specs (L6) `∀`-generally.
5. Then the correspondence (L4) for the reshaped, substitution-based fragment,
   with the interpreter's env as the bridge.

## Risks / notes

- **Capture-avoiding `substLoc` correctness** — standard, but must stop at
  re-binders; unit-test shadowing directly.
- **Every local read becomes a heap load** (`.deref (.locLit l)`) — Goose's known
  cost; correctness-neutral, and matches the interpreter. Non-addressed-local
  optimization (keep pure values off the heap) is a *later* efficiency win, not
  needed for correctness or the slice.
- **`Cont` substitution** — declarations substitute into the continuation, so
  `substLoc` must traverse `Cont` (the `seq`/`scope`/`loop`/`frame` payloads).
  Bounded and mechanical.
