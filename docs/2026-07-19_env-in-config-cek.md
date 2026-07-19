# Locals as an environment in the Config (CEK) — supersedes eager substitution (2026-07-19)

Designing `substLoc`'s scope handling (`docs/2026-07-19_reshape-mechanics-design.md`
proposed eager substitution) revealed that substitution **fights GoLean's machine
structure**. This note reverses that lean toward an **explicit environment carried
in the Config** — the CEK-machine representation — and explains why it is both
the idiomatic and the less-bug-prone choice, while still fixing the audit.

## Why substitution fights the CK machine

Two structural frictions, not incidental:

1. **Inline mid-sequence declarations.** `x := 0` lowers to `initialization x;
   assign …` as separate statements. `x`'s scope is "the rest of the current
   sequence," which lives in the continuation `k` (`.seq rest k`). Per-declaration
   substitution must therefore reach *into* `k`, or special-case the sequence
   advance — the substitution's extent is entangled with the continuation.
2. **Scope extent.** A name's scope ends at *its* `.scope` in `k`, but `k` can
   nest several `.scope`s; substitution has to know which one, which the term
   structure doesn't tell it locally.

These are exactly the puzzles an explicit environment removes.

## The resolution: environment in the Config (CEK)

The relation is an **abstract machine** (Control = `Config`, Kontinuation =
`Cont`). Its natural handling of variables is an **environment**, not
substitution — that is the textbook **CEK machine**. Substitution is the natural
choice for a *lambda calculus* (which is why Goose/GooseLang substitutes); an
environment is the natural choice for *us*. Adopting it:

- **The `Config` carries the current frame's environment** `env : LocalEnv`
  (name→`Loc`, the scope stack we already have). Declaration **extends** `env`;
  `.scope`/frame exit **restores** it — reusing the push/pop logic that is
  already correct today (it just moves from `ExecState.locals` to the `Config`).
- **`ExprR`/`AssigneeR` resolve `.var`/`.ref` against the `Config`'s `env`**,
  threaded in (mechanical: only `var`/`ref` read it; every other rule passes it
  through untouched).
- Inline `x := 0` is now trivial — the declaration step just prepends `(x, loc)`
  to `env`; no reaching into `k`, no scope-extent puzzle. The environment *is* the
  scope.

## Why it still fixes the audit (and is NOT the rejected Option A)

The audit's defect: `wp_assign`'s `hred` was unsatisfiable because
`ExecState.locals` lives in the **state** `σ`, which the WP quantifies and the
state interpretation cannot pin.

- **Option A (rejected)** put a camera on `σ.locals` — modelling a *state* env in
  separation logic.
- **This (CEK)** puts `env` in the **`Config`** — the Iris *expression*, which is
  **fixed in the WP goal, not quantified**. Resolution `env[x] = some loc` is a
  pure fact about the fixed `Config`, discharged with no camera and no `∀σ`. So
  `wp_assign` gets a trivially-dischargeable `⌜env[x] = some loc⌝` premise instead
  of the unsatisfiable `hred` — exactly the spike's resolved `wp_store`, with the
  `Loc` read from the Config's `env`. **State interp stays heap-only.**

Env in *control* ≠ env in *state*. Only the latter needs a camera.

## Mechanics & loose ends

- **`Config`** gains `env` on the executing configurations; the terminal
  `.next .stop` carries a canonical empty `env` so `ToVal`'s round-trip is
  unaffected (resolution is irrelevant at termination).
- **`Cont.frame`** already restores `callerLocals`; under CEK the caller's `env`
  is restored from the frame on return, and a call installs the callee's fresh
  `env` (params) — the same discipline, relocated.
- **`Expr.locLit` (step 1) becomes vestigial.** Under CEK we don't rewrite
  `var`→`locLit`; `.var x` resolves via `env`. `locLit` is a harmless, valid node
  (its `ExprR` rule is sound) — keep it for now (address-of-computed-location may
  want it later), remove if it stays unused. Honest flag: step 1 committed a node
  this approach doesn't strictly need.
- **Correspondence** is *cleaner*, not harder: interp keeps `ExecState.locals`,
  relation keeps `Config.env`; they are the same structure, so the bridge is
  `σ.locals ≈ Config.env` (an equality, not a substitution-vs-names relation).

## Recommendation

Adopt **environment-in-Config (CEK)**, superseding eager substitution. It removes
the substitution/scope-extent bug surface, is the idiomatic representation for our
abstract machine, reuses the existing scope discipline, keeps the state
heap-only, and fixes `hred` — all the wins of the location-resolved plan, with
less new machinery. The reshape becomes **"relocate `locals` from `ExecState` to
`Config`,"** plus threading `env` through `ExprR`/`AssigneeR`.

Because this reverses a documented decision, it is a sign-off point before
building.
