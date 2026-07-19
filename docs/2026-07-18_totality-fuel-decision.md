# Totality strategy for the type-directed Ops (2026-07-18)

## Context

The 2026-07 design review found that the shared substrate (`GoLean/GoCore/Ops.lean`)
and the interpreter (`Eval.lean`) were `partial def`. In Lean 4 a `partial def`
compiles to an opaque constant with **no equational lemmas**, so:

- the relation (`Rel.lean`) whose rule premises call these functions cannot have
  those premises unfolded, and
- `Correspondence.lean`'s `execStmt … = .ok …` hypotheses cannot be inverted.

Making the substrate and interpreter **total** is therefore the prerequisite for
the relation to be a real proof authority and for the eventual Iris WP rules
(`wp_load`, `wp_store`, …), which are proved by inverting the relation's
`PrimStep` premises.

## The recursion that is not structural

Most Ops recursion is structural and converts to a plain `def` directly:

- `loadLoc` / `storeLoc` recurse on the `Loc` argument (field/index bases are
  strict subterms).
- `coerceStoredValue`, `valueEq`, `normalizeValueForTy`, `defaultValue` recurse
  into array/struct **children**, which are strict subterms of the value/type —
  once the `for`-loops are rewritten as list helpers the termination checker
  sees the descent.

The one genuinely non-structural recursion is **resolving a `.defined` type name
through the type environment**: `.defined name → .alias target → recurse on
target`, and `.defined name → .struct fields → recurse on each field type`. Here
the *type* changes to something fetched from the environment (not a subterm),
while the *value* may stay the same (alias case). This terminates for any
well-formed Go program — Go type definitions cannot form value-containment cycles
— but GoCore's `TypeEnv` does not yet encode that invariant.

## Decision: fuel (chosen), not type-env acyclicity

Two ways to make the type-directed ops total:

1. **Fuel** — a `Nat` parameter decremented only at `.defined` resolution,
   returning an `unsupported "type nesting too deep"` (or a fixed point) at zero.
2. **Type-env acyclicity well-formedness** — a `WellFormedTypeEnv` predicate
   (defined-type resolution graph is acyclic) plus a decreasing measure over it,
   threaded as a proof at every call site.

**We chose fuel** (user decision, 2026-07-18), for:

- **Uniformity with `execStmt`**, which is already fuel-based, so correspondence
  lemmas thread a single fuel notion rather than mixing fuel with a
  well-formedness proof obligation.
- **Immediate totality with no new metatheory**; the acyclicity invariant is
  real up-front work and every call site would have to carry the proof.
- It is **reversible**: the acyclicity refinement can replace fuel later if the
  artifact becomes painful in proofs.

### How fuel is applied (so it stays faithful)

`typeResolutionFuel : Nat := 1024` is decremented **only** when a `.defined`
name is resolved through the environment. Array/struct/child recursion is
structural and never consumes fuel. Consequently fuel bounds **type-nesting
depth, not value size** — no valid value can spuriously exhaust it, and any
well-formed Go program stays far under 1024. Each op keeps its original public
signature via a thin wrapper (`f := fFuel typeResolutionFuel …`) over a fuel'd
worker, so call sites are unchanged and proofs about concrete types unfold the
worker with the constant.

### Cost accepted

- An artificial depth artifact: the `… too deep` branch is reachable only for
  pathological (cyclic or absurdly deep) type environments the frontend should
  never emit.
- Correspondence/WP lemmas over the type-directed ops carry a "fuel large
  enough" side condition, dischargeable for concrete types.

## Status

- `Ops.lean` is fully total (zero `partial def`) as of 2026-07-18.
- The interpreter (`Eval.lean`) is the remaining `partial` layer; the same
  fuel-and-structural approach applies (`execStmt`/`execStmts` already carry
  fuel; the expression/helper recursion and `for`-loops need the same treatment).
