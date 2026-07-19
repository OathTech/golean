# Modelling locals in the Iris state interpretation (#23) — design (2026-07-19)

The audited blocker on a *usable* `wp_assign` (findings D2-4/5/7). The state
interpretation currently owns only `σ.heap` (`genHeapInterp (heapToMap σ.heap)`),
so nothing pins how a name resolves — and `hred` quantifies `∀ σ₁` over
unconstrained `σ₁.locals`, making it unsatisfiable for any real assign. To
discharge resolution *from owned resources* the state interp must also pin
`σ.locals` (the name→`Loc` environment). New infrastructure → design + sign-off
before building (per CLAUDE.md).

## What resolution actually needs (from the slice)

- `x = e` (var LHS): `lookupLoc σ "x" = .ok loc`, i.e.
  `LocalEnv.lookup σ.locals "x" = some loc`.
- `*p = e` (deref LHS, lowers to assignee `.addr (.var "p")`): `lookup σ "p" =
  .ok (.addr target)` = `lookupLoc σ "p"` (locals) **then** `loadLoc` (heap —
  already covered by `pointsTo_loadLoc`). So the *only* new obligation is pinning
  `LocalEnv.lookup σ.locals name = some loc`.
- `inc(&x)`: `&x` = `.ref "x"` needs `lookupLoc σ "x" = .ok loc_x`; the call
  enters a fresh frame binding `p`; on return the caller env is restored.

So: (a) an ownable fact `name resolves to loc`, and (b) frame/scope discipline
(fresh env on call, restore on return; push/pop on blocks).

## The fork

### Option A — env ghost map (recommended)

Add a second gen_heap-style ghost map keyed by name: `EnvGS : genHeapGS String
Loc GF EnvF` (String has a lawful compare). State interp becomes
`genHeapInterp (heapToMap σ.heap) ∗ envInterp (resolveMap σ.locals)`, where
`resolveMap σ.locals := fun name => LocalEnv.lookup σ.locals name` projected to a
finite map (same `foldr`/first-match bridge trick as `heapToMap`). Ownership
`name ↦ₑ loc` + `genHeap_valid` ⟹ `LocalEnv.lookup σ.locals name = some loc`,
discharging resolution.

- **Pro:** reuses the gen_heap machinery + bridge-lemma pattern we already built
  and adversarially validated; makes locals **first-class ownable resources**
  (`name ↦ₑ loc`) — the reusable structure that later features (closures capture
  env, method receivers, defer) will need; **leaves `Rel.lean` untouched**, so
  the L4 correspondence frontier isn't disturbed.
- **Con:** needs scope/frame WP laws that update the env map: call enters a fresh
  env (`p ↦ₑ …`, caller env framed away), return restores it; block push/pop.
  These are new (the audit's "materially harder" part), but they are exactly the
  L5 call/frame lemmas the slice needs anyway.
- **Slice-sized subtlety:** `resolveMap` must track the *current* resolution
  (shadowing = innermost wins), mirroring `LocalEnv.lookup`'s inner→outer walk —
  again a first-match `foldr` bridge. No shadowing occurs in the slice, but the
  bridge is written general so widening is free.

### Option B — location-resolved intermediate `Config`

Reshape `Rel.lean` so resolution is its own pure step: `.exec (.assign lhs rhs)
k` → resolve `lhs`→`loc`, `rhs`→`val` → `.store loc val k`; the heap law is over
`.store` with a concrete `loc`, no locals in the state interp.

- **Pro:** heap laws become HeapLang-clean; no env camera.
- **Con:** reshapes the Config/Step (bigger); adds a resolution-step correspondence;
  **disturbs L4** (already the heaviest frontier); does not give first-class
  locals ownership (wanted for later framing).

## Recommendation: Option A

It reuses validated machinery, keeps the relation (and thus L4) stable, and
establishes locals-as-resources — the general structure the slice exists to
prove. The cost (frame/scope env laws) is L5 work we owe regardless. Option B
trades the env camera for a relation reshape that lands on the already-hardest
frontier.

## Plan under Option A (each a general lemma)

1. `EnvF`/`resolveMap` + the two bridge lemmas (`get?_resolveMap` ↔
   `LocalEnv.lookup`; `resolveMap` after `declareLocal`/push/pop), mirroring
   `heapToMap`.
2. Extend the state interp with `envInterp`; extend `GoCoreGS`/`GoCoreGpreS`/
   `GoCoreS` with the env functor; re-establish `wp_seqn`/adequacy (pure w.r.t.
   env, as with the heap).
3. Restate `wp_assign` owning `name ↦ₑ loc` (or the resolved chain for `*p`);
   `hred` becomes *derivable* — resolution from env ownership + `loadLoc` from
   heap ownership. Now a real, dischargeable Hoare law.
4. `wp_ref` (`&x`), `wp_call`/frame (fresh env in, restore out) — the slice's
   remaining L5 lemmas.
5. Instantiate for `inc`/`main` (L6), all `∀`-general.
