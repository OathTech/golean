# Goose / new-Perennial design mapping — steal the best, surpass the limits (2026-07-19)

Three parallel deep-reads of the actual checkouts (`../deps/perennial/{src/goose_lang,new,goose}`, `../deps/goose`), to settle the locals-modelling fork (#23) against the one system that has verified concurrent Go in Iris — the same problem class as our raft north star. All claims below were grounded to file:line by the readers; spot-check before relying.

## What Perennial actually does

**Variables & functions (`src/goose_lang/lang.v`, `new/golang/`, `goose.go`):**
- **Every Go local is a heap cell; the metalevel `let`-binder holds the LOCATION, not the value.** Reads are always `Deref`. No addressed/non-addressed optimization — the translator boxes everything (`goose.go:1046-71,1364-69`), and `&x` is just naming the binder.
- **Names are ordinary lambda binders resolved by substitution** (`lang.v:785-808`). The machine `state` is `{ heap; go_state; world }` — **no name→location environment exists** (`lang.v:626-634`).
- **Calls are `App` + substitution; no runtime frame.** Params are boxed on entry; multi-return is tuples; early `return` is a value-level labeled-pair monad, not a control effect in state (`defn/exception.v`).

**Memory & WP (`new/golang/theory/`):**
- `loc = (block, offset)`; a **type-indexed points-to `l ↦[dq] v` as a typeclass** whose *definition varies by type*: primitive = one untyped `heap_pointsto` cell; **struct = separating conjunction of per-field points-to; array = big-sep of per-element** (`postlifting.v`, `postlang.v:498-523`, `array.v:14-20`).
- **Field-granular ownership is native** — `l ↦ struct` splits into `l.[t,"f"] ↦ v_f`, independently ownable/persistable.
- WP laws are textbook-clean and sealed over an untyped `na_heap`, with an `Access` typeclass so one `wp_load`/`wp_store` fires for bare cells, field-slices, or invariant-wrapped resources (`postlifting.v:134-150`, `mem.v:82-99`).

**Trust & maturity (`goose/README.md`, `new/proof/`):**
- **Translator + semantics are explicitly trusted** — no proof of translator correctness, no differential oracle vs real `go run`; only a curated hand-maintained boolean spot-check, and the Rocq interpreter ("Waddle") isn't wired into CI.
- Per-package proofs sit on **permanently-open `Assumptions` typeclasses** never discharged against translated code.
- **Raft is their least-finished tree**: 29 of 51 `new/proof` admits live in `go_etcd_io`; `node.t`/`message.t` are bare `Axiom t : Type`; `readonly.v` was one-shot-LLM-generated with live `Admitted (* Trusted *)` and an unresolved overflow admit.
- Old→new rewrite was to *add mutation* (old Goose: "assignments are not supported, only bindings"). Floats erased to bit-patterns (arithmetic postulated); `unsafe` out of scope; channels are a hand-written reimplementation, not the runtime.

## Best ideas to STEAL

1. **No runtime name environment. Locals are heap cells; the binder holds the location; names resolve by substitution → the proof-facing state is heap-only.** This is the decisive answer to #23 (below).
2. **Type-indexed points-to that recurses on the type** — primitives = one cell, structs/arrays = sep-conj/big-sep of field/element points-to, so **field-granular ownership is free**, and load/store are type-directed folds bottoming out in primitive cells. With `loc = (block, offset)`, `l.[t,"f"]` and `l[i]` are first-class ownable addresses.
3. **Clean sealed typed-over-untyped WP laws + an `Access` accessor** so one law serves bare/field-slice/invariant-wrapped ownership.
4. **Value-level return/exception monad** for non-local control instead of a machine effect (a cheaper alternative to our CK continuations — note, don't necessarily adopt).

## Limitations to SURPASS

1. **The trust gap is the whole game.** Perennial gives Go a semantics *on faith*. **GoLean's differential gate (`go run` vs. the executable interpreter, failing-set diff per commit) is precisely the missing cross-check.** This is our core differentiator — and it is the reason to **keep a name-carrying, executable, differentially-tested interpreter** even as the proof core goes nameless.
2. **No permanent `Assumptions` axiom layer.** Our total/executable semantics can close the interpreter→relation gap by proof (the correspondence) rather than by an open axiom record.
3. **Raft is NOT a solved problem** anywhere — the closest prior art is mostly admits and opaque axioms. We inherit no free lunch; plan for the hard parts.
4. **Field-access ergonomics and float/unsafe policy** must be decided up front (their pain points: 5.8s-per-store tactics, admitted field-split instances, bit-erased floats).

## RECOMMENDATION — the locals foundation (#23)

**Reject Option A (runtime env ghost-map).** It models in separation logic exactly the structure the proven concurrent-Go system *eliminates*. A runtime variable environment is the VST tradition (sequential C); Perennial deliberately uses substitution, and its heap-only state is what makes closures/goroutines tractable. Building an env camera is diverging from the architecture that reached our north star — the divergence most likely to bite at scale.

**Adopt the Goose-aligned shape: the proof-facing relation is over RESOLVED LOCATIONS; the state interpretation stays heap-only (which we already have).** Concretely:
- Names are resolved to `Loc`s at lowering (a resolution pass / substitution), so the relation's `Step` for an assign references a concrete target `Loc`, not a `lookupLoc name` against a state env. Then `wp_assign` is over a concrete location — **no `hred`, no env camera** — exactly Perennial's `wp_store` shape. This is "Option B done right": resolution by lowering, not a runtime resolution *step*.
- **The interpreter keeps names + its `LocalEnv`** — that is the differentiator (executable, diff-tested against real Go). Its `LocalEnv` becomes the **correspondence witness**: interp name `x` ↔ relation location `env[x]`. So names live in the diff-tested layer; the proof layer is nameless; the env is the bridge, not a separation-logic resource.

Net: this is *less* separation-logic machinery than Option A (no new camera — reuses the heap-only interp we built), it is the proven foundation, and it preserves GoLean's reason to exist. The cost is reshaping the relation's variable/assignee handling from name-based to location-based — real work, but foundational and one-time.

**Heap upgrade (separate, tracked):** adopt the type-indexed / field-flattened points-to (`loc=block/offset`, `l.[t,"f"]`) when structs enter the proof frontier. Not needed for the pointer+call slice (scalar cells), but it is the right heap for raft's structs — our current whole-struct-at-one-cell `Loc` is coarser.

## Implication for the slice + next step

Under this recommendation the pointer+call slice's L5 becomes: a location-based `wp_assign`/`wp_deref-store`/`wp_ref`/`wp_call` in Perennial's clean shape, over a relation whose variable handling is resolved. The immediate design question shifts from "how to model locals in the logic" to **"where does name→Loc resolution happen — a lowering pass into a location-based relation IR, or substitution in the Config"** — a smaller, better-posed question than the env-camera build. That is the next thing to design before writing L5.
