# The call/frame law needs a richer state interpretation (2026-07-20)

Designing arc `slice-call-frame`'s `wp_call` surfaced two state-dependencies
that heap-cell ownership cannot pin — both would reproduce the `∀σ` vacuity
trap the audits killed twice if stated as state-independent premises:

1. **Function lookup.** `Step.call` requires `findFunctionIn? σ.functions
   funcId = some func`. `σ.functions` is in the quantified state; no `↦` owns
   it. But it is **invariant**: no `Step` rule modifies `functions` (they all
   update `heap`/`nextAddr` only). The standard Iris move for immutable global
   state: **pin it in the state interpretation** — `⌜σ.functions = prog⌝` for a
   `prog` fixed in the ghost-state class (`GoCoreGS.prog`). Laws extract the
   equality from the interp; each law's post-state preserves it definitionally.

2. **Frame allocation freshness.** `BindParamsR`/`DeclsR` allocate fresh cells
   at `σ.nextAddr`. For gen_heap allocation (`genHeap_alloc`) the key must be
   fresh — **not in the map** — but nothing in `ExecState`'s type guarantees
   heap keys sit below `nextAddr`. So the interp also carries a well-formedness
   invariant: `⌜HeapWf σ⌝` (every base key in `σ.heap` is `< σ.nextAddr`),
   preserved by every step (stores hit existing keys; allocs bump `nextAddr`).
   This is the first concrete piece of the tracked "merge invariant" work
   (TODO #15).

**New state interp:**
`stateInterp σ := genHeapInterp (heapToMap σ.heap) ∗ ⌜σ.functions = prog⌝ ∗ ⌜HeapWf σ⌝`

**Blast radius:** `GoCoreGS` gains a `prog : Array Func` field; every existing
WP law re-establishes the two pure conjuncts after its step (definitional for
heap-set steps: `functions` untouched, keys unchanged); `go_adequacy` picks
`prog := σ.functions` at allocation and gains an `HeapWf σ` hypothesis on the
initial state (honest: adequacy holds from well-formed starts — the
interpreter only ever produces such states, and the initial state of a run is
`{}`-plus-declarations, trivially wf).

**Then `wp_call` (the inc shape: one pointer param, no results, fall-through):**
premises are the pure `findFunctionIn? prog funcId = some func` (fixed
program!), conditioned arg-evaluation facts, and a continuation obligation
that receives the **freshly allocated** param cells (`∃ frameEnv pa', pa'.id ↦
⟨…, argVal⟩ ∗ …`) plus the body-WP under `.frame` — allocation surfacing as
new `↦`s is exactly gen_heap's alloc story. `frameFall` then pops via a pure
step law. `frameReturn`+`ResultsR` (for `main`'s `return x`) reads result
cells the 4a edit now allocates.

**Sequencing (4b):** (i) state-interp upgrade + re-green existing laws;
(ii) allocation bridge (`heapToMap` after `ExecState.alloc` = `insert` at a
fresh key, freshness from `HeapWf`); (iii) `wp_call` + witness (`inc(&x)`
shape); (iv) `frameFall`/`frameReturn` step laws. Item 5 then composes the
`inc` spec; 2b (`go_heap_adequacy`) rides the same allocation machinery.
