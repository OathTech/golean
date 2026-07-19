# A2 step 3 design — WP laws over the real GoCore relation (2026-07-18)

Where A2 stands: the bare `Language` is instantiated on the real
`Config`/`ExecState` (`proofs/GoLeanProofs.lean`, committed, builds). Step 3 adds
`IrisGS_gen` + a state interpretation, then proves WP laws. Two sub-milestones,
cheap-first:

## 3a. Pure control WP (no gen_heap) — the cheap real-WP milestone

Proves a WP law over GoCore's actual `Step` without any heap reasoning, so it
needs only the invariant + later-credit cameras (not the heap functors).

- **GF**: a `BundledGFunctors` with functors 0–3 of HeapLang's `HeapLangS`
  (`InvMapF`, `DisjointLeibnizSet CoPset`, `DisjointLeibnizSet PosSet`,
  `Auth.AuthURF Credit`) — the invariant + credit machinery WP/fupd require.
  Drop HeapLang's functors 4–6 (the heap `HeapView`/`MetaUR`). Mirror the
  `InvGpreS` + `LcGpreS` instances (no `heap_pre`).
- **StateInterp**: `stateInterp _ _ _ _ := iprop(True)` (nothing to interpret
  without a heap).
- **IrisGS_gen**: `numLatersPerStep _ := 0`, `forkPost _ := True`,
  `stateInterp_mono` trivial. `ExecState` is `Inhabited` (structure defaults),
  satisfying `wp_lift_pure_det_step_no_fork`'s `[Inhabited State]`.
- **The law**: e.g. `wp_seqn : WP (.exec (.seqn ss) k) {{Φ}} ⊣ WP (.next (.seq
  ss.toList k)) {{Φ}}` via `wp_lift_pure_det_step_no_fork`. `Step`'s `seqn` rule
  is deterministic (unique successor, state unchanged) — discharge `Hsafe`
  (reducible: witness the `seqn` step) and `Hpuredet` (invert `Step`: only `seqn`
  applies to `.exec (.seqn ss) k`; `cases` the step). Good candidates: `seqn`,
  `seqDone`, `ifTrue/ifFalse` (need the `ExprR` cond premise — pick `boolLit`),
  `returnStmt`, `loopBreak`.

This is the "real WP over the real relation" validation, deferring heap plumbing.

## 3b. Heap WP (`wp_store`/`wp_load`) — needs the gen_heap bundle

The real payoff: a heap law over `Step.assign`/`deref`. Requires instantiating
the gen_heap library (`Iris.BI.Lib.GenHeap`) for GoCore's heap:

- **Key/value**: `Loc` → `HeapCell` (heap cells are keyed by `.base` locs).
  `Loc` has `DecidableEq`; gen_heap's map (`Std.ExtTreeMap`) additionally needs
  **`Ord Loc`** (derive it; `Loc` = `base`/`field`/`index` over
  `Addr`/`TypeId`/`String`/`Int`, all orderable).
- **Map functor**: `fun V => Std.ExtTreeMap Loc V compare` (GoCore's `HeapF`),
  plus the `HeapView Loc (Agree (LeibnizO HeapCell)) HeapF` functor added to the
  GF (extend 3a's GF with HeapLang's functors 4–6 analogues).
- **StateInterp**: `stateInterp σ _ _ _ := genHeapInterp (σ.heap.toExtTreeMap)`
  — convert GoCore's `Heap` (`List (Loc × HeapCell)`) to the map **inside** the
  interpretation, so `ExecState`/`Ops`/interpreter stay untouched (no heap
  representation change, differential suite safe). The conversion must be a
  faithful function `List (Loc × HeapCell) → ExtTreeMap Loc HeapCell` (last-write
  or dedup-consistent with `Heap.set`/`Heap.lookup`).
- **The laws**: mirror the spike's `wp_store` (`../iris-spike/Spike.lean`) but
  over `Step.assign` (uses `AssigneeR`/`ExprR`/`storeLoc` premises) — invert the
  assign rule, relate `pointsTo l cell` to `Heap.lookup σ.heap l` via the
  conversion + `genHeap_valid`, update via `genHeap_update`. `wp_load` over
  `deref` similarly with `loadLoc`.
- **Adequacy**: mirror HeapLang's `heap_adequacy` (allocate the heap ghost state
  from `σ.heap`), targeting `adequate .NotStuck` (decision D1).

## 3b findings from the initial probe (2026-07-19)

Concrete facts established before 3b's full implementation, to start it efficiently:

- **Key gen_heap by `GoLean.Addr`, not `Loc`.** Heap cells live only at
  `.base addr` locs, and `Addr` is `structure Addr where id : Nat` — a trivial
  lawful `Ord` (`compare a.id b.id`), avoiding a lawful compare for the recursive
  `Loc`. Namespace gotcha: the value types (`Addr`, `Loc`, `GoValue`) are in
  namespace **`GoLean`** (not `GoLean.GoCore`) — `Value.lean` closes `GoCore`
  before defining them. So it's `GoLean.Addr`.
- **The `genHeapGS`/`genHeapPreS` classes** (`Iris.BI.Lib.GenHeap`): a
  `genHeapGS L V GF H` needs `[Std.LawfulFiniteMap H L]` and bundles
  `GhostMapG`/`ElemG` functors + `heapName`/`metaName`. For a WP *lemma* you
  **assume** a `GoCoreGS` class (extends `InvGS_gen` + `genHeapGS Addr HeapCell
  GF GoHeapF`), exactly as HeapLang's laws assume `[HeapLangGS]`; no functor
  construction (that is adequacy, 3b-final).
- **RESOLVED — the path is confirmed (2026-07-19 probe).** The "vendored-Std
  friction" was a name-resolution mistake, not a missing instance. The class is
  **`Iris.Std.LawfulFiniteMap`** (iris-lean's own `Iris.Std`, seen as `Std`
  inside iris via `open Iris`), and it **infers out of the box** for a
  `Nat`-keyed map:
  ```
  import Std.Data.ExtTreeMap Iris.Std.PartialMap Iris.Std.FromMathlib
         Iris.Std.GenSetsInstances Iris.BI.Lib.GenHeap
  example : Iris.Std.LawfulFiniteMap (fun V => Std.ExtTreeMap Nat V compare) Nat
      := inferInstance   -- ✓
  ```
  So **key gen_heap by `Nat`** (the `addr.id`), not `Addr`/`Loc` — `Nat` already
  has `TransCmp`/`LawfulEqCmp`/`DecidableEq`, which are exactly what
  `GenSetsInstances` + gen_heap need. `GoHeapF := fun V => Std.ExtTreeMap Nat V
  compare`; `convert : Heap → ExtTreeMap Nat HeapCell` folds `.base ⟨n⟩ ↦ cell`.
  No unproven Iris capability remains — the whole of 3b now has a working
  template (spike for `wp_store`/adequacy, HeapLang for the camera).
- **`GoHeapF := fun V => Std.ExtTreeMap GoLean.Addr V compare`**; `StateInterp σ
  := genHeapInterp (convert σ.heap)` with `convert : List (Loc × HeapCell) →
  ExtTreeMap Addr HeapCell` folding `.base addr ↦ cell` (ignore non-`.base`,
  there are none). Relate `Heap.lookup σ.heap (.base a) = some cell` ↔
  `(convert σ.heap).get? a = some cell` as the bridge lemma for `wp_store`.
- **`wp_store` is at STATEMENT granularity** (reviewer B3): there is no atomic
  heap `Step`; the atomic step is `Step.assign`, which evaluates `AssigneeR`/
  `ExprR` (pure, read-only in the scalar subset) then `storeLoc`. So the law is
  `wp_assign` over `Step.assign`, mirroring the spike's `wp_store` proof
  (`wp_lift_atomic_step` + `genHeap_valid`/`genHeap_update`) but inverting the
  assign rule and threading the pure assignee/expr premises. Rocq Iris is the
  reference if iris-lean lacks a needed gen_heap lemma.
- **When to swap 3a's placeholder:** replace the trivial `StateInterp`/`IrisGS`
  (under `[InvGS_gen]`) with the gen_heap ones (under `[GoCoreGS]`) and move
  `wp_seqn` under `[GoCoreGS]` — its pure proof still holds; this avoids two
  conflicting `StateInterp ExecState Unit GF` instances.

## 3b.2 result — `wp_assign` proved (2026-07-19)

`wp_assign` lands: the first heap Hoare law over GoCore's real `Step.assign`,
axiom-clean (`propext`/`Classical.choice`/`Quot.sound`, no sorry). What was
learned vs. the plan above:

- **The heap-key-uniqueness invariant is NOT needed** (the subtlety flagged for
  the crux lemma dissolved). Defining `heapToMap` as a **`foldr`** — the list
  head is inserted *last*, so it wins a key clash — makes the projection match
  `Heap.lookup`'s front-to-back first-match *unconditionally*. Both skip
  non-`base` locs identically. So the two bridge lemmas hold for *any* heap, no
  well-formedness hypothesis:
  - `get?_heapToMap : get? (heapToMap h) k = Heap.lookup h (.base ⟨k⟩)` (read
    bridge — turns `genHeap_valid`'s map fact into the assoc-list lookup
    `storeLoc`/`loadLoc` consume).
  - `heapToMap_set_base : heapToMap (Heap.set h (.base a) c) ≡ₘ insert (heapToMap
    h) a.id c` (write bridge — lets `genHeap_update` service `storeLoc`). Proved
    via the read bridge, reducing to a pure `Heap.set`/`Heap.lookup` fact.
  These are small structural inductions; the `≡ₘ` (pointwise `get?`) target +
  `genHeapInterp_eqv` avoid any strict map-equality reasoning.
- **`wp_lift_step`, not `wp_lift_atomic_step`.** The spike's store reduced to a
  *value* (`()`), so atomic lifting applied. GoCore's assign reduces to `.next
  k`, a **non-value** control config, so the general `wp_lift_step` is required,
  and the law is **continuation-passing**: `a.id ↦ old ∗ (a.id ↦ new -∗ WP
  (.next k) @ s;E {{Φ}}) ⊢ WP (.exec (.assign lhs rhs) k) @ s;E {{Φ}}`. This is
  the right shape for a statement-level law in a CK machine — you thread the
  caller's continuation WP (which `wp_lift_step` hands back as `WP e₂`), instead
  of applying `Φ` to a produced value. `wp_load` will mirror it.
- **The locals gap (the real remaining work).** `Step.assign` bundles
  `AssigneeR`/`ExprR`/`storeLoc`, and resolving `lhs`/`rhs` to a location + value
  reads `ExecState.locals`, which the state interpretation does **not** model
  (gen_heap owns only `σ.heap`). So the law takes an operational side condition
  `hred` as a hypothesis: "at a state whose target base cell holds `oldcell`, the
  assign steps deterministically to `.next k` writing `newcell` into that one
  cell." The heap-camera core — valid/update/bridge — is fully proven; `hred` is
  discharged per-call from concrete `lhs`/`rhs`. Deriving `hred` in general needs
  **locals modelled in the state interpretation** (or an intermediate
  location-resolved Config, HeapLang-style). That is the next structural step —
  likely folded into Reshape B, since it also touches `ExecState`'s shape.
- **Next:** `wp_load` over `deref` (read-only: `loadLoc` + read bridge +
  `genHeap_valid`, no update), then adequacy (`heap_adequacy` analogue:
  `genHeap_init` from `σ.heap`, `adequate .NotStuck`).

## Notes

- The proof file stays **legacy** (imports golean-legacy + iris-module); the
  probe confirmed iris's `iprop`/proof-mode/`WP` machinery works from legacy, so
  no module migration is needed (backlogged).
- Keep 3a and 3b in files under the `GoLeanProofs` lib so the committed bare-
  `Language` milestone isn't disturbed if a proof is mid-flight.
- The heaviest risk is the gen_heap camera bundling (dense, ~50 lines mirrored
  from HeapLang) and the List→map conversion lemmas; 3a sidesteps all of it and
  should land first.
