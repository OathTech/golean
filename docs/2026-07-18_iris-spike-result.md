# Iris spike result — VALIDATE (2026-07-18)

The throwaway Iris vertical-slice spike (master plan §8 step 1) came back
**validate, not kill**. The plan's Iris endgame seats on the relation shape we
are committing to. Spike lives at `../iris-spike/` (sibling to `golean/` and
`deps/`; a standalone Lake project pinned to Lean 4.31.0 requiring
`deps/iris-lean/Iris`). It is NOT part of the golean build (which is 4.29.1) —
it is a self-contained evidence artifact and a template for Reshape A.

## What was validated

1. **Toolchain (biggest unknown) — clears.** `lake build` provisioned Lean
   4.31.0 + iris-lean's pinned Qq/batteries and built all of iris-lean +
   HeapLang + its WP/adequacy tests + the spike, **offline** after one `lake
   update`. So the v4.29→v4.31 gap is a real but mechanical integration step
   (bump the golean toolchain when iris lands), not an architectural risk.

2. **A CK machine seats on bare `Language` — no ectx.** Instantiated iris-lean's
   `ToVal` + `PrimStep` + `Language` + `IrisGS_gen` for a minimal
   continuation-style expression (`CExpr` = terminal value | atomic store) whose
   step relation `CStep` is given **directly** (no evaluation contexts, no
   `EctxLanguage`). Compiles. This is the empirical confirmation of the iris
   reviewer's conclusion: *"not an ectx redesign — instantiate `Language`
   directly."* GoCore's `Config`/`Cont` CK machine is a valid Iris `Expr` shape.

3. **A heap-touching `wp_store` is provable over the direct step relation.**
   Proved `wp_store_ck` via `wp_lift_atomic_step` on `CStep` — **no
   ectx/baseStep bridge** (that indirection, which HeapLang carries, simply
   vanishes for a bare-`Language` CK machine, so the proof is *shorter* than
   HeapLang's). Reused HeapLang's language-independent gen_heap
   (`pointsTo`, `genHeap_valid`, `genHeap_update`) for the state interpretation.
   `#print axioms IrisSpike.wp_store_ck` → `[propext, Classical.choice,
   Quot.sound]` only — a real proof, no `sorryAx`.

4. **D1 (not-stuck adequacy) is directly supported.** iris-lean's `adequate`
   takes a `Stuckness`; `adequate .NotStuck` is what HeapLang's `heap_adequacy`
   produces. The progress/safety adequacy the plan committed to is the library's
   native form, not something we must bolt on.

## What this does and does not prove

- **Does:** the four load-bearing "does the Iris layer even work on our shape"
  questions — toolchain, bare-`Language` CK embedding, heap WP via lifting,
  not-stuck adequacy availability — are all answered yes. The reviewers' worry
  that `Config`/`Cont` might force an ectx rewrite is retired.
- **Does not:** it is a *toy* (one store op, HeapLang's heap reused). It does
  not exercise GoCore's real `Config`/`Cont`, the oracle/nondeterminism, or a
  full adequacy proof for a custom language. Those are the reshapes below —
  but the spike shows the *target shape* they aim at is sound.

## Confirms the reshapes are the right next work

The spike kept state (`State` = heap) **separate** from the expression — exactly
Reshape A (heap out of `Config`/`ExecState` into Iris `State`), because `ToVal`'s
round-trip law forbids `Expr` embedding the heap. And it has no oracle — Reshape
B (oracle out of `ExecState`, existential `mapRange` rule) is what lets the real
nondeterministic relation take this shape. The spike is the concrete target both
reshapes port GoCore toward.

## Gotcha recorded (for the port)

The failing symptom for many iterations was `unexpected token 'WP'; expected
command`. Cause: a `section WP` / `end WP` — once iris-lean's `WP` term notation
is imported, `WP` is a reserved token and cannot name a section. Rename the
section. (Not an import or statement-form problem, which is where time went.)
Also: importing `Iris.BI` / `Iris.Instances` alongside the HeapLang chain was
unnecessary; the minimal working import set is `Iris.HeapLang.{Notation,
ProofMode,Instances,PrimitiveLaws}` + `Iris.ProgramLogic.{WeakestPre,Adequacy}`.

## Next

Per master plan §8: proceed to **Reshape A** (heap out of `Config` into Iris
`State`) on the real scalar relation, then port this `wp_store` onto real
GoCore. The spike is the reference. The v4.29→v4.31 bump is scheduled with that
integration, not before.
