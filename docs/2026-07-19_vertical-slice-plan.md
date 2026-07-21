# Vertical-slice plan — first end-to-end trust chain (2026-07-19)

Strategy (proven on ACL2Lean, adapted here): pick one well-chosen small Go
program, push it through **every** layer of the trust chain, and show the
*structure* is right at each layer — then pry the slice wider. The program is
only the witness that the layers compose; every artifact is a **general lemma**,
never specialized to the example.

## Adapting the "frontier map" to GoLean

ACL2Lean's coverage notion is *replay depth* (corpus fn → "replays nodes k/N").
GoLean has no replay; its clean coverage notion is the **differential corpus** (a
Go program passes = frontend + interpreter agree with `go run`). So the frontier
map here is a **(construct) × (trust-chain layer)** grid: the differential corpus
already gives a clean green/red for the *lower* layers per construct; the map
extends that upward through the proof layers, which have no coverage number yet.
A construct is "fully sliced" when green through all six layers. The **frontier**
is the boundary — the named layer where each construct currently stalls.

## The slice program

```go
func inc(p *int) { *p = *p + 1 }
func main() int {
    x := 0
    inc(&x)
    inc(&x)
    return x        // == 2
}
```

Chosen (over straight-line / loop alternatives) because it forces the two real
blockers the pre-merge audit found — a **usable** heap law (#23: locals in the
state interp, since `*p = …` resolves through locals) and the **frame/locals
split** (D4-12: `Config.frame` is exercised only by a call) — while staying in
the already-modeled subset (no maps/slices/interfaces/loops).

**Anti-over-specialization discipline (the win condition):** the deliverable is
the *reusable machinery*, not "the example verifies". Every layer produces a
general lemma the example merely instantiates:
- `{ p ↦ n } inc(p) { p ↦ n+1 }` — a spec of `inc` ∀ n, not "inc makes it 1".
- a general `wp_assign` over any resolved location; a general call/frame rule.
If a proof mentions the literal `2`, we specialized. If it instantiates `∀ n`,
we did not. Generality is what makes "pry wider" cheap instead of a rewrite.

## The frontier map (grounded 2026-07-19)

Layers bottom→top; per slice-construct status. ✓=green, ▲=frontier (stalls here),
· = not yet reached.

Updated 2026-07-19 after the CEK reshape (#23 done):

| construct \ layer      | L1 frontend | L2 interp+diff | L3 relation | L4 corresp. | L5 WP lemma | L6 spec |
|------------------------|:---:|:---:|:---:|:---:|:---:|:---:|
| int lit / arith        | ✓ | ✓ | ✓ | ▲ | ✓* | · |
| local decl `x := 0`    | ✓ | ✓ | ✓ | ▲ | · | · |
| assign to var          | ✓ | ✓ | ✓ | ▲ | **✓** | · |
| address-of `&x`        | ✓ | ✓ | ✓ | ▲ | · | · |
| deref-load `*p`        | ✓ | ✓ | ✓ | ▲ | ✓* (`exprR_deref_load`) | · |
| deref-store `*p = …`   | ✓ | ✓ | ✓ | ▲ | **✓** (`wp_deref_store`) | · |
| call + frame + return  | ✓ | ✓ | ✓ | ▲ | ▲ (new) | · |
| composed spec (main)   | — | ✓ | — | — | — | ▲ |

`*` = available as a supporting lemma, not a standalone WP step (arith is
big-step inside `ExprR`; deref-load is `pointsTo_loadLoc`, an ownership⟹value
lemma). **Bold ✓** = the reshape's headline: `wp_assign` is now a usable law
(`wp_assign_lit` discharges its premises), closing the audited #23 blocker.
`deref-store` L5 is now marked **unblocked** rather than #23-blocked: the camera
problem is gone for *every* assignee form (`.var` resolves via `env`; `.addr`
resolves via `ExprR env` — both fixed in the goal), so the deref-store lemma is
now just "to write," not "structurally blocked."

**Grounding of the lower rows:** L1 — `ref`/`deref`/`addr`/`field-addr`/
`index-addr` all lower in `NativeToIR.lean`; `*p = …` lowers via `.deref e →
.addr e` (assignee). L2 — `Corpus/coverage/exec/pointers/deref-assign` is a
passing differential case; the slice program is one `go run` away from a case
(first executable step: add it, confirm diff-green). L3 — `Rel.lean`'s `Step`
has `ExprR.ref`/`.deref`, `AssigneeR.addr`, `assign`, `call`, `frameReturn`.

## The two live frontiers (what the slice pushes)

- **L4 — correspondence (interp ⇄ relation).** SEVERED (audit D4-10): the
  interpreter is `partial`, so `execStmt … = .ok …` cannot be inverted and the
  correspondence is unprovable. Pushing this frontier for the slice's constructs
  requires **totalizing the exercised subset** (assign / ref / deref / call /
  frame / return over the scalar+pointer fragment) and proving the per-construct
  correspondence lemmas. Heaviest frontier.
- **L5 — WP general lemmas.** Have (all axiom-clean): `wp_seqn`; **`wp_assign`**
  (var LHS, `wp_assign_lit` discharges it) and **`wp_deref_store`** (`*p = e`,
  `.addr` LHS) — both built on the shared gen_heap core **`wp_store_step`** (which
  takes the now-*derivable* `hred`); `pointsTo_loadLoc` (read law) and
  **`exprR_deref_load`** (the `*p` expression fact). Remaining to reach the spec:
  (a) the **non-literal-rhs assembly** — compose `exprR_deref_load` + `ExprR.addInt`
  into `wp_deref_store`'s `hrhs`/`hrhs_det` for `*p + 1`, which forces (b)
  **multi-cell ownership** (`inc`'s `p` is a pointer *param*, so resolving `*p`
  reads p's own cell as well as the target — the spec owns `p_loc ↦ addr(a) ∗ a ↦
  n`), and (c) the **call/frame/return** lemma (none exists; also needs the
  results-allocation gap closed so a value-returning frame like `main` reads its
  result local). All now ordinary lemma-writing / composition, no blocked research.
- L6 — spec: compose the WP lemmas into `{p↦n} inc(p) {p↦n+1}` and `main ⊢
  result = 2` (via `∀`-general sub-lemmas). Trivial once L5 lands.

## Open scope question for this planning session

Does the **first** slice close L4 (totalize the fragment + prove correspondence),
or push L5+L6 first (usable WP + spec over the relation) and leave L4 as the
named next frontier? Closing L4 is the honest "structure connects end-to-end"
claim but is the heaviest lift; deferring it ships a slice with a still-severed
middle but both ends green + the WP layer real. **Recommendation:** push L5+L6 to
completion first (they unblock #23, the audited blocker, and yield the first
*usable* Hoare law), then push L4 as the immediately-following frontier — so the
slice is "structurally complete except the named, tracked correspondence wall,"
which we then close before widening.

## Widening plan (after the slice)

A (this: pointer + call) → **B** add a loop + invariant (while-WP, Hoare
while-rule) → **C** quorum-flavored threshold decision (array + the majority
property — first raft-shaped safety property) → … → the GoCore⇒abstract-raft
refinement + quorum invariant (D4-9, the top of the chain, still nonexistent).
Each widening adds constructs/columns to the frontier map and reuses the general
lemmas from prior slices.

## First moves — superseded 2026-07-20 by the punch list below

(Original moves 1–2 are DONE: slice cases differentially green; the CEK reshape
made `wp_assign` a usable, witnessed law. Move 3 partially done: deref-load
lemma + `wp_deref_store`+witness landed; call/frame remains.)

## Punch list to close the slice (2026-07-20 — THE work queue, in order)

Layer status: L1 frontend ✅ · L2 interp+differential ✅ · L3 relation ✅ (CEK) ·
L4 correspondence ❌ (the wall) · L5 WP laws 🟨 (~60%) · L6 spec ⬜.

1. **Close `hstore`** — discharge the open store-typing side-condition in
   `wp_assign_lit`/`wp_deref_store_ref` for a concrete cell, so a witness
   carries ZERO hypotheses (`◌ → ✓` in `proofs/Audit.lean`'s ledger). Small.
2. **End-to-end adequacy witness** — compose shipped laws into a WP for a
   concrete program, feed `go_adequacy`, get a **closed** `adequate …` theorem.
   **2a DONE (2026-07-20):** `adequate_seqn_nil` (`wp_seqn` + new `wp_seq_done`
   + `wp_value'` through `go_adequacy`/`GoCoreS`) — zero hypotheses, pure
   program; the chain composes and the conclusion is Iris-free. In the Audit
   gates. **2b (open):** a *heap-touching* witness composing `wp_assign_lit`
   needs a `go_heap_adequacy` variant that hands the initial heap's `↦`
   fragments to the WP proof (HeapLang's `heap_adequacy` shape — gen_heap init
   with fragment ownership). Do alongside item 3 or fold into arc 2's finish.
3. **Heap-reading RHS** — `*p = *p + 1`. **DONE (2026-07-20):**
   `wp_store_via_ptr` (premises conditioned on the owned cells, consuming the
   new two-cell core `wp_store_step₂`) + zero-hypothesis witness
   `wp_inc_via_ptr` (`{p ↦ addr(a) ∗ a ↦ m} *p = *p+lit {p ↦ addr(a) ∗ a ↦
   norm(m+lit)}`, ∀-general over `m`). First multi-`↦` law; in the Audit gates.
4. **Call/frame/return law** — **DONE (2026-07-20)** in five increments:
   4a `Step.call` results-allocation edit; 4b-i functions-pinned + `HeapWf`
   state interp (`docs/2026-07-20_call-law-design.md`); `wp_call_unary` (frame
   entry, fresh param cell via `genHeap_alloc`) + `wp_frame_fall` +
   **`wp_inc_call`** (the composed `{x↦m} inc(&x) {x↦m+lit}` cross-frame
   witness); `wp_frame_return` (+`_int` witness, value-returning exit);
   `wp_init`/`wp_assign_var` (+witnesses). Every construct in main()'s body
   now has its law. Remaining nuance for item 5: a nullary-arg/unary-result
   call variant for main's own entry (result cell allocated via the DeclsR
   leg — same pattern as `wp_call_unary`).
   ⚠ Note (pre-merge audit F-B): closing the gap means **editing `Step.call`**
   — a change to the trusted operational relation, not just adding a lemma. It
   must preserve the `ToVal` terminal constraint and re-clear the full
   validation gate (relation changes don't touch the interpreter, but the
   correspondence instances and every WP proof over `Step` must re-elaborate).
5. **Compose L6 — DONE (2026-07-21).** `wp_inc_call` = the `inc` spec
   (∀-general, cross-frame); `wp_main_call` (∀-general composition through
   main's whole body) and `wp_main_returns_two` (the `kind=.int, lit=1`
   instance: calling main stores `.int 2` — the literal 2 appears only in this
   final instance); **`slice_adequate`** = the closed end-to-end theorem: from
   ANY well-formed initial state containing `inc`+`main`, the full program
   `r := 0; r = main()` runs to termination never-stuck (`adequate .NotStuck`,
   zero ownership hypotheses — the program allocates its own cells), with
   `r ↦ 2` machine-checked Iris-side within the proof. **2b remainder
   (tracked):** surfacing `r = 2` *operationally* in `adequate`'s φ needs the
   strong-adequacy final-state readout (`wp_strong_adequacy_gen` plumbing) —
   the one strengthening left; the heap-touching closed `adequate` itself is
   delivered.
6. **Totalize Eval's big-step cluster → prove the correspondence** (the L4
   wall; TODO F3). Converts `interpreterSound/PanicStatement` from Props into
   theorems and joins the differential island to the proof island. Heaviest;
   after it, "differentially tested" and "proven" refer to the same artifact.

Items 1–3 and 5: ordinary lemma work, no known blockers. Item 4 embeds a
semantics edit (see its ⚠ note). Item 6: the one big lift.
Non-blocker note: BUG-001 (struct/array writes) does NOT gate this slice (no
structs in it). After the slice: widen per the ladder (§Widening) with the
concurrency-model design note (TODO F4) before any fork machinery.

### Arc shape (2026-07-20) — items batched by RISK CLASS, not adjacency

The audit boundary sits exactly where the risk boundary is: pure proof-layer
work (touches `proofs/` only — the differential is frozen by construction,
cheap audit) is batched separately from semantics edits (trusted relation
changes — everything downstream re-elaborates, focused audit).

- **Arc 1 `slice-l5-pure` — items 1+2+3** (proofs-only): zero-hypothesis
  witnesses (`hstore` closed, `◌ → ✓`), the end-to-end adequacy witness (first
  fully closed `adequate` — the first demonstrated "Iris dissolves" artifact,
  added to the Audit gates), multi-`↦` heap-reading RHS (`*p = *p + 1`).
- **Arc 2 `slice-call-frame` — items 4+5**: the `Step.call` results-allocation
  edit + call/frame/return law, with item 5 (`inc` spec + `main ⊢ 2`) composed
  in the same arc — item 5 IS the call law's discharge witness, so per the
  non-vacuity gate the law shouldn't merge without it. Slice finish line.
- **Arc 3 — item 6** solo (Eval totalization → correspondence): different
  subsystem, heaviest lift.
- F4/F5 strategy notes ride along wherever convenient (F5 pairs with arc 2's
  finish).

Each arc ends per the CLAUDE.md merge protocol (gate → audit ask → sign-off →
ff-merge → on `main`).
