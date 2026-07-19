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
| deref-load `*p`        | ✓ | ✓ | ✓ | ▲ | ✓* (read law) | · |
| deref-store `*p = …`   | ✓ | ✓ | ✓ | ▲ | ▲ (unblocked) | · |
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
- **L5 — WP general lemmas.** Have: `wp_seqn` (✓), and now **`wp_assign` — a
  usable law** (CEK reshape closed #23; `wp_assign_lit` discharges it), plus
  `pointsTo_loadLoc` (the deref-load read law). Still to write (all now
  *unblocked* — no camera obstacle remains): a **deref-store** lemma (assignee
  `.addr`, same pattern as `wp_assign` with `AssigneeR.addr`), the **non-literal
  rhs** assembly for `*p + 1` (compose `pointsTo_loadLoc` + arith into
  `hrhs`/`hrhs_det`), and the **call/frame/return** lemma (none exists; also needs
  the results-allocation gap closed so a value-returning frame like `main` reads
  its result local). These are ordinary lemma-writing now, not blocked research.
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

## First moves

1. Add the slice program as a differential corpus case; confirm L2 green (diff vs
   `go run` = 2). Grounds the bottom of the map for the exact program.
2. #23: model `ExecState.locals` (+ `Config.frame` callerLocals) in the state
   interpretation → make `wp_assign` a usable law (its `hred` dischargeable).
3. Build the missing L5 general lemmas: `wp_ref`, deref-load, deref-store,
   call/frame/return.
4. Compose L6: `inc` spec + `main` result. Then push L4 (totalize + correspond).
