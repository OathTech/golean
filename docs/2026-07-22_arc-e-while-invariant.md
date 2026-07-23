# Arc E rung B: the while-invariant WP law (2026-07-22)

Design note for the first rung of the widening ladder
(`docs/2026-07-19_vertical-slice-plan.md` §Widening: A pointer+call →
**B loop+invariant** → C quorum threshold). Written before code.

## 0. Scoping — what already exists (verified 2026-07-22)

Much better than TODO implied; rung B is **proofs-only** (cheap risk class):

- **Interpreter**: `.while` fully implemented (`Eval.lean:834+`,
  fuel-decreasing back edge — one of the two designed back-edges).
- **Relation**: complete rule set (`Rel.lean:448-465`): `whileTrue/False`
  (cond via `ExprR`, state-threaded), `whilePanic`, and the `.loop c b env k`
  continuation with `loopNext` (back edge), `loopContinue`, `loopBreak`,
  `loopReturn`.
- **Correspondence**: `StmtFragNS.whileStmt` EXISTS and
  `execStmt_frag_sound` already handles the while case — while programs are
  already inside `interpreterSound_frag`. `StmtFragNS` also covers
  `ifThenElse`/`break`/`continue` — the frontier is `ExprFrag`, not
  statements.
- **Corpus**: `control-flow/` pins loops (for-condition-eval,
  for-break-skips-post, infinite-loop-return, goto-loop, …); `quorum/`
  already has slice-C-shaped cases (committed-index, vote-result).
- **Iris**: Löb is available and idiomatic (`iloeb` tactic, used twice
  inside iris-lean's own WP proofs; `BILoeb`/`loeb` in DerivedLawsLater).

**The one hard scope boundary:** `ExprR`/`ExprFrag` have `eqCmp` (equality)
but NO ordering comparison (`lt`/`le`). So a `while x < 3` loop cannot be
stated over the trusted relation today.

## 1. Rung sequencing (risk classes, per the 2026-07-20 arc-shape doctrine)

- **B1 (proofs-only, this rung):** the general while-invariant law + a
  read-step lifting core + an eq-conditioned witness + surface discharge.
  Differential frozen by construction.
- **B2 (semantics edit, own commit, focused differential):** add `ltCmp`
  to `ExprR` + `ExprFrag` + interpreter-correspondence case
  (`evalExpr_frag_ok`) + corpus guardrail cases FIRST (guardrails-first);
  then the multi-iteration witness `x := 0; while x < 3 { x = x + 1 }` ⇒
  `{x ↦ 0} … {x ↦ 3}` — the proper quantified-testcase loop spec. The
  quorum rung (C) needs `lt`/`>` anyway (majority threshold).
- Honesty constraint for B1: the eq-conditioned witness executes exactly
  ONE iteration (with only `eqCmp`, any terminating loop's cond flips after
  one body run). It still exercises the full Löb cycle — true branch, body,
  back edge, IH application, false branch, exit — but the docstring must
  say "single-iteration witness; multi-iteration arrives with B2", never
  imply more.

## 2. The law (B1 design)

House style: continuation-passing, premises conditioned on owned cells
(the CEK dividend — env is in the goal, only the heap is quantified).

New lifting core `wp_read_step` (Lifting.lean): a deterministic,
heap-READING, non-mutating step — from config `c₀`, owning `a.id ↦ cell`,
`Step c₀ σ₁ c₁ σ₁` deterministically (state unchanged). Shape mirrors
`wp_store_step` minus the ghost update. Needed because the while-cond step
reads the cell but writes nothing (neither `wp_lift_pure_det_step_no_fork`
— not pure, needs the cell — nor `wp_store_step` — no write — fits).

The rule (sketch; exact premises to be settled at proof time):

```
theorem wp_while_cell {a : Addr} {c b env k}
    {Inv : HeapCell → Prop} {dec : HeapCell → Bool}
    -- cond evaluates, deterministically, to dec(cell), for any Inv-cell:
    (hcond : ∀ σ₁ cell, Inv cell →
      Heap.lookup σ₁.heap (.base a) = some cell →
      ExprR env σ₁ c (.value (.bool (dec cell)) σ₁)
      ∧ ∀ out, ExprR env σ₁ c out → out = .value (.bool (dec cell)) σ₁)
    -- one body iteration: from an Inv-cell with dec true, re-establish
    -- some Inv-cell at the loop continuation (continuation-passing):
    (Hbody : ∀ cell, Inv cell → dec cell = true →
      iprop(a.id ↦ cell
        ∗ ((∃ cell', ⌜Inv cell'⌝ ∗ a.id ↦ cell')
            -∗ WP (Config.next (.loop c b env k)) @ s ; E {{ Φ }}))
        ⊢ WP (Config.exec b env (.loop c b env k)) @ s ; E {{ Φ }}) :
    iprop((∃ cell₀, ⌜Inv cell₀⌝ ∗ a.id ↦ cell₀)
      ∗ ((∃ cell, ⌜Inv cell ∧ dec cell = false⌝ ∗ a.id ↦ cell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }}
```

Proof plan: `iloeb as IH` (Löb over the whole entailment, generalizing the
current cell). Unfold one cond step via `wp_read_step`:
- `dec cell = false` → `whileFalse` step to `.next k` → exit continuation.
- `dec cell = true` → `whileTrue` step to `.exec b env (.loop …)` → apply
  `Hbody`; its continuation holds the re-established `∃ cell'` and must
  show `WP (.next (.loop …))` — one pure det step (`loopNext`, via
  `wp_lift_pure_det_step_no_fork` like `wp_seq_next`) back to the while
  config, whose later strips `▷ IH`; apply IH with `cell'`.
- `whilePanic` is excluded by `hcond` determinism (the det clause forces
  the panic rule's `ExprR … (.panic msg)` premise into a `.value` shape —
  same inversion pattern as `wp_assign`'s `assignValuePanic` case).

Body scope (v1): the body premise speaks only of normal completion
(`.next (.loop …)`). `break`/`continue`/`return` inside the body reach
`.breaking/.continuing/.returning (.loop …)` configs; the loop-side rules
exist (`loopBreak/Continue/Return`) and small WP laws for them are cheap
to add when a witness needs them — NOT in B1's witness, so not in B1
(fail-closed: an unprovable WP, not a wrong law).

Partial correctness throughout — an infinite loop satisfies any while
triple vacuously at the triple layer; `Progress`/`GoSpec` still hold
(never-stuck ≠ terminating), and that is the honest reading. Termination
metrics are explicitly out of scope for the ladder until liveness (F5
tier 2).

## 3. B1 witness + surface discharge

Witness program (fragment-legal today):
`x := 0; while (x == 0) { x = x + 1 }` — `Inv cell := cell int-typed with
value ∈ {0, 1}`, `dec := (value == 0)`. Law instance
`wp_while_eq_once`-style: `{x ↦ 0} … {x ↦ 1}`, zero unresolved premises
(cond via `ExprR.var` + `eqCmp`; needs `var`/`eqCmp` determinism
inversion lemmas in `Inversions.lean` if not present). Surface: a
`GoSpec` discharge through the existing exit pipe (statement in
Surface.lean stated FIRST, per the widening loop), demonstrating the
while law composes with `goSpec_of_wp` unchanged — the anti-hack check
for this rung.

## 4. Order of work (B1)

1. Corpus guardrail: confirm/add the exact witness-shaped case
   (eq-conditioned single-iteration while, result observed); differential
   green before any law work.
2. `wp_read_step` core (Lifting.lean).
3. Determinism inversion lemmas for `var`/`eqCmp` conditions
   (Inversions.lean) as needed.
4. `wp_while_cell` (new `Laws/Loop.lean`) — Löb proof.
5. Witness (same file, same commit — non-vacuity gate).
6. Surface statement + discharge; Audit ledger; gate.
Then B2 (the `ltCmp` semantics commit) as a separate gate-validated slice.
