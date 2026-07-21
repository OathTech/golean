import GoLeanProofs
import GoLean.GoCore.Correspondence

/-!
# In-build epistemic gate for the Iris proof layer

This file is a **machine-checked, re-runnable** guard on the proof layer's
claims. It builds as part of `lake build` (a default target), so an edit that
weakens the epistemic position **fails the build** rather than silently shipping.
It defends against both error kinds:

- **Commission** (claiming something false): the axiom gates below use
  `#guard_msgs in #print axioms` — if any listed theorem ever acquires an axiom
  beyond its recorded set (a `sorryAx` from a `sorry`, `ofReduceBool` from
  `native_decide`, or a new hand-rolled `axiom`), the generated message stops
  matching the docstring and the build errors. Type-checking alone is *not*
  enough — Lean's kernel accepts `sorryAx` — so we assert the exact axiom set,
  not mere elaboration (mechanism from ACL2Lean's axiom audit,
  `docs/2026-07-19_directional-audit-findings.md` follow-up).

- **Omission / vacuity** (a true-but-unusable law): every user-facing WP/Hoare
  law must have a **discharge witness** — a theorem instantiating it on a
  concrete program and discharging its premises. This file *references* each
  witness, so deleting a witness (or a law) breaks this build. This is the
  standing defense the `wp_assign`-hred and `wp_deref_store` vacuity bugs each
  slipped past when the check was a one-off manual audit (CLAUDE.md non-vacuity
  gate).

Three-state honesty (ACL2Lean `✓ / ◌ / ✗`): `✓` = axiom-clean **and** witnessed;
`◌` = axiom-clean but not yet instantiated end-to-end (a real, tracked gap, not a
green claim); `✗` would be a hole (must never appear — the build forbids it).

To re-baseline after an *intended* change: run `#print axioms <name>` and update
the matching docstring here in the same commit, with the reason.
-/

open GoLean.Iris

namespace GoLean.Iris.Audit

/-! ## Exhaustive axiom sweep — every declaration, not a hand-maintained list

The curated `#guard_msgs` gates below pin the *exact* axiom set of the key
theorems. But a curated list is only as good as the hand maintaining it: a NEW
theorem (public or private) added anywhere in our code would dodge it. This
sweep closes that: it walks **every** constant declared in any module whose
name starts with `GoLean` (`GoLean.*`, `GoLeanProofs`) or in the current file —
**by module of origin, not by namespace**, so a declaration in an unexpected or
top-level namespace is still swept (pre-merge tamper audit 2026-07-20, finding
F1: the earlier namespace-prefix filter let a top-level `sorry` theorem in the
built proofs file pass). It collects each constant's transitive axioms and
**fails the build** if any depends on one outside the classical trio
`{propext, Classical.choice, Quot.sound}` — which is exactly how a `sorry`
(`sorryAx`) or `native_decide` (`ofReduceBool`) would surface. Coverage is by
construction within the built import closure; a brand-new proofs file must be
imported to be built at all, which `scripts/ci`'s proofs-file check enforces
separately (finding F2). -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- Target = our modules (by module-name root string, catching GoLean.* and
  -- GoLeanProofs) plus anything declared in the file being elaborated
  -- (no module index yet).
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot.toString.startsWith "GoLean")
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut bad : Array (Name × Name) := #[]
  let mut audited := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true
    unless ours do continue
    let axs ← collectAxioms n
    audited := audited + 1
    for ax in axs do
      unless allowed.contains ax do
        bad := bad.push (n, ax)
  if bad.isEmpty then
    IO.println s!"audit sweep: {audited} declarations across all GoLean* modules, all axiom-clean"
  else
    let lines := bad.qsort (fun a b => a.1.toString < b.1.toString)
      |>.map (fun (n, ax) => s!"  {n} depends on {ax}")
    throwError "audit sweep FAILED — declarations with disallowed axioms \
      (a `sorry`, `native_decide`, or new postulate?):\n{String.intercalate "\n" lines.toList}"

/-! ## Axiom gates — the recorded axiom set of every proof-facing declaration.
    A change to any set fails the build until this file is deliberately updated. -/

-- Heap projection bridges (read/write faithfulness of `heapToMap`).
/-- info: 'GoLean.Iris.get?_heapToMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms get?_heapToMap
/-- info: 'GoLean.Iris.heapToMap_set_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms heapToMap_set_base

-- Read law + its operational half.
/-- info: 'GoLean.Iris.loadLoc_base_of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms loadLoc_base_of_lookup
/-- info: 'GoLean.Iris.pointsTo_loadLoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pointsTo_loadLoc
/-- info: 'GoLean.Iris.exprR_deref_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exprR_deref_load

-- WP laws.
/-- info: 'GoLean.Iris.wp_seqn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_seqn
/-- info: 'GoLean.Iris.wp_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_assign
/-- info: 'GoLean.Iris.wp_deref_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_deref_store

-- Discharge witnesses (the non-vacuity evidence).
/-- info: 'GoLean.Iris.wp_assign_lit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_assign_lit
/-- info: 'GoLean.Iris.wp_deref_store_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_deref_store_ref

-- Adequacy (the top of the WP layer).
/-- info: 'GoLean.Iris.go_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms go_adequacy

-- The store side-condition facts behind the zero-hypothesis witnesses.
/-- info: 'GoLean.Iris.intKind_normalize_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intKind_normalize_idem
/-- info: 'GoLean.Iris.storeLoc_int_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms storeLoc_int_cell

-- The read-through pointer store (arc slice-l5-pure item 3): the first
-- multi-points-to law, premises conditioned on the owned cells.
/-- info: 'GoLean.Iris.wp_store_via_ptr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_store_via_ptr
/-- info: 'GoLean.Iris.wp_inc_via_ptr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_inc_via_ptr

-- The call law (arc slice-call-frame item 4b): frame entry with fresh-cell
-- handover, resolved against the state-interp-pinned program; the frame-pop
-- step law; and the composed cross-frame witness.
/-- info: 'GoLean.Iris.wp_call_unary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_call_unary
/-- info: 'GoLean.Iris.wp_frame_fall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_frame_fall
/-- info: 'GoLean.Iris.wp_inc_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_inc_call

-- The value-returning frame exit + the remaining pure control-step laws
-- (arc slice-call-frame, toward item 5's main composition).
/-- info: 'GoLean.Iris.wp_frame_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_frame_return
/-- info: 'GoLean.Iris.wp_frame_return_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_frame_return_int
/-- info: 'GoLean.Iris.wp_seq_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_seq_next
/-- info: 'GoLean.Iris.wp_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_return

-- Declaration + var-copy laws (the last per-construct laws main() needs).
/-- info: 'GoLean.Iris.wp_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_init
/-- info: 'GoLean.Iris.wp_init_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_init_int
/-- info: 'GoLean.Iris.wp_assign_var' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_assign_var
/-- info: 'GoLean.Iris.wp_assign_var_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_assign_var_int

-- Item 5: the slice composition and its closed end-to-end theorem.
/-- info: 'GoLean.Iris.wp_seq_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_seq_return
/-- info: 'GoLean.Iris.wp_call_nullary_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_call_nullary_ret
/-- info: 'GoLean.Iris.wp_main_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_main_call
/-- info: 'GoLean.Iris.wp_main_returns_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_main_returns_two
/-- info: 'GoLean.Iris.slice_adequate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slice_adequate

-- The end-to-end artifact: a CLOSED `adequate` theorem composed from the WP
-- laws through go_adequacy (arc slice-l5-pure item 2). The chain composes.
/-- info: 'GoLean.Iris.wp_seq_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wp_seq_done
/-- info: 'GoLean.Iris.adequate_seqn_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adequate_seqn_nil

/-! ## Non-vacuity gate — every user-facing WP law is bound to a discharge witness.
    Deleting a witness (or a law) makes one of these references fail to elaborate,
    breaking the build. `wp_assign_lit`/`wp_deref_store_ref` each instantiate their
    law on a concrete program and discharge all but the external store-typing
    side-condition. -/

/-- `✓` wp_assign — witnessed by `wp_assign_lit` (`x = intLit n`). -/
example := @wp_assign_lit
/-- `✓` wp_deref_store — witnessed by `wp_deref_store_ref` (`*(&x) = intLit n`,
the heap-independent address the law covers). -/
example := @wp_deref_store_ref
/-- `✓` wp_store_via_ptr — witnessed by `wp_inc_via_ptr` (`*p = *p + 1`, the
multi-`↦` read-through store; ∀-general over the stored int). -/
example := @wp_inc_via_ptr
/-- `✓` wp_call_unary — witnessed by `wp_inc_call` (the full `inc(&x)` call:
frame entry with fresh param cell → body store → frame exit; premises are
program membership (genuinely external) and the argument-variable resolution
(fixed-env, discharged by `simp` at every use)). -/
example := @wp_inc_call
/-- `✓` wp_frame_return — witnessed by `wp_frame_return_int` (int result local
returned into an int target cell, ∀-general). -/
example := @wp_frame_return_int
/-- `✓` wp_init — witnessed by `wp_init_int` (`x := 0` at int, zero
hypotheses). -/
example := @wp_init_int
/-- `✓` wp_assign_var — witnessed by `wp_assign_var_int` (int var copy,
∀-general). -/
example := @wp_assign_var_int
/-- `✓` wp_call_nullary_ret — witnessed by `wp_main_call` (main's entry in the
slice composition; ∀-general over kind/lit). -/
example := @wp_main_call
/-- `✓` the slice itself — `slice_adequate` is the closed end-to-end theorem
(never-stuck, r ↦ 2 machine-checked inside; see its docstring for the
operational-readout remainder). -/
example := @slice_adequate

/-! ## Three-state ledger — what is NOT yet fully closed (kept honest, not hidden)

- `✓ go_adequacy` — **instantiated end-to-end** (arc `slice-l5-pure` item 2,
  2026-07-20): `adequate_seqn_nil` composes `wp_seqn` + `wp_seq_done` +
  `wp_value'` through `go_adequacy` with the concrete bundle `GoCoreS`,
  yielding a closed, zero-hypothesis `adequate .NotStuck …` for the
  empty-sequence program from any initial state — the chain composes, and the
  conclusion mentions no Iris. **Honest scope:** the witness is a *pure*
  program. A *heap-touching* end-to-end witness (composing `wp_assign_lit`)
  additionally needs a `go_heap_adequacy` variant that hands the initial
  heap's `↦` fragments to the WP proof (HeapLang's `heap_adequacy` shape) —
  tracked as punch-list item 2b, not yet built.
- `✓ wp_seqn` — now consumed by the end-to-end witness `adequate_seqn_nil`.
- `✓ wp_assign_lit` / `✓ wp_deref_store_ref` — **ZERO hypotheses** (arc
  `slice-l5-pure` item 1, 2026-07-20): the formerly-open `hstore` side-condition
  is now proven via `storeLoc_int_cell` + `intKind_normalize_idem` (idempotent
  normalize on an int-typed cell, arbitrary prior value). Each witness is a
  closed instantiation of its law.
- `✓ interpreterSound_frag` — the interpreter⇄relation correspondence is
  **proven over the scalar+pointer fragment, calls included** (arc
  `eval-totalization`, 2026-07-21): the Eval big-step cluster was totalized
  (GoCore has zero `partial def`s), and `execStmt_frag_sound`/
  `execStmtList_frag_sound` (mutual simulation on `(fuel, sizeOf stmt)`)
  derive `interpreterSound_frag` — a normal interpreter completion of a
  fragment statement (assign, seqn, block with declarations, if, while,
  return/break/continue, **and direct calls with frames**: `Step.call` →
  body simulation → `frameReturn`/`frameFall`) over a fragment program
  (`StInv`: fragment heap, no methods, fragment functions) is a reachable
  `Steps` terminal, in exactly `interpreterSoundStatement`'s shape. The D2
  frame-exit divergence is carried as the `avoid`-index discipline
  (block-scoped declarations may not shadow result names); value-returning
  fall-through is excluded syntactically (`EndsRet`, mirroring Go's
  missing-return compile error). Axiom-clean.
- The **unrestricted** `interpreterSoundStatement`/`interpreterPanicStatement`
  remain `def : Prop` — **stated, not proven**, and are *false as literally
  stated* (the interpreter is richer than the relation, e.g. string `add`;
  and D1 nested-`seqn` scoping — see the Correspondence module header and
  `docs/2026-07-21_eval-totalization-correspondence.md`). Nothing here or
  elsewhere should count them as established. The D1 splice rule and the panic side
  (D3) are the tracked next layers (Arc C); calls are covered as of item 6e.
-/

/-- Non-vacuity reference: the fragment correspondence theorems exist and
type-check with their stated hypotheses. -/
example := @GoLean.GoCore.Correspondence.interpreterSound_frag
example := @GoLean.Iris.SliceCorrespondence.slice_interp_run_in_relation
example := @GoLean.Iris.SliceCorrespondence.frontend_shaped_decl_in_relation
example := @GoLean.GoCore.Correspondence.execStmt_frag_sound
example := @GoLean.GoCore.Correspondence.evalExpr_frag_ok

end GoLean.Iris.Audit
