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
- `✓ go_heap_adequacy` + `✓ slice_adequate_computes` +
  `✓ slice_interp_computes_two` — **the 2b operational readout is closed in
  its COMPUTED-SOMEWHERE form** (arc `exit-infra`, 2026-07-21): strong
  adequacy surfaces an Iris-side `↦ 2` into `adequate`'s φ as a final
  `ExecState` fact, and composing with the correspondence yields: EVERY
  terminating interpreter run of the slice program ends with SOME heap cell
  holding `int 2` — no execution in the proof; no Iris, and not even the
  relation, in the statement. **The cell's address is EXISTENTIAL — this is
  NOT the lowering target** ("the result cell holds 2"): it cannot
  distinguish "returns 2" from "computed 2 somewhere" (dead frame cells
  also hold 2). Per `docs/2026-07-21_native-spec-surface.md` D8, the
  lowering target is claimed only by the pinned-observable form — which is
  now PROVEN: see the `✓ Surface` entry (`goldenReturnsTwo`, with the
  `≠ 3` twin as its corollary).
- `✓ golden_interp_computes_two` — **the computed-somewhere readout holds
  over the FRONTEND'S OWN OUTPUT** (arc `exit-infra`, 2026-07-21; same
  existential-address scope as above — NOT the lowering target): the full
  WP walk (`wp_incLowered_call` → `wp_incViaCallLowered_ret2` →
  `golden_adequate_computes`) runs over `GoldenSlice.sliceLowered` — the
  frontend's actual lowering, pinned by `scripts/check-golden` — through
  every Arc C mechanism the hand model never exercised: `wp_block_nil` +
  pushed-scope lookups, D1 `seqCont` splices of nested `.seqn` groups
  (`seqCont_splice`, the first use of the splice branch in a WP proof), the
  explicit `x = 0` assignment, the synthesized `$res0` result local.
  Composed with `golden_interp_run_in_relation`: every terminating
  interpreter run of the driver over the lowered program ends with a heap
  cell holding `int 2`. The "hand model ≈ lowering" manual claim is retired;
  the same existential-address honest scope as the slice version applies.
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
  `Steps` terminal, in exactly `interpreterSoundStatement`'s shape.
  (Updated for arc `rel-completion`: frame exits read call-time-pinned
  locations, so block-scoped shadowing needs NO condition and fall-through
  stores like `frameReturn`; the residual Go-unreachable condition is only
  that a body's spine inits don't redeclare a result id —
  `SpineFrag.init`'s `∉ avoid`.) Axiom-clean.
- `✓ interpreterPanic_frag` — the panic side is **proven over the fragment**
  (arc `rel-completion` D3b, 2026-07-21): an interpreter panic on a fragment
  statement reaches the relation's terminal `.panicked` with the same
  message (T1p/T2p mutual panic induction; substrate panic-freedom lemmas;
  witnessed on `x := 1; x = 1/0`).
- `✓ Surface` (arc `spec-surface`, 2026-07-21) — **THE LOWERING TARGET IS
  CLOSED, in its pinned-observable form.** All three step-0 targets are
  PROVEN (`Specs/GoldenSurface.lean`): `goldenTriple`
  (`{r ↦ 0} r = incViaCall() {r ↦ 2}` — a native `GoTriple` over
  `execStmt` runs of the frontend's actual lowering),
  `goldenReturnsTwo` (the Verdi-register corollary: the designated output
  cell at base address 0 holds `int 2` in every terminating run — no `∃`
  over addresses), and `goldenNotThree` (the negative twin, now the
  promised two-line corollary). Machinery, all once-proven:
  `go_heap_adequacy_own` (initial-heap handover via `genHeap_init_names`),
  the `SurfaceBridge` crossings (`reflect`/`extract` by `HProp` induction;
  extraction reconstructs genuine disjointness from `DFrac` validity), and
  the generic exit theorem `goTriple_of_wp` — per-program obligations are
  exactly the fragment shape checks plus the WP proof (the golden walk,
  reused unchanged — twice now: the frame-closure upgrade below also left
  it untouched). **Frame closure + progress landed (same arc, later):**
  `GoTriple` is now FRAME-CLOSED — the quantified-testcase form: any heap
  where the `P`-footprint is allocated, and the frame provably survives
  untouched (`F.sub` of the final heap) — with Iris's `wp_frame_l`
  carrying the frame inside `goSpec_of_wp` so the per-program WP
  obligation never mentions it; and `Progress` (every relation-reachable
  configuration is terminal or can step, from `adequate_not_stuck`) is
  bundled with the triple as `GoSpec`. `goldenSpec` proves the full
  judgment for the golden program, and `goldenFuncSpec` proves the
  function-level quantified-testcase form (`GoFuncSpec`, v1: unary int
  result, return observed at the caller's target cell = the call
  protocol's/`collectResults`' frame-exit observation; `(T, error)`
  queued behind the interface widening) — "`incViaCall()` needs no heap
  and returns 2", ∀ target cell, prior value, and frame; the golden WP
  walk reused unchanged a fourth time. v1 honest scope: the fragment-scope
  side condition (`HeapFrag` on the raw initial heap) remains; a
  `.panicked` terminal counts as stuck, so `Progress` implies no reachable
  panics (#24 scope).
- The **unrestricted** `interpreterSoundStatement`/`interpreterPanicStatement`
  remain `def : Prop` — **stated, not proven**, and false as literally
  stated only for the richer-interpreter reason now (the interpreter covers
  values/constructs the relation doesn't; the D1 splice rule landed, so the
  scoping counterexample is gone). Nothing here or elsewhere should count
  them as established; widening the fragment narrows the gap.
-/

/-- Non-vacuity reference: the fragment correspondence theorems exist and
type-check with their stated hypotheses. -/
example := @GoLean.GoCore.Correspondence.interpreterSound_frag
example := @GoLean.Iris.SliceCorrespondence.slice_interp_run_in_relation
example := @GoLean.Iris.SliceCorrespondence.frontend_shaped_decl_in_relation
example := @GoLean.GoCore.Correspondence.interpreterPanic_frag
example := @GoLean.Iris.SliceCorrespondence.panic_shaped_in_relation
example := @GoLean.Iris.SliceCorrespondence.panic_eq_shaped_in_relation
example := @GoLean.Iris.SliceCorrespondence.panic_call_arg_in_relation
example := @GoLean.Iris.go_heap_adequacy
example := @GoLean.Iris.slice_adequate_computes
example := @GoLean.Iris.SliceCorrespondence.slice_interp_computes_two
example := @GoLean.Iris.GoldenSlice.golden_interp_run_in_relation
example := @GoLean.Iris.GoldenSlice.sliceLowered_funcs
example := @GoLean.Iris.GoldenSlice.wp_incLowered_call
example := @GoLean.Iris.GoldenSlice.wp_incViaCallLowered_ret2
example := @GoLean.Iris.GoldenSlice.golden_adequate_computes
example := @GoLean.Iris.GoldenSlice.golden_interp_computes_two
example := @GoLean.Surface.GoTriple
example := @GoLean.Surface.goldenTriple_statement
example := @GoLean.Surface.goldenReturnsTwo_statement
example := @GoLean.Surface.goldenNotThree_statement
example := @GoLean.Iris.go_heap_adequacy_own
example := @GoLean.Iris.reflect
example := @GoLean.Iris.extract
example := @GoLean.Iris.goTriple_of_wp
example := @GoLean.Iris.goSpec_of_wp
example := @GoLean.Surface.GoSpec
example := @GoLean.Surface.Progress
example := @GoLean.Surface.GoFuncSpec
example := @GoLean.Surface.goldenSpec
example := @GoLean.Surface.goldenFuncSpec
example := @GoLean.Surface.goldenTriple
example := @GoLean.Surface.goldenReturnsTwo
example := @GoLean.Surface.goldenNotThree
example := @GoLean.GoCore.Correspondence.execStmt_frag_sound
example := @GoLean.GoCore.Correspondence.evalExpr_frag_ok

end GoLean.Iris.Audit
