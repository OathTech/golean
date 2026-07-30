import Lean
import GoLeanProofs
import GoLean

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
    A change to any set fails the build until this file is deliberately updated.
    (R3 REBUILD, 2026-07-23: the reshape's S4 PRUNED block — the per-theorem
    restoration checklist — served its purpose and is replaced by the gates
    below over the restored surface. The old entries and their theorems
    remain readable at git rev 5a9eab2; the retirement mapping is in the
    ledger section.) -/

-- The machine correspondence (T1/T2's replacement) — note: no
-- Classical.choice; these are constructive.
/-- info: 'GoLean.GoCore.Machine.stepFn_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepFn_sound
/-- info: 'GoLean.GoCore.Machine.step_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_complete
/-- info: 'GoLean.GoCore.Machine.runConfig_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.runConfig_sound
/-- info: 'GoLean.GoCore.Machine.execStmt_sound_normal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execStmt_sound_normal
/-- info: 'GoLean.GoCore.Machine.step_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_det

-- The adequacy family.
/-- info: 'GoLean.Iris.go_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.go_adequacy
/-- info: 'GoLean.Iris.go_heap_adequacy_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.go_heap_adequacy_own
/-- info: 'GoLean.Iris.go_heap_invariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.go_heap_invariance
/-- info: 'GoLean.Iris.adequate_seqn_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.adequate_seqn_nil

-- The exit pipes.
/-- info: 'GoLean.Iris.goSpec_of_wp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.goSpec_of_wp
/-- info: 'GoLean.Iris.goInvariant_of_wp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.goInvariant_of_wp

-- The composed-walk laws and their witnesses.
/-- info: 'GoLean.Iris.wp_assign_lit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_assign_lit
/-- info: 'GoLean.Iris.wp_while_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_while_inv
/-- info: 'GoLean.Iris.wp_while_eq_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_while_eq_once
/-- info: 'GoLean.Iris.wp_recover_catch_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_recover_catch_seven
/-- info: 'GoLean.Iris.GoldenSlice.wp_goldenDriver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenSlice.wp_goldenDriver
/-- info: 'GoLean.Iris.GoldenRecover.wp_recoverDirect_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenRecover.wp_recoverDirect_body

-- The golden surface: all six step-0 targets.
/-- info: 'GoLean.Surface.goldenSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenSpec
/-- info: 'GoLean.Surface.goldenFuncSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenFuncSpec
/-- info: 'GoLean.Surface.goldenInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenInvariant
/-- info: 'GoLean.Surface.goldenTriple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenTriple
/-- info: 'GoLean.Surface.goldenReturnsTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenReturnsTwo
/-- info: 'GoLean.Surface.goldenNotThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenNotThree

-- The recover spec over the PINNED ACTUAL LOWERING (proof-corpus
-- catch-up arc, slice B — the manifest gate for the frontend-lowering
-- twin of `wp_recover_catch_seven`).
/-- info: 'GoLean.Surface.recoverFuncSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.recoverFuncSpec

/-! ## Non-vacuity gate — every user-facing WP law bound to a discharge
    witness (deleting a witness or a law breaks this build). -/

/-- `✓` the expression-walk step laws + `wp_assign_lit` — the composed
assignment walk is itself the discharge witness of the walk architecture
(every step law's premise discharged on a concrete statement). -/
example := @GoLean.Iris.wp_assign_lit
/-- `✓` wp_while_inv — witnessed by `wp_while_eq_once` (corpus-pinned
`control-flow/while-eq-single-iteration`; the full Löb cycle with real
machine walks on both sides). -/
example := @GoLean.Iris.wp_while_eq_once
/-- `✓` the call laws — witnessed on the CONCRETE golden functions
(`wp_call_enter_inc`, `wp_call_enter_incViaCall`; kernel-bridged literals;
external premises = the program/method pins). -/
example := @GoLean.Iris.wp_call_enter_inc
example := @GoLean.Iris.wp_call_enter_incViaCall
/-- `✓` the frame exits — `wp_frame_return_int` (premise-free given
resources) and its invariant-opening form, both consumed by the golden
walk. -/
example := @GoLean.Iris.wp_frame_return_int
example := @GoLean.Iris.wp_frame_return_int_inv
/-- `✓` the unwinding/defer/call-value law families (proof-corpus
catch-up arc, 2026-07-26) — witnessed AT ONCE by the recover-catch
composition walk (`defer rec(&r); panic("boom")` provably returns 7:
defer registration, panic entry, unwinding, the PANIC-path drain, the
recover walk marking the chain, the write through the captured pointer,
the cancelled unwind, and both frame exits), plus per-law instantiation
witnesses for the paths the walk does not traverse (value-call entry,
normal-path drains, unrecovered resume, chain merge, breakables).
Proof-corpus entry: the defer/recover composition row
(`docs/2026-07-24_proof-corpus.md` §5). -/
example := @GoLean.Iris.wp_recover_catch_seven
example := @GoLean.Iris.wp_call_value_enter_rec
example := @GoLean.Iris.wp_frame_defer_return_rec
example := @GoLean.Iris.wp_frame_defer_fall_rec
/-- `✓` the same composition over the PINNED ACTUAL LOWERING
(`GoldenRecover.recoverLowered`, `scripts/check-golden`'s second program;
proof-corpus catch-up arc slice B, 2026-07-30): the walk additionally
witnesses `wp_init` at an interface type, the interface-cell store, the
recover continuation walk crossing the assign frames, and the FALL-path
value frame exit `wp_frame_fall_int` (a function that ends by
recovered-panic fall-through, never by `return`). `recoverFuncSpec` is
the manifest gate for the row. -/
example := @GoLean.Iris.GoldenRecover.wp_recoverDirect_body
example := @GoLean.Iris.GoldenRecover.wp_recoverCall
example := @GoLean.Iris.wp_frame_fall_int
example := @GoLean.Surface.recoverFuncSpec

/-- `✓` the golden walk and both its call forms. -/
example := @GoLean.Iris.GoldenSlice.wp_inc_body
example := @GoLean.Iris.GoldenSlice.wp_call_inc_stmt
example := @GoLean.Iris.GoldenSlice.wp_incViaCall_body
example := @GoLean.Iris.GoldenSlice.wp_goldenCall
example := @GoLean.Iris.GoldenSlice.wp_goldenCall_inv
/-- `✓` the negative pins (trivialization guards). -/
example := @GoLean.GoCore.NegativeSpecs.unbound_ref_stuck
example := @GoLean.GoCore.NegativeSpecs.unbound_var_stuck
example := @GoLean.GoCore.NegativeSpecs.terminal_stuck
example := @GoLean.GoCore.NegativeSpecs.div_nonzero_no_panic

/-! ## Three-state ledger

- `✓ Machine correspondence` (reshape S5, 2026-07-23) — `stepFn_sound` +
  `step_complete` + `runConfig_sound`/`execStmt_sound_normal` replace the
  old T1/T2 fragment inductions AT FULL-FRAGMENT SCOPE (no `StInv`, no
  `HeapFrag`, no spine conditions). The old *fragment-scoped* theorems
  (`interpreterSound_frag`, `interpreterPanic_frag`) are RETIRED —
  superseded by strictly stronger statements. The driver-level PANIC
  assembly (an `interpreterPanic` analogue over `runConfig`'s `.error`
  path) is explicitly QUEUED, not claimed: helper-propagated panics at
  relation-silent sites make it need a reachability argument (stage log
  §6′ of the design note).
- `✓ Surface` (R3, 2026-07-23) — ALL SIX golden targets re-proven over
  the machine (`goldenSpec`/`goldenFuncSpec`/`goldenInvariant`/
  `goldenTriple`/`goldenReturnsTwo`/`goldenNotThree`), statements
  unchanged in content modulo two RECORDED strengthenings (env as
  `execStmt`-wrapper argument; `HeapFrag` side-condition retired). The
  exit pipes lost their fragment shape checks. The old
  existential-address `*_computes` readouts and the hand-model slice
  chain (`slice_adequate`, `wp_main_returns_two`, `wp_inc_call`, …) are
  RETIRED as superseded — the pinned-observable forms subsume their
  claims; the deleted theorems remain at git rev 5a9eab2.
- `✓ Loop` (R3) — `wp_while_inv` re-derived with the bind-form condition
  premise; the arc-E recorded divergence (condition as operational
  premise) is CLOSED exactly as its revisit note predicted.
- The unrestricted driver-outcome parity statements (normal AND panic and
  stuck classification, wrapper vs relation) are NOT claimed as theorems;
  the differential (zero drift on 718) is the operational evidence, and
  the queued panic assembly is the proof-side gap on record.
-/

end GoLean.Iris.Audit
