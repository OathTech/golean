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
theorem (public or private) added anywhere under the proof-facing namespaces
would dodge it. This sweep closes that: it walks **every** constant whose
(private-name-stripped) name lies under `GoLean.Iris` or `GoLean.GoCore`
(relation, correspondence, substrate — everything the proofs rest on), collects
its transitive axioms, and **fails the build** if any declaration depends on
one outside the classical trio `{propext, Classical.choice, Quot.sound}` —
which is exactly how a `sorry` (`sorryAx`) or `native_decide` (`ofReduceBool`)
would surface. Coverage is by construction, not by enumeration: adding a
declaration automatically adds it to the audit. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`GoLean.Iris, `GoLean.GoCore]
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut bad : Array (Name × Name) := #[]
  let mut audited := 0
  for n in names do
    let user := (privateToUserName? n).getD n
    unless prefixes.any (·.isPrefixOf user) do continue
    let axs ← collectAxioms n
    audited := audited + 1
    for ax in axs do
      unless allowed.contains ax do
        bad := bad.push (n, ax)
  if bad.isEmpty then
    IO.println s!"audit sweep: {audited} declarations under GoLean.Iris/GoLean.GoCore, all axiom-clean"
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

/-! ## Three-state ledger — what is NOT yet fully closed (kept honest, not hidden)

- `◌ go_adequacy` — axiom-clean, but **not yet instantiated end-to-end**: no
  witness composes the WP laws into a `WP c {{…}}` and feeds `go_adequacy` to
  yield a closed `adequate …` for a concrete program. Until that witness exists,
  "the chain composes" is unproven at the top. Tracked: build an adequacy
  end-to-end witness (a concrete GoCore program, WP built from `wp_seqn` +
  `wp_assign_lit`, no remaining hypotheses).
- `◌ wp_seqn` — axiom-clean; a pure control-reduction law with no `∀σ`-over-state
  premise (no vacuity surface), currently used by no downstream witness. Low
  risk; a witness lands with the adequacy end-to-end proof.
- `◌ wp_assign_lit` / `wp_deref_store_ref` — discharge every premise **except**
  the external `hstore` (a `∀σ` store-typing side-condition). That premise is
  believed dischargeable (idempotent normalize on a well-typed int cell) but is
  **not proven here**. Tracked: discharge `hstore` for a concrete cell so a
  witness carries *zero* open hypotheses.
- The interpreter⇄relation correspondence (`interpreterSoundStatement`,
  `interpreterPanicStatement`) are `def : Prop` — **stated, not proven**
  (blocked on Eval big-step totalization). They are claims, not theorems; nothing
  here or elsewhere should count them as established.
-/

end GoLean.Iris.Audit
