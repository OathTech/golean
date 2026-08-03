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

/-! ## Statement-TCB gate — the DELETION TEST, mechanized

Doctrine of record: `docs/2026-08-01_tcb-and-layering-doctrine.md` §1.
Top-level theorem STATEMENTS must be semantically interpretable without
Iris: if Iris were deleted from the build, every designated headline
statement must still elaborate and denote the same proposition in base
definitions. Proofs may use anything — they are deleted with Iris; the
statements remain and must still be the same questions.

Mechanization: for each DESIGNATED theorem below, walk the transitive
STATEMENT CLOSURE of its type and fail the build if any constant reached
originates in an Iris module (module-of-origin via `getModuleIdxFor?`,
root name `Iris` — the same discrimination the axiom sweep uses, so a
stray top-level or renamed constant cannot dodge it; note this
deliberately includes `Iris.Std.*`).

**The closure, precisely** (the deletion test needs every constant the
statement's MEANING depends on):
- seed: the constants of the theorem's TYPE expression;
- for every constant reached, the constants of its own TYPE — a
  statement means nothing if something it mentions no longer elaborates;
- for a DEFINITION reached (`defnInfo` — incl. `def`/`abbrev`/matchers/
  well-founded auxiliaries), additionally the constants of its VALUE:
  the statement's meaning unfolds through definitions, so a `def` whose
  body mentions Iris smuggles Iris into the proposition even when the
  type looks clean;
- for an INDUCTIVE reached, its constructors (and hence their types):
  the denoted proposition quantifies over the type's inhabitants, which
  the constructors determine;
- for a THEOREM or AXIOM reached, its type only — proof terms are
  irrelevant to what the statement SAYS (they are exactly what the
  deletion deletes);
- for an OPAQUE constant reached (`opaqueInfo` — `opaque` defs, and the
  kernel-level `default` stubs Lean emits for `partial def` and for
  derived nested-inductive `BEq`/`Repr` instances), additionally the
  constants of its VALUE, same as a definition: an
  `opaque x : Prop := <Iris term>` smuggles Iris exactly as a `def`
  would. (Audit response 2026-08-01, pre-merge finding: the first form's
  `| _ => pure ()` catch-all silently truncated this kind to type-only —
  a constructed `opaque … := Nonempty CoPset` statement passed the gate.
  Decision recorded here: constructors, recursors and the `Quot`
  primitives have no separate value and contribute their types only; the
  match below is EXHAUSTIVE, no wildcard, so a `ConstantInfo` kind this
  gate has not explicitly considered is a COMPILE ERROR — fail closed —
  never a silent type-only fallback.)

This is stronger than the surface-purity import scan (an unused Iris
import survives deletion; a statement unfolding through one Iris
constant does not) and complements it: imports are checked per-module,
meaning is checked per-theorem. On success it prints the audited count
and the per-theorem closure sizes, so growth is visible in the log.
Fail-closed everywhere: a missing designated name, a non-theorem, an
unresolvable constant, or an exhausted walk budget all FAIL the build —
whitelist nothing. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isIris : Array Bool := mods.map (fun m => m.getRoot == `Iris)
  -- The designated headline theorems (the summit family + the golden and
  -- recover surfaces + the math bridge). Extend this list when a new
  -- headline theorem is claimed; never remove without a recorded reason.
  -- (Audit response 2026-08-01: `goldenInvariant` added — the sixth
  -- step-0 target, axiom-gated below and named "all six" there, but
  -- omitted here since the list's introduction with no recorded reason;
  -- plus the two new first-order readouts `recoverReturnsSeven` and
  -- `quorumAckedIndexReturnsTwelveTrue`, the doctrine's mandatory
  -- rung-2 readout twins for `recoverFuncSpec` /
  -- `quorumAckedIndexFuncSpec2`.)
  let designated : List Name := [
    ``GoLean.Surface.quorumOneKnownFuncSpec,
    ``GoLean.Surface.quorumOneKnownMeetsSpec,
    ``GoLean.Surface.quorumOneKnownReturnsTwelve,
    ``GoLean.Surface.quorumOneKnownNotEleven,
    ``GoLean.Surface.quorumThreeAllFuncSpec,
    ``GoLean.Surface.quorumThreeAllMeetsSpec,
    ``GoLean.Surface.quorumThreeAllReturnsSix,
    ``GoLean.Surface.quorumThreeAllNotTwelve,
    ``GoLean.Surface.committedIndexAllConfigs,
    ``GoLean.Surface.committedIndexAllReturnsSix,
    ``GoLean.Surface.committedIndexAllNotTwelve,
    ``GoLean.Surface.committedIndexAll_refutes_wrong,
    ``GoLean.Surface.quorumAckedIndexFuncSpec2,
    ``GoLean.Surface.quorumAckedIndexReturnsTwelveTrue,
    ``GoLean.Surface.recoverFuncSpec,
    ``GoLean.Surface.recoverReturnsSeven,
    ``GoLean.Surface.goldenFuncSpec,
    ``GoLean.Surface.goldenSpec,
    ``GoLean.Surface.goldenTriple,
    ``GoLean.Surface.goldenInvariant,
    ``GoLean.Surface.goldenReturnsTwo,
    ``GoLean.Surface.goldenNotThree,
    ``GoLean.Quorum.committedIndexRef_meets_spec]
  let mut lines : Array String := #[]
  let mut violations : Array String := #[]
  for t in designated do
    let some tinfo := env.find? t
      | throwError "statement-TCB gate: designated theorem {t} is MISSING \
          (renamed without re-pointing the gate?)"
    unless tinfo matches ConstantInfo.thmInfo _ do
      throwError "statement-TCB gate: {t} is not a theorem"
    -- Worklist walk of the statement closure, with parent pointers so a
    -- violation reports its dependency chain, and an explicit budget so
    -- the walk is total and fails loud rather than spinning.
    let mut queue : Array Name := tinfo.type.getUsedConstants
    let mut parent : Std.HashMap Name Name := {}
    for c in queue do
      parent := parent.insert c t
    let mut visited : NameSet := {}
    let mut exhausted := true
    for _ in [0:2000000] do
      if queue.isEmpty then
        exhausted := false
        break
      let c := queue.back!
      queue := queue.pop
      if visited.contains c then
        continue
      visited := visited.insert c
      match env.getModuleIdxFor? c with
      | some idx =>
        if isIris[idx.toNat]! then
          -- Reconstruct the reach chain for the report, then stop at the
          -- boundary (no recursion INTO Iris — one constant is the proof).
          let mut chain := s!"{c}"
          let mut cur := c
          for _ in [0:100000] do
            match parent.get? cur with
            | some p =>
              chain := s!"{p} → " ++ chain
              cur := p
              if p == t then break
            | none => break
          violations := violations.push
            s!"  {t}: statement closure reaches Iris constant {c} \
              (module {mods[idx.toNat]!})\n    chain: {chain}"
          continue
      | none => pure ()
      let some ci := env.find? c
        | throwError "statement-TCB gate: {c} (reached from {t}) not found"
      let mut next : Array Name := ci.type.getUsedConstants
      -- EXHAUSTIVE over ConstantInfo — no wildcard (fail-closed; see the
      -- docstring's opaque-constant rule, audit response 2026-08-01).
      match ci with
      | .defnInfo v => next := next ++ v.value.getUsedConstants
      | .opaqueInfo v => next := next ++ v.value.getUsedConstants
      | .inductInfo v => next := next ++ v.ctors.toArray
      | .thmInfo _ => pure ()   -- type only, deliberate (docstring rule)
      | .axiomInfo _ => pure () -- type only, deliberate (docstring rule)
      | .ctorInfo _ => pure ()  -- no value; type already walked
      | .recInfo _ => pure ()   -- no value; type already walked
      | .quotInfo _ => pure ()  -- primitive; type already walked
      for n in next do
        unless visited.contains n do
          if !(parent.contains n) then
            parent := parent.insert n c
          queue := queue.push n
    if exhausted then
      throwError "statement-TCB gate: walk budget exhausted at {t} — \
        raise the bound deliberately, never silently"
    lines := lines.push s!"  {t}: {visited.size} statement constants"
  if violations.isEmpty then
    IO.println s!"statement-TCB gate: {designated.length} designated theorems, \
      all statement closures Iris-free"
    for l in lines do
      IO.println l
  else
    throwError "statement-TCB gate FAILED — a headline STATEMENT depends on \
      Iris (the deletion test; reformulate the statement, do not whitelist):\n\
      {String.intercalate "\n" violations.toList}"

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
-- Its first-order readout twin (audit response 2026-08-01 — the
-- doctrine's mandatory rung-2 readout, previously missing).
/-- info: 'GoLean.Surface.recoverReturnsSeven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.recoverReturnsSeven

-- Quorum-pilot phase-0 pins (statement-first targets; the *_statement
-- defs are TARGETS and are deliberately not pinned as results — these
-- are the non-vacuity instances showing the spec is satisfiable and
-- bites, on etcd's own example values).
/-- info: 'GoLean.Quorum.isCommittedIndex_acked3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Quorum.isCommittedIndex_acked3
/-- info: 'GoLean.Quorum.not_committedIndex_acked3_103' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Quorum.not_committedIndex_acked3_103
/-- info: 'GoLean.Quorum.not_committedIndex_acked3_101' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Quorum.not_committedIndex_acked3_101

-- Quorum-pilot phase-4 per-construct laws (`Laws/StmtOps.lean` + `Specs/GoldenQuorumPin.lean`, né `Laws/QuorumOps.lean`,
-- 2026-07-31): the wide-statement (`stmtOpK`) walk, `sortSlice`,
-- `mapLookup`, and the map-range snapshot — each pinned on the walk it
-- is witnessed by.
/-- info: 'GoLean.Iris.wp_map_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_map_lookup
/-- info: 'GoLean.Iris.wp_sort_slice_srt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_sort_slice_srt
/-- info: 'GoLean.Iris.wp_map_range_snapshot_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_map_range_snapshot_committed
-- (Axiom set SHRANK [propext, Quot.sound] → [propext] at the de-WF
-- restructure 2026-08-03 — the refuting counterexample's evaluation no
-- longer routes through Quot-based machinery. Shrinking is the safe
-- direction; re-pinned to the actual set.)
/-- info: 'GoLean.Iris.typeEnv_pin_is_load_bearing' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Iris.typeEnv_pin_is_load_bearing

-- Quorum-pilot phase-4 slice 5 (2026-07-31): the first multi-result
-- function-spec discharge over the pinned lowering, its walk, and the
-- satisfiability guard on its precondition.
/-- info: 'GoLean.Surface.quorumAckedIndexFuncSpec2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumAckedIndexFuncSpec2
-- Its two-cell first-order readout twin (audit response 2026-08-01 —
-- the doctrine's mandatory rung-2 readout, previously missing).
/-- info: 'GoLean.Surface.quorumAckedIndexReturnsTwelveTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumAckedIndexReturnsTwelveTrue
/-- info: 'GoLean.Iris.GoldenQuorum.wp_ackedIndexCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_ackedIndexCall
/-- info: 'GoLean.Iris.wp_call_enter_ackedIndexImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_call_enter_ackedIndexImpl
/-- info: 'GoLean.Surface.quorumAckedIndexPre_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumAckedIndexPre_satisfiable

-- Quorum-pilot phase-4 SUMMIT (2026-07-31): THE GOAL's first instance —
-- the real `main.MajorityConfig.CommittedIndex` of the pinned lowering,
-- walked end to end at n = 1, at `GoFuncSpec` strength, with the machine
-- answer upgraded to the declarative quorum spec.
/-- info: 'GoLean.Surface.quorumOneKnownFuncSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownFuncSpec
/-- info: 'GoLean.Surface.quorumOneKnownMeetsSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownMeetsSpec
/-- info: 'GoLean.Surface.quorumOneKnownReturnsTwelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownReturnsTwelve
/-- info: 'GoLean.Surface.quorumOneKnownNotEleven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownNotEleven
/-- info: 'GoLean.Iris.wp_map_iter_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_map_iter_inv
/-- info: 'GoLean.Iris.wp_map_iter_inv_key_sum_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_map_iter_inv_key_sum_witness
/-- info: 'GoLean.Iris.GoldenQuorum.wp_committedIndex_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_committedIndex_body
/-- info: 'GoLean.Iris.GoldenQuorum.wp_oneKnownCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_oneKnownCall

-- Proof-automation arc phase 3 (2026-08-01): THE 3-VOTER RUNG — the same
-- real `CommittedIndex`, at a config whose map range has 3! = 6 iteration
-- orders, discharged by ONE generic iteration through `wp_map_iter_inv`
-- plus a permutation invariant, and an ORDER-BLIND sort.
/-- info: 'GoLean.Surface.quorumThreeAllFuncSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllFuncSpec
/-- info: 'GoLean.Surface.quorumThreeAllMeetsSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllMeetsSpec
/-- info: 'GoLean.Surface.quorumThreeAllReturnsSix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllReturnsSix
/-- info: 'GoLean.Surface.quorumThreeAllNotTwelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllNotTwelve
/-- info: 'GoLean.Iris.GoldenQuorum.wp_ci_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_ci_loop
/-- info: 'GoLean.Iris.GoldenQuorum.wp_ci_range_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_ci_range_body
/-- info: 'GoLean.Iris.mergeSort_eq_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.mergeSort_eq_of_perm
-- The MACHINE-sort twins (sub-branch audit 2026-08-03: the machine sorts
-- with the structural `sortLe` since the de-WF restructure; the mergeSort
-- lemmas above stay for the math layer's `sortAsc`).
/-- info: 'GoLean.Iris.sortLe_perm' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Iris.sortLe_perm
/-- info: 'GoLean.Iris.pairwise_sortLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.pairwise_sortLe
/-- info: 'GoLean.Iris.arraySet_middle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.arraySet_middle
/-- info: 'GoLean.Quorum.storeLoc_stk_fill' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Quorum.storeLoc_stk_fill

-- Proof-automation arc phase 4 (2026-08-01): THE ∀-CONFIG THEOREM — the
-- same real `CommittedIndex`, at EVERY config and EVERY acked map, with
-- the inputs supplied through the caller's heap. Both branches of the fit
-- test, voters that never reported, and a `slices.Sort` computed at a
-- SYMBOLIC length by induction over the machine's own loops.
/-- info: 'GoLean.Surface.committedIndexAllConfigs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.committedIndexAllConfigs
/-- info: 'GoLean.Surface.committedIndexAllReturnsSix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.committedIndexAllReturnsSix
/-- info: 'GoLean.Surface.committedIndexAllNotTwelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.committedIndexAllNotTwelve
/-- info: 'GoLean.Iris.GoldenQuorum.wp_ci_loop_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_ci_loop_all
/-- info: 'GoLean.Iris.GoldenQuorum.wp_ci_fitIf_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.GoldenQuorum.wp_ci_fitIf_all
/-- info: 'GoLean.Iris.applyStmtOp_sortSlice_ints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.applyStmtOp_sortSlice_ints
/-- info: 'GoLean.Iris.forIn_range'_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.forIn_range'_inv
/-- info: 'GoLean.Iris.mergeSort_pairs_eq_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.mergeSort_pairs_eq_of_perm
/-- info: 'GoLean.Iris.sortLe_pairs_eq_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.sortLe_pairs_eq_of_perm
/-- info: 'GoLean.Iris.mapLookupValue_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.mapLookupValue_hit
/-- info: 'GoLean.Quorum.encodesConfig_cfgSnapshot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Quorum.encodesConfig_cfgSnapshot

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
catch-up arc, 2026-07-26; coverage wording corrected 2026-07-30 after
the pre-merge audit) — the recover-catch composition walk (`defer
rec(&r); panic("boom")` provably returns 7) traverses the
defer/panic/recover SPINE (11 of the family's 21 laws); every law the
walk does not traverse has a NAMED per-law instantiation witness in
`Laws/Unwind.lean`, each referenced here so deleting any witness breaks
this build (the audit found the previous anonymous `example` witnesses
were invisible to this gate, and `wp_breakable_done` had no witness at
all — `wp_breakable_done_witness` closes it). Proof-corpus entry: the
defer/recover composition row (`docs/2026-07-24_proof-corpus.md` §5). -/
example := @GoLean.Iris.wp_recover_catch_seven
example := @GoLean.Iris.wp_call_value_enter_rec
example := @GoLean.Iris.wp_frame_defer_return_rec
example := @GoLean.Iris.wp_frame_defer_fall_rec
example := @GoLean.Iris.wp_call_value_no_targets_witness
example := @GoLean.Iris.wp_panic_resume_continue_witness
example := @GoLean.Iris.wp_panic_frame_empty_witness
example := @GoLean.Iris.wp_panic_resume_merge_witness
example := @GoLean.Iris.wp_breakable_enter_witness
example := @GoLean.Iris.wp_breakable_break_witness
example := @GoLean.Iris.wp_breakable_done_witness
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

/-- `✓` the quorum per-construct laws (`Laws/StmtOps.lean`, witnesses in `Specs/GoldenQuorumPin.lean`; né `Laws/QuorumOps.lean` — quorum
pilot phase 4 item 2, 2026-07-31), each witnessed SAME-COMMIT by a walk
over a statement `rfl`-projected out of the pinned lowering
(`QuorumPin.{rangeStmt,sortStmt,mapLookupStmt}` — edit the pin and the
projections stop being `rfl`):

- the wide-statement (`stmtOpK`) family — `wp_stmt_op_first`,
  `wp_stmt_op_shift_target`, `wp_stmt_op_shift_plain`,
  `wp_stmt_op_apply_store`, `wp_stmt_op_apply_read_store₂` — NOTHING
  existed for `stmtOpK` before this file; witnessed by the `sortSlice`
  and `mapLookup` statement walks below;
- `wp_sort_slice` (the `slices.Sort` extern, one apply step over the
  slice's single backing cell) — witness `wp_sort_slice_srt`, the REAL
  `slices.Sort(srt)` statement on `[3,1,2] ↦ [1,2,3]`;
- `wp_map_lookup` (comma-ok read: one cell read, two written) and its
  new lifting core `wp_read_store_step₂` — witness
  `wp_map_lookup_ackedIndex`, the REAL `idx, ok := m[id]` of
  `main.mapAckIndexer.AckedIndex`. The earlier recorded divergence (the
  `idx` cell declared `uint64` where the lowering declares
  `main.Index`) is CLOSED by the `σ.types` pin: the witness now names the
  faithful `.defined main.Index` cell;
- `wp_map_range_snapshot` (+ the nil form) — the state-reading step
  feeding `Laws/Range`'s nondeterministic `mapIterK` law; witness
  `wp_map_range_snapshot_committed` on the REAL voter loop.

`✓ The nondeterministic map-iteration law is PINNED and WITNESSED`
(2026-07-31, pre-merge audit finding 9). `wp_map_iter_next_key` shipped
(2528b4f) with `hnorm : ∀ σ, …` and NO same-commit witness — the exact
vacuity smell CLAUDE.md names. `normalizeValueForTy` resolves a
`.defined` key type through `TypeEnv.lookup σ.types`, so the unpinned
premise was FALSE at every NAMED key type (`map[Index]int` is literally
in `deps/raft/quorum/quick_test.go`) and the law was VACUOUS there while
reading as general; the sole instantiation was at a `uint64` key, i.e.
the target's own shape, so no gate could see it. `hnorm` now carries the
`σ.types` pin like every sibling law, and TWO named witnesses ship with
it: `wp_map_iter_next_key_basic_key_witness` (basic key — the pin rides
unused) and `wp_map_iter_next_key_defined_key_witness` (a DEFINED key
type, the instance the unpinned form could not have had). Neither names
the pilot target.

`✓ Dynamic-dispatch frame entry` (2026-07-31, the phase-4 types-pin
slice). The blocker recorded here previously — `GoCoreGS` pinned
`functions` and `methods` but NOT `types`, so every `∀ σ` premise about
`bindParams`/`allocDecls`/`concreteMethodForDynamic?` at a named type was
false and any such law vacuous — is FIXED: `GoCoreGS.types` and the
`σ.types = GoCoreGS.types GF` conjunct of the state interpretation now
pin it, and `typeEnv_pin_is_load_bearing` remains as the kernel-checked
demonstration of why the pin is load-bearing (it is a REGRESSION GUARD
now, not a blocker note). On that pin:

- `wp_call_dynamic_enter₂` — frame entry through an interface ANCHOR at
  the two-parameter/two-result arity: `enterFrame` finds the anchor,
  `dynamicDispatch?` redirects to the concrete method for the receiver
  box's dynamic type with the receiver UNBOXED, `bindParams` allocates
  the parameter cells normalized at the CONCRETE method's declared
  types, `allocDecls` defaults the results, and the body runs under the
  fresh frame. Statement is target-free (anchor id, concrete callee,
  dynamic type, names, types and values are all law variables; only the
  ARITY is fixed, as in the `wp_call_enter_arg1`/`cap1` family).
  Witness: `wp_call_dynamic_enter_ackedIndex`, on the REAL
  `main.AckedIndexer.AckedIndex` anchor of the pinned lowering, EVERY
  premise discharged by computation against `quorumLowered` with only
  the three ghost pins external.
- the general machinery it rests on, all target-free: `wp_alloc_step₄`
  (deterministic step allocating four fresh cells — the first
  multi-allocation lifting core), `bindParams₂`/`allocDecls₂` (the
  two-parameter/two-result computation equations), `allocMany` +
  `HeapWf.allocMany` (consecutive allocation, general in the list),
  `heapToMap_set_base₂`/`₄` + `insert_eqv` (the projection algebra), and
  `execState_pin_eq` (the `∀σ`-premise closer: a state with the three
  pinned fields known IS the pinned state up to heap and counter, which
  is what makes such premises computable rather than simp-fought).

`✓ Ty structural equality is total and transparent` (2026-07-31). `Ty` is
a nested inductive (`funcType` carries `List Ty`), and Lean's derived
`BEq` for nested inductives is OPAQUE — no equations, no `unfold`, no
`decide`, not even `rfl` on two identical closed types. Dynamic-type
identity is decided by `==` on `Ty`, so with the derived instance NO
dispatch fact was kernel-provable at all. `Ty.eqb`/`Ty.eqbFuel`
(`GoLean/GoCore/Value.lean`) replace it with an ordinary total,
transparent, fuel-bounded structural equality that fails closed on
exhaustion; the differential is unchanged by it (872/872 against the
recorded baseline, re-pinned by the final audit response). -/
example := @GoLean.Iris.wp_map_range_snapshot
example := @GoLean.Iris.wp_sort_slice
example := @GoLean.Iris.wp_map_lookup
example := @GoLean.Iris.wp_stmt_op_first
example := @GoLean.Iris.wp_stmt_op_shift_target
example := @GoLean.Iris.wp_stmt_op_shift_plain
example := @GoLean.Iris.wp_sort_slice_srt
example := @GoLean.Iris.wp_map_lookup_ackedIndex
example := @GoLean.Iris.wp_map_range_snapshot_committed
example := @GoLean.Iris.wp_map_range_snapshot_nil
example := @GoLean.Iris.wp_map_iter_next_key
example := @GoLean.Iris.wp_map_iter_next_key_basic_key_witness
example := @GoLean.Iris.wp_map_iter_next_key_defined_key_witness
example := @GoLean.Iris.wp_stmt_op_apply_store
example := @GoLean.Iris.wp_stmt_op_apply_read_store₂
example := @GoLean.Iris.wp_read_store_step₂
example := @GoLean.Iris.typeEnv_pin_is_load_bearing
example := @GoLean.Iris.wp_call_dynamic_enter₂
example := @GoLean.Iris.wp_call_dynamic_enter_ackedIndex
example := @GoLean.Iris.wp_alloc_step₄
example := @GoLean.Iris.bindParams₂
example := @GoLean.Iris.allocDecls₂
example := @GoLean.Iris.HeapWf.allocMany
example := @GoLean.Iris.heapToMap_set_base₄
example := @GoLean.Iris.execState_pin_eq
example := @GoLean.GoCore.Ty.eqb
/-- `✓` **the first `GoFuncSpec2` discharge** (quorum pilot phase 4
slice 5, 2026-07-31): `quorumAckedIndexFuncSpec2` — the REAL
`main.mapAckIndexer.AckedIndex` of the pinned lowering, at the
multi-result surface judgment's strength, on a concrete one-entry
receiver: the caller's two cells receive `(12, true)`, in any admissible
heap, beside any frame. The W1 arity widening's first instance. The
machine walk it rests on (`wp_ackedIndexCall` → `wp_ackedIndex_body`)
traverses: the two-target/two-argument call operand walk, the STATIC
two-parameter/two-result frame entry, `wp_init` at the DEFINED type
`main.Index`, the comma-ok map read, two stores at a defined type, and
the TWO-result frame exit — each a general law with its premises
discharged by computation against `quorumLowered`.

Trusted-surface change in the same slice (the `σ.types` pin's twin): the
Surface judgments (`GoTriple`/`Progress`/`GoInvariant`/`GoSpec`/
`GoFuncSpec`/`GoFuncSpec2`) and the exit pipe now carry the program's
**method table** instead of an empty default. `enterFrame` consults it on
every call, so the old default silently restricted every surface judgment
to programs with NO methods — i.e. no interface dispatch, the fragment
the raft target lives in. The golden/recover statements pin their own
`.methods` (both `#[]`, so they are unchanged in content); the quorum
statements pin `quorumLowered.methods`, which is what the executable
driver seeds (`StepFn.runFunctionWithContextM`).

Vacuity guard, same commit: `quorumAckedIndexPre_satisfiable` exhibits a
concrete four-cell heaplet satisfying the discharged precondition (a
`GoSpec` over an unsatisfiable `InitialSplit` would be true of anything —
the exact failure mode this file exists to catch). Statement-honesty
note: the FIRST `quorumAckedIndexFuncSpec2_statement` (`39891ae`, phase
4 — NOT phase 0, as this note said before the 2026-07-31 pre-merge audit's
finding 6; only the `GoFuncSpec2` SHAPE is phase-0) was FALSE, not
merely unproven (it passed `#[]` arguments to a two-parameter method, so
`enterFrame`'s arity check leaves the configuration stuck and `Progress`
fails); the correction is recorded in the statement's own docstring and
in the arc doc, not smuggled.

`✓` **THE ARC'S NAMED GOAL, first instance** (quorum pilot phase 4
summit, 2026-07-31): `quorumOneKnownFuncSpec` DISCHARGES the
target `quorumOneKnownFuncSpec_statement` (written at `39891ae`, one
commit earlier — phase 4, not phase 0) — the pinned lowering of the
real etcd-io/raft driver returns `12` at `GoFuncSpec` strength — and
`quorumOneKnownMeetsSpec` restates it with the DECLARATIVE quorum spec
as the postcondition (`IsCommittedIndex [1] ackedOneKnown`, via the
proven `committedIndexRef_meets_spec`). `quorumOneKnownReturnsTwelve` is
the first-order readout and `quorumOneKnownNotEleven` its negative twin.

**Re-derived by TACTIC (proof-automation arc phase 2, 2026-08-01)**: the
whole walk chain under `quorumOneKnownFuncSpec` — `wp_ackedIndex_body`
through `wp_oneKnownCall` — is now produced by `go_walk`
(`GoLeanProofs/Tactics/GoWalk.lean`) instead of by hand-enumerated
`iapply`/`isplitl` steps. **No statement changed**; the acceptance is
exactly the two pins already in this file and in `AutomationTargets`: the
`#print axioms` gate below still reads `[propext, Classical.choice,
Quot.sound]` (a tactic-generated term is a kernel term like any other,
and the whole-module sweep at the top of this file sees it), and
`summitStatement_holds : summitStatement_pinned` still type-checks, so
the re-derivation inhabits the same type. A tactic cannot weaken a claim
it does not get to restate.

The declarative reading is now MECHANIZED end to end (2026-07-31,
pre-merge audit finding 5): `isCommittedIndex_unique` proves the spec
determines `r` uniquely and `isCommittedIndex_iff` turns it into the
characterization `IsCommittedIndex c acked r ↔ r = committedIndexRef c
acked`. Before this, uniqueness — the very thing that upgrades "the
machine's answer IS a committed index" to "the machine computes Go's
`CommittedIndex`" — was asserted in `IsCommittedIndex`'s docstring and
proven nowhere. Still UNMECHANIZED, and now marked so at the def: that
etcd's SECOND implementation (`alternativeMajorityCommittedIndex`,
`quick_test.go`) satisfies the spec — it is not modeled in Lean.

Scope, honestly: **n = 1**, so the map range's nondeterminism is
degenerate and the `len(stk) >= n` test takes the reslice branch. The
three-voter walk is the recorded next widening.

`◌ NOT PROVEN` (unchanged, recorded rather than quietly dropped): the
`quorumOneKnownNotEleven_statement` target (`39891ae`, phase 4) — the
UNCONDITIONAL
`¬ GoFuncSpec … (n = 11)` — is not refutable from the triple, because a
`GoTriple` is vacuously true of a program that fails to terminate;
refuting it demands exhibiting a terminating run (a kernel evaluation of
the interpreter over the whole pinned program). The run-conditioned twin
above is what the golden precedent proves, and is what is proven here. -/
example := @GoLean.Quorum.committedIndexRef_oneKnown
example := @GoLean.Quorum.isCommittedIndex_unique
example := @GoLean.Quorum.isCommittedIndex_iff
example := @GoLean.Quorum.isCommittedIndex_oneKnown
example := @GoLean.Quorum.not_isCommittedIndex_oneKnown_11
example := @GoLean.Surface.quorumAckedIndexFuncSpec2
example := @GoLean.Surface.quorumAckedIndexPre_satisfiable
example := @GoLean.Iris.GoldenQuorum.wp_ackedIndexCall
example := @GoLean.Iris.GoldenQuorum.wp_ackedIndex_body
example := @GoLean.Iris.wp_call_enter₂
example := @GoLean.Iris.wp_call_enter_ackedIndexImpl
example := @GoLean.Iris.wp_call_target_next
example := @GoLean.Iris.wp_call_targets_done_arg
example := @GoLean.Iris.wp_call_arg_next
example := @GoLean.Iris.wp_frame_return₂
example := @GoLean.Iris.wp_read₂_store₂_step
example := @GoLean.Surface.sat_sep_insert
example := @GoLean.Surface.quorumOneKnownFuncSpec
example := @GoLean.Surface.quorumOneKnownMeetsSpec
example := @GoLean.Surface.quorumOneKnownReturnsTwelve
example := @GoLean.Surface.quorumOneKnownNotEleven
example := @GoLean.Iris.GoldenQuorum.wp_committedIndex_body
example := @GoLean.Iris.GoldenQuorum.wp_ci_loop_one
example := @GoLean.Iris.GoldenQuorum.wp_committedIndexCall
example := @GoLean.Iris.GoldenQuorum.wp_run_body
example := @GoLean.Iris.GoldenQuorum.wp_oneKnown_body
example := @GoLean.Iris.GoldenQuorum.wp_oneKnownCall
example := @GoLean.Iris.wp_alloc_store_step
example := @GoLean.Iris.wp_alloc_step₃
example := @GoLean.Iris.wp_stmt_op_apply_alloc_store
example := @GoLean.Iris.wp_make_map
example := @GoLean.Iris.wp_make_slice
example := @GoLean.Iris.wp_make_slice_c2
example := @GoLean.Iris.wp_call_enter₂₁
example := @GoLean.Iris.wp_frame_return₁
example := @GoLean.Iris.wp_strict_apply_read
example := @GoLean.Iris.wp_strict_apply_pin
example := @GoLean.Iris.wp_eval_strict_nullary_pin
example := @GoLean.Iris.wp_assign_store_loc
/-- `✓` the golden walk and both its call forms. -/
example := @GoLean.Iris.GoldenSlice.wp_inc_body
example := @GoLean.Iris.GoldenSlice.wp_call_inc_stmt
example := @GoLean.Iris.GoldenSlice.wp_incViaCall_body
example := @GoLean.Iris.GoldenSlice.wp_goldenCall
example := @GoLean.Iris.GoldenSlice.wp_goldenCall_inv
/-- `✓` **THE INDUCTIVE RANGE RULE** (proof-automation arc phase 1,
2026-08-01). `wp_map_iter_inv` — the loop-invariant rule for the
NONDETERMINISTIC key-only map range, and the piece that makes k-voter
(and eventually ∀-config) quorum proofs reachable at all: ONE
generic-iteration obligation over an arbitrary remaining snapshot and an
arbitrary pick, plus an invariant, in place of the `k!` pick orders
`wp_map_iter_next_key` alone would force. Proven by ordinary Nat
induction on `remaining.size` (the snapshot strictly shrinks, so no Löb
is needed — the deterministic analogue `wp_while_inv` does need it).

STATEMENT IS TARGET-FREE (standing over-specialization check): key
variable, key/value types, body, snapshot, environment, continuation and
invariant are all law variables; no quorum name, value or program
fragment appears. RECORDED v1 narrowings, with widening paths in the
law's docstring: key-only iteration (inherited from
`wp_map_iter_next_key`), and normally-completing bodies only —
`break`/`continue` bodies cannot discharge the body premise (a
completeness scope, not a soundness side-condition; `continue` needs one
pure-step law, `break` needs a second exit wand).

TWO WITNESSES, per the arc's explicit requirement that the FIRST one be
non-quorum:

* `wp_map_iter_inv_key_sum_witness` — `for k := range m { sum = sum + k }`
  over an ARBITRARY snapshot of nonnegative `int` keys, with the
  invariant "`sum` holds the total of the entries consumed so far". Its
  guardrail is the corpus case `range/range-map-key-sum` (differential
  PASS, added in the same commit); the body term in the witness is
  HAND-BUILT and says so — it is evidence the premises are jointly
  satisfiable by a real program shape, not a claim about a lowering.
* the QUORUM instance, not a separate theorem but a REWIRING: the n = 1
  summit's voter loop (`wp_ci_loop_one`) now discharges its range
  segment THROUGH this rule, with the body obligation extracted as
  `wp_ci_range_body_one` and an invariant naming the reachable snapshots
  (`#[voter 1]` before, `#[]` after). `quorumOneKnownFuncSpec`'s
  statement and axiom set are unchanged by the rewiring — which is
  exactly the acceptance shape phase 2 will need for `go_walk`. -/
example := @GoLean.Iris.wp_map_iter_inv
example := @GoLean.Iris.wp_map_iter_inv_key_sum_witness
example := @GoLean.Iris.keyIntSum_eraseIdx
example := @GoLean.Iris.keyIntSum_nonneg
example := @GoLean.Iris.int_normalize_of_nonneg_lt
example := @GoLean.Iris.mapIterInvRule
/-- `✓` **The proof-automation arc's phase-0 TARGETS**
(`Specs/AutomationTargets.lean`). Both are now DISCHARGED (phases 3 and
4, 2026-08-01 — see the blocks below):

* `committedIndexAllConfigs_statement` — THE GOAL: for every config and
  acked map, and every heap snapshot pair ENCODING them
  (`EncodesConfig`/`EncodesAcked`), the pinned lowering of the real
  `main.MajorityConfig.CommittedIndex` satisfies `IsCommittedIndex`.
  No SMALL bound on `c.length`, so it covers both sides of
  `if len(stk) >= n`. **DISCHARGED 2026-08-01** by
  `committedIndexAllConfigs`. The statement carries ONE recorded
  correction (phase 4): a `c.length < 2 ^ 63` REPRESENTABILITY
  hypothesis, without which the statement is FALSE rather than unproven
  — at `2 ^ 63` voters the lowering's `n := len(c)` wraps negative in
  Go's `int` and `stk[:n]` panics, which `Progress` counts as stuck. The
  correction is recorded in full at the target's docstring, in the same
  form as the earlier `quorumAckedIndexFuncSpec2_statement` correction.
  The design decision behind the shape (encode the INPUTS in the heap and
  speak about the METHOD, rather than quantify over a synthesized driver
  family) is recorded in the module docstring and the arc build log.
* `quorumThreeAllFuncSpec_statement` — the 3-voter rung. **DISCHARGED
  2026-08-01** by `quorumThreeAllFuncSpec`; the statement is unchanged.
  `quorumThreeAllNotTwelve_statement` (its UNCONDITIONAL negative twin)
  stays a target and carries the same honesty note as
  `quorumOneKnownNotEleven_statement`: an unconditional refutation needs
  a terminating run exhibited, so it is a target, not a corollary. The
  run-conditioned twin `quorumThreeAllNotTwelve` IS proven.

Non-vacuity of the TARGETS themselves is pinned in the same file: an
encoding is exhibited (`encodesConfig_three`), the value the 3-voter rung
must produce is computed (`committedIndexRef_threeAll`, `rfl`) and
upgraded to the spec (`isCommittedIndex_threeAll`) with two negative
twins; and the shape traps that made an earlier statement FALSE rather
than unproven are pinned by `rfl` against the lowering
(`committedIndex_arity_in_pin`, `committedIndex_types_in_pin` —
the arity mismatch class of the first `GoFuncSpec2` statement).

`summitStatement_pinned`/`summitStatement_holds` are the phase-2
ACCEPTANCE criteria as checkable facts: the `go_walk` re-derivation must
inhabit the SAME statement, and the axiom gate above must still read the
classical trio. No line-count assertion is encoded — a budget is not a
correctness property. -/
example := @GoLean.Quorum.committedIndexAllConfigs_statement
example := @GoLean.Quorum.encodesConfig_three
example := @GoLean.Quorum.committedIndexRef_threeAll
example := @GoLean.Quorum.isCommittedIndex_threeAll
example := @GoLean.Quorum.not_isCommittedIndex_threeAll_12
example := @GoLean.Quorum.not_isCommittedIndex_threeAll_5
example := @GoLean.Surface.quorumThreeAllFuncSpec_statement
example := @GoLean.Surface.quorumThreeAllNotTwelve_statement
example := @GoLean.Surface.committedThreeAll_in_pin
example := @GoLean.Surface.committedIndex_arity_in_pin
example := @GoLean.Surface.committedIndex_types_in_pin
example := @GoLean.Surface.summitStatement_pinned
example := @GoLean.Surface.summitStatement_holds
example := @GoLean.Iris.GoldenQuorum.wp_ci_range_body_one
/-- `✓` **THE 3-VOTER RUNG — proof-automation arc phase 3, 2026-08-01.**
`quorumThreeAllFuncSpec` DISCHARGES the phase-0 target
`quorumThreeAllFuncSpec_statement` (the `theorem … : <the def>` IS the
statement-identity check): etcd's own `committedThreeAll` driver —
`MajorityConfig{1,2,3}` with `mapAckIndexer{1:12, 2:5, 3:6}` — returns
`6` over the PINNED lowering, at `GoFuncSpec` strength.
`quorumThreeAllMeetsSpec` restates it with the DECLARATIVE quorum spec
(`IsCommittedIndex [1,2,3] ackedThreeAll`); `quorumThreeAllReturnsSix` is
the first-order readout and `quorumThreeAllNotTwelve` its
run-conditioned negative twin (`12`, the largest acked index — the answer
a "returns something a voter acked" bug would give).

WHAT IS NEW HERE, and why it is not "n = 1 with bigger numbers":

* **The range costs ONE generic iteration.** At n = 3 there are `3! = 6`
  iteration orders. `wp_ci_loop` — stated for an ARBITRARY voter list
  `ks₀` and an arbitrary acked function `ack`, so it is the n-voter law,
  not the 3-voter one — discharges the whole range through
  `wp_map_iter_inv` with the invariant
  `∃ ks filled, ⌜rem = cfgSnapshot ks ∧ ks ⊆ ks₀ ∧ (ks.map ack ++ filled) ~ ks₀.map ack⌝ ∗ …`.
  The single `List.Perm` IS the order-insensitivity: what is still to
  come plus what has been written is the whole multiset, and nothing says
  in which order `filled` was built. No iteration order is enumerated
  anywhere in this file.
* **The body is a general law.** `wp_ci_range_body` is one iteration of
  `majority.go`'s fill loop at an ARBITRARY voter id, an ARBITRARY acked
  index, an ARBITRARY `AckedIndexer` snapshot (the lookup's answer is the
  `hpair` premise) and an ARBITRARY scratch-array shape
  (`zeros`/`filled`/`trail` over any backing length `cap`, any slice
  length). It writes at a SYMBOLIC index — the first walk in the project
  to do so.
* **The sort is order-blind.** After the loop the array holds a
  permutation of `[12,5,6]` and which one is genuinely undetermined.
  `sortLe_pairs_eq_of_perm` (the machine's structural `sortLe` at the
  `(Int × IntKind)` comparison, antisymmetric on elements of one kind;
  since the de-WF restructure 2026-08-03 — the mergeSort twins remain for
  the math layer) collapses that to one transition, so the six orders
  never reach `applyStmtOp`.

OVER-SPECIALIZATION CHECK, per new law. `Laws/Values.lean` is entirely
TARGET-FREE — `arraySet_middle`/`arrayGet_middle` (positional read/write
at any prefix length), `normalizeArrayForTy_int`/
`normalizeValueForTy_intArray` (any kind, any fuel, any state),
`int_normalize_of_range` (any `Int` in range),
`eq_of_perm_of_pairwise`/`mergeSort_eq_of_perm` (any element type, any
comparison) — no program, lowering, config or acked value occurs in any
statement. `storeLoc_stk_fill` is about a fill loop over any array, at
any position. The two WALK laws (`wp_ci_range_body`, `wp_ci_loop`) name
the pinned lowering's statements — they are walks OF the target and
cannot avoid that — but their DATA is fully quantified: no voter count,
no config, no acked value and no `n` occurs in either statement. The
3-voter numbers enter only at the instantiation sites
(`wp_committedIndex_body_three` onward).

`◌ NOT PROVEN` (recorded, not quietly dropped): the UNCONDITIONAL
`quorumThreeAllNotTwelve_statement`, for the reason the whole family
carries — a `GoTriple` is vacuously true of a non-terminating program, so
refuting it demands EXHIBITING a terminating run. (THE ARC GOAL,
`committedIndexAllConfigs_statement`, is DISCHARGED in phase 4 — the
block below.) -/
example := @GoLean.Surface.quorumThreeAllFuncSpec
example := @GoLean.Surface.quorumThreeAllMeetsSpec
example := @GoLean.Surface.quorumThreeAllReturnsSix
example := @GoLean.Surface.quorumThreeAllNotTwelve
example := @GoLean.Iris.GoldenQuorum.wp_ci_loop
example := @GoLean.Iris.GoldenQuorum.wp_ci_range_body
example := @GoLean.Iris.GoldenQuorum.wp_committedIndex_body_three
example := @GoLean.Iris.GoldenQuorum.wp_ci_fitIf_three
example := @GoLean.Iris.GoldenQuorum.wp_ci_tail_three
example := @GoLean.Iris.GoldenQuorum.wp_committedIndexCall_three
example := @GoLean.Iris.GoldenQuorum.wp_run_body_three
example := @GoLean.Iris.GoldenQuorum.wp_threeAll_body
example := @GoLean.Iris.GoldenQuorum.wp_threeAllCall
example := @GoLean.Iris.GoldenQuorum.wp_ackedIndex_body_entries
example := @GoLean.Iris.wp_map_lookup_ackedIndex_entries
example := @GoLean.Iris.mapLookupValue_singleton
example := @GoLean.Iris.arraySet_middle
example := @GoLean.Iris.arrayGet_middle
/-- `✓` **THE ∀-CONFIG THEOREM — proof-automation arc phase 4,
2026-08-01.** `committedIndexAllConfigs` DISCHARGES the arc's GOAL
(`committedIndexAllConfigs_statement`, phase 0; the `theorem … : <the
def>` IS the statement-identity check): for EVERY voter list, EVERY acked
map and every heap snapshot pair encoding them, the pinned lowering of
the real `main.MajorityConfig.CommittedIndex` — called on a heap-carried
receiver and a heap-carried `AckedIndexer` — delivers a value satisfying
the DECLARATIVE quorum spec `IsCommittedIndex`, at `GoSpec` strength.
`committedIndexAllReturnsSix` reads it out first-order at the 3-voter
encoding (also its non-vacuity witness: an admissible initial state
exists) and `committedIndexAllNotTwelve` is the run-conditioned negative
twin; `committedIndexAll_refutes_wrong` is the ∀-quantified refutation
(the postcondition pins the answer uniquely, via
`isCommittedIndex_iff`).

WHAT IS NEW HERE, over the 3-voter rung:

* **BOTH branches of `if len(stk) >= n`** (`wp_ci_fitIf_all`): the
  on-stack `[7]uint64` reslice at `n ≤ 7` and the `make([]uint64, n)`
  allocation above it. The scratch array's ADDRESS and CAPACITY become
  existential and nothing downstream knows which branch ran.
* **Voters that never reported** (`wp_ci_range_body_miss`,
  `wp_ci_loop_all`): `AckedIndex` answers `(0, false)`, the `if` is not
  taken and NEITHER the slot NOR the fill index moves — so the missing
  voters' zeros end up in the LOW slots, which is exactly `ackedOrZero`.
  The invariant carries the zero count explicitly (`zeros + filled.length
  = n`, `ks.length ≤ zeros`) and its `List.Perm` is over the REPORTED
  values (`reduceOption`).
* **`slices.Sort` at a SYMBOLIC length** (`applyStmtOp_sortSlice_ints`):
  the machine's two `for i in [:len]` loops discharged by induction
  (`forIn_range'_inv`) rather than unrolled, with the sort's ANSWER a
  premise — any sorted permutation of the loaded values IS the answer
  (`sortLe_pairs_eq_of_perm` at the machine's `sortLe`; the reference's
  `sortAsc` stays mergeSort-based on the math side).
* **The encoding bridge** (`encodesConfig_cfgSnapshot`,
  `encodesAcked_lookup`): the map SNAPSHOT predicates become the loop
  law's `cfgSnapshot` and per-voter lookup answers — the latter through
  `mapLookupValue_hit`/`_miss`, the map-entry SEARCH at a symbolic entry
  array (`forIn_find_none`/`forIn_find_some`).

OVER-SPECIALIZATION CHECK, per new law. `Laws/Values.lean` and the new
`Laws/StmtOps.lean` material (né `Laws/QuorumOps.lean`) are TARGET-FREE by inspection:
`forIn_range'_yield`/`_inv` (any monad-free body, any invariant),
`applyStmtOp_sortSlice_ints` (any int kind, any length, any tail),
`buildDefaultArrayValue_int`, `checkSliceBounds_prefix`,
`sortLe_pairs_eq_of_perm` (and the retained math-layer
`mergeSort_pairs_eq_of_perm`), `perm_replicate_reduceOption`,
`perm_eraseIdx_reduceOption`, `mem_reduceOption_map`,
`list_split_first_match`, `forIn_find_none`/`_some`,
`mapLookupValue_hit`/`_miss` (any int key KIND — the `{kind : IntKind}`
axis was generalized at the 2026-08-01 pre-merge audit response from a
`.uint64` pin, which was exactly the target's `map[uint64]Index` key type
and which nothing in the proofs required; same for
`mapLookupValue_singleton`) — no program, lowering, config or acked
value occurs in any statement. The WALK laws (`wp_ci_fitIf_all`,
`wp_ci_range_body_miss`, `wp_ci_loop_all`, `wp_ci_tail_all`,
`wp_committedIndex_body_all`, `wp_committedIndexCall_all`) name the
pinned lowering's statements — they are walks OF the target — but their
DATA is fully quantified: no voter count, no config and no acked value
occurs; `7` appears only where `majority.go` writes it (the on-stack
array's length), and the ONE numeric constant in a statement,
`18446744073709551615`, is `math.MaxUint64` from the source. -/
example := @GoLean.Surface.committedIndexAllConfigs
example := @GoLean.Surface.committedIndexAllReturnsSix
example := @GoLean.Surface.committedIndexAllNotTwelve
example := @GoLean.Surface.committedIndexAll_refutes_wrong
example := @GoLean.Iris.GoldenQuorum.wp_ci_fitIf_all
example := @GoLean.Iris.GoldenQuorum.wp_ci_range_body_miss
example := @GoLean.Iris.GoldenQuorum.wp_ci_loop_all
example := @GoLean.Iris.GoldenQuorum.wp_ci_tail_all
example := @GoLean.Iris.GoldenQuorum.wp_committedIndex_body_all
example := @GoLean.Iris.GoldenQuorum.wp_committedIndex_body_empty
example := @GoLean.Iris.GoldenQuorum.wp_committedIndexCall_all
example := @GoLean.Iris.applyStmtOp_sortSlice_ints
example := @GoLean.Iris.forIn_range'_inv
example := @GoLean.Iris.forIn_find_none
example := @GoLean.Iris.forIn_find_some
example := @GoLean.Iris.mapLookupValue_hit
example := @GoLean.Iris.mapLookupValue_miss
example := @GoLean.Iris.mergeSort_pairs_eq_of_perm
example := @GoLean.Iris.perm_replicate_reduceOption
example := @GoLean.Iris.perm_eraseIdx_reduceOption
example := @GoLean.Quorum.encodesConfig_cfgSnapshot
example := @GoLean.Quorum.encodesAcked_lookup
example := @GoLean.Quorum.sortedAcked_perm
example := @GoLean.Quorum.sortedAcked_get
example := @GoLean.Iris.normalizeListWith_id
example := @GoLean.Iris.normalizeValueForTy_intArray
example := @GoLean.Iris.int_normalize_of_range
example := @GoLean.Iris.eq_of_perm_of_pairwise
example := @GoLean.Iris.mergeSort_eq_of_perm
example := @GoLean.Iris.mergeSort_intKind_eq_of_perm
example := @GoLean.Quorum.storeLoc_stk_fill
example := @GoLean.Quorum.perm_eraseIdx_append
example := @GoLean.Quorum.sortLe_three_all
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
  the differential (zero drift on the full corpus — 872 cases as of
  2026-07-31; the figure said "718" from 2026-07-23 until the final
  pre-merge audit's finding 14 caught it four corpus growths later) is
  the operational evidence, and the queued panic assembly is the
  proof-side gap on record.
-/

end GoLean.Iris.Audit
