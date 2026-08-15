import Lean
import GoLeanProofs
import GoLean
import Audit.Kit
import Audit.Reverse
import Audit.Gcd
import Audit.MinMax
import Audit.InsertionSort
import Audit.BinSearch
import Audit.WordCount
import Audit.Histogram
import Audit.PowMod
import Audit.DotProduct

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

**RELATION-freedom (sem-adequacy arc slice 4, 2026-08-04)**: the gate
additionally forbids the Prop-level transition relation from any
designated statement closure — the arc's deletion test extends to it
(the relation is proof infrastructure exactly like Iris; headline
statements speak `stepFn`/`execStmt` only). The relation lives INSIDE
`GoLean.GoCore.Machine` (same module as `stepFn`'s premise functions),
so module-of-origin cannot discriminate; the check is by constant NAME
instead: an explicit forbidden set — the inductives
`GoLean.GoCore.Machine.Step` / `GoLean.GoCore.Machine.Steps` — plus
everything namespaced under them (constructors, recursors, `casesOn`/
`below`/`noConfusion` auxiliaries: name-prefix match, which cannot
confuse `Step` with `Steps` because prefixes match whole components).
Reaching one is exactly eviction debt: reformulate the statement, never
whitelist.

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
  -- The relation's defining constants (see the docstring's
  -- RELATION-freedom block): the two inductives, matched with everything
  -- in their namespaces. `Name.isPrefixOf` matches whole components, so
  -- `…Machine.Step` does NOT match `…Machine.Steps` (nor `…Machine.stepFn`).
  -- (Channels arc slice 2, 2026-08-07: the pool relations `StepE` — the
  -- spawn-component per-goroutine relation — and `StepM` join the
  -- forbidden set: they are proof infrastructure exactly like
  -- `Step`/`Steps`; headline statements speak `stepMulti`/`execProg`.)
  -- (Channels arc slice 3: the NPDRF statement layer's relations join —
  -- `StepMFine`/`StepsMFine` are the reduction obligation's proof
  -- infrastructure, and `StepsM` its coarse closure; headline statements
  -- keep speaking `stepMulti`/`execProg`.)
  let forbiddenRoots : List Name :=
    [`GoLean.GoCore.Machine.Step, `GoLean.GoCore.Machine.Steps,
     `GoLean.GoCore.Machine.StepE, `GoLean.GoCore.Machine.StepM,
     `GoLean.GoCore.Machine.StepMFine, `GoLean.GoCore.Machine.StepsM,
     `GoLean.GoCore.Machine.StepsMFine,
     -- Channels arc slice 5: the CONCURRENT Iris Language's per-thread
     -- relation (LangC.lean) — proof infrastructure like its siblings;
     -- it lives in a GoLeanProofs module (module-of-origin cannot flag
     -- it), so it joins the name-based forbidden set.
     `GoLean.Iris.StepEC, `GoLean.Iris.GoPrimStepC]
  let isRelation : Name → Bool := fun n =>
    forbiddenRoots.any (fun r => r == n || r.isPrefixOf n)
  -- FAIL-CLOSED existence check on the forbidden set itself (S5 audit
  -- response): the roots are raw name literals — a rename would
  -- silently drop a relation from the check (the 2026-07-23
  -- purity-scan rename-hole class). Mirror the designated list's
  -- missing-name guard: every root must resolve in the environment.
  for r in forbiddenRoots do
    let some _ := env.find? r
      | throwError "statement-TCB gate: forbidden relation root {r} is \
          MISSING (renamed without re-pointing the gate?)"

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
  -- (Sem-adequacy slice 5, 2026-08-04: the run-conditioned negative twins
  -- were RENAMED `*Run` — their statements are unchanged — and the clean
  -- names now belong to the NEW UNCONDITIONAL twins discharging the
  -- phase-4 `*_statement` targets (`Specs/TotalPins.lean`). Both forms
  -- stay designated: the run-conditioned twins remain the readouts'
  -- negative rung; the unconditional ones are the new headline claims.)
  -- (Audit response 2026-08-04: the eight slice-5 headline deliverables
  -- — the four per-seed `<pin>Terminates` and the four normal-pinned
  -- `<pin>TotalReadout` forms — were shipped WITHOUT designation; added
  -- here, to Challenge/Solution, and to judge-config.json. 25 → 33.)
  let designated : List Name := [
    ``GoLean.Surface.quorumOneKnownFuncSpec,
    ``GoLean.Surface.quorumOneKnownMeetsSpec,
    ``GoLean.Surface.quorumOneKnownReturnsTwelve,
    ``GoLean.Surface.quorumOneKnownNotElevenRun,
    ``GoLean.Surface.quorumOneKnownNotEleven,
    ``GoLean.Surface.quorumThreeAllFuncSpec,
    ``GoLean.Surface.quorumThreeAllMeetsSpec,
    ``GoLean.Surface.quorumThreeAllReturnsSix,
    ``GoLean.Surface.quorumThreeAllNotTwelveRun,
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
    ``GoLean.Surface.goldenTerminates,
    ``GoLean.Surface.recoverTerminates,
    ``GoLean.Surface.quorumOneKnownTerminates,
    ``GoLean.Surface.quorumThreeAllTerminates,
    ``GoLean.Surface.goldenTotalReadout,
    ``GoLean.Surface.recoverTotalReadout,
    ``GoLean.Surface.quorumOneKnownTotalReadout,
    ``GoLean.Surface.quorumThreeAllTotalReadout,
    ``GoLean.Quorum.committedIndexRef_meets_spec,
    -- Channels arc slice 2 (2026-08-07): the fork/join KERNEL witnesses
    -- over the ThreadPool carrier (`execProg`) — pinned-stream rung-1
    -- readouts (canonical/adversarial/alternating schedules complete
    -- .normal with the pinned value; the all-asleep program classifies
    -- .deadlock). The full GoSpecC witness is the slice-5 deliverable
    -- (design of record's slice plan); the COMPARATOR landmark for this
    -- designated-set change was DISCHARGED at the arc-final audit
    -- response (2026-08-08): scripts/comparator-judge PASS — 44
    -- theorems certified in 123 s, fresh clone @ c526fb7c7f9e (run
    -- record: the comparator-judge sprint doc's landmark log; never
    -- run as part of ci).
    ``GoLean.Surface.forkJoinStreamCanonical,
    ``GoLean.Surface.forkJoinStreamAdversarial,
    ``GoLean.Surface.forkJoinStreamAlternating,
    ``GoLean.Surface.forkJoinDeadlockCanonical,
    ``GoLean.Surface.forkJoinDeadlockAdversarial,
    -- Channels arc slice 5 (2026-08-07): the ∀-SCHEDULE fork/join
    -- witnesses (the pool ∀-streams kernel checker discharges the
    -- `∀ ch` quantifier — every schedule + latitude stream completes
    -- the rendezvous at .normal/42; deadlock-freedom and
    -- race-REFUSAL-freedom (the detector never refuses; scoped by its
    -- recorded U1–U3 under-approximations) first-order corollaries;
    -- the TerminatesNormallyC instance), and
    -- the GoSpecC inhabitation witness `goldenSpecC` (the
    -- conservation-transfer lane; the genuinely-spawning
    -- frame-quantified instance is the recorded successor debt —
    -- Surface.lean witness-status note). The pinned-stream slice-2
    -- witnesses above stay byte-identical (growth by extension). The
    -- Comparator landmark for this designated-set change was
    -- DISCHARGED 2026-08-08 (44/44 in 123 s @ c526fb7c7f9e — see the
    -- slice-2 comment above and the sprint doc's landmark log).
    ``GoLean.Surface.forkJoinAllSchedules42,
    ``GoLean.Surface.forkJoinNoDeadlock,
    ``GoLean.Surface.forkJoinNoRace,
    ``GoLean.Surface.forkJoinTerminatesNormallyC,
    ``GoLean.Surface.goldenSpecC,
    -- S5 audit response: the pool-carrier first-order readout twin of
    -- `goldenSpecC` (the rung-2 readout on the judgment's own carrier
    -- — the audit found the golden readouts were sequential-carrier
    -- only). 43 → 44.
    ``GoLean.Surface.goldenReturnsTwoC,
    -- Spec-parity arc D3 curation (USER RULING 2026-08-10; the arc's
    -- designated-set change, 44 → 48): the two candidate pairs join
    -- in their FUEL-FREE forms only — the class-1 exemplar's GoSpecC
    -- triple + pool readout twin (upstream wp_testCompareNilToNil
    -- Qed) and the class-3 flagship's ∃N-∀fuel≥N kernel certificate +
    -- ∀-schedule verdict readout (upstream wp_DSPExample Qed). The
    -- fuel-based kernel-evidence siblings (dspCert400 &c.) stay
    -- UNDESIGNATED per the ruling — proof evidence, nothing more.
    -- Statement defs hoisted to the def-only
    -- Specs/GooseParityTargets.lean (F4 discipline); the Comparator
    -- landmark for this designated-set change is the coordinator's
    -- post-merge-prep step (never part of ci).
    ``GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC,
    ``GoLean.ImportedGoose.SemanticsNil.compareNilToNilReadoutC,
    ``GoLean.ImportedGoose.ChannelActris.dspCert,
    ``GoLean.ImportedGoose.ChannelActris.dspAllSchedules,
    -- Examples phase-2 arc end (2026-08-14): the VERIFIED-EXAMPLES
    -- GALLERY headlines — the public object of agreement
    -- (`docs/verified-examples.md`). Designation was deferred from the
    -- foundation merge BY RULING (swapping three statements then
    -- designating pays the comparator landmark once, not twice); the
    -- swaps are final, so they join here. 48 → 56.
    --
    -- USER RULING (2026-08-14, verbatim): "this is basically saying
    -- that *in order to state the theorems* we need definitions of what
    -- fib and whatever mean. That's in the TCB necessarily. So what
    -- we're doing here is hoisting things into the Comparator set which
    -- are definitionally part of the TCB. This all seems fine, go
    -- ahead."
    --
    -- THE SET IS WHAT THE GALLERY QUOTES VERBATIM AS A HEADLINE — the
    -- eight `**The theorem(s)**` blocks, enumerated from the doc rather
    -- than from memory. Supporting material the gallery only NAMES in
    -- prose is deliberately NOT designated: the `_readout` twins (no
    -- readout STATEMENT is quoted anywhere; two axiom-pin LINES are,
    -- which is a different gate), the `_v1` pairs, the `_framed`
    -- companions, `maxCount_total_canonical` and `wordcount_empty_ok`.
    -- `maxCount_total_canonical` carries an extra reason: it is stated
    -- in run-internal vocabulary (`wcEnv`/`wcSeed`/`wcCall`), so
    -- designating it would pull proof scaffolding into the Challenge's
    -- trusted closure — the layering doctrine's exact prohibition.
    --
    -- Statement vocabulary hoisted to the def-only
    -- `GoLeanProofs/Examples/Targets.lean` (F4 discipline; that file's
    -- docstring records why it sits under `Examples/` and not `Specs/`
    -- — ci's import-direction lint forbids `Examples/*` from importing
    -- `Specs/*` with "Exceptions: NONE", and siting it here keeps that
    -- lint intact instead of punching a hole in it). The Comparator
    -- landmark for this designated-set change was DISCHARGED 2026-08-14:
    -- scripts/comparator-judge PASS — 56 theorems certified in 308 s,
    -- fresh clone @ e42020397648 (run record + the wrapper's
    -- dot-in-path finding: the comparator-judge sprint doc's landmark
    -- log; never run as part of ci).
    ``GoLean.Examples.Fib.fib_ok,
    ``GoLean.Examples.Fib.fib_total,
    ``GoLean.Examples.Gcd.gcd_ok,
    ``GoLean.Examples.Reverse.reverse_ok,
    ``GoLean.Examples.MinMax.minmax_ok,
    ``GoLean.Examples.BinSearch.search_ok,
    ``GoLean.Examples.InsertionSort.isort_ok,
    ``GoLean.Examples.WordCount.wordcount_ok]
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
      if isRelation c then
        -- Relation constant reached: report with the dependency chain and
        -- stop at the boundary (no recursion into the relation — one
        -- constant is the proof of the violation).
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
          s!"  {t}: statement closure reaches RELATION constant {c} \
            (Step/Steps are proof infrastructure — sem-adequacy slice 4)\
            \n    chain: {chain}"
        continue
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
      all statement closures Iris-free and relation-free"
    for l in lines do
      IO.println l
  else
    throwError "statement-TCB gate FAILED — a headline STATEMENT depends on \
      Iris or the relation (the deletion test; reformulate the statement, \
      do not whitelist):\n\
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

-- The ThreadPool correspondence + conservation (channels arc slice 2) —
-- constructive like the sequential kit.
/-- info: 'GoLean.GoCore.Machine.stepMulti_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepMulti_sound
/-- info: 'GoLean.GoCore.Machine.execProg_single_eq_execStmt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execProg_single_eq_execStmt
/-- info: 'GoLean.GoCore.Machine.stepM_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepM_complete

-- The race-detection + NPDRF layer (channels arc slice 3) — the
-- detector's conservation hinge, the proved half of the reduction, and
-- the representative both-mover lemmas. The relation-side pair is
-- constructive; the two mover lemmas inherit Classical.choice from
-- `Heap.lookup_set_ne` (the pre-existing ∀-choices-kit lemma their
-- frame argument reuses), recorded as-is — they are proof
-- infrastructure, not correspondence theorems.
/-- info: 'GoLean.GoCore.Machine.raceUpdate_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.raceUpdate_single
/-- info: 'GoLean.GoCore.Machine.stepM_le_stepMFine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepM_le_stepMFine
/-- info: 'GoLean.GoCore.Machine.reachesM_le_fine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.reachesM_le_fine
/-- info: 'GoLean.GoCore.Machine.storeLoc_root_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.storeLoc_root_frame
/-- info: 'GoLean.GoCore.Machine.loadLoc_after_disjoint_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.loadLoc_after_disjoint_store

-- The fork/join pool kernel witnesses (pinned streams; slice 2).
/-- info: 'GoLean.Surface.forkJoinStreamCanonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinStreamCanonical
/-- info: 'GoLean.Surface.forkJoinStreamAdversarial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinStreamAdversarial
/-- info: 'GoLean.Surface.forkJoinStreamAlternating' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinStreamAlternating
/-- info: 'GoLean.Surface.forkJoinDeadlockCanonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinDeadlockCanonical
/-- info: 'GoLean.Surface.forkJoinDeadlockAdversarial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinDeadlockAdversarial

-- The slice-5 ∀-schedule fork/join witnesses + the GoSpecC
-- inhabitation witness (channels arc slice 5). The ∀-stream family
-- inherits Classical.choice through the checker soundness kit's
-- sequential dependencies; all within the allowlist.
/-- info: 'GoLean.Surface.forkJoinAllSchedules42' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinAllSchedules42
/-- info: 'GoLean.Surface.forkJoinNoDeadlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinNoDeadlock
/-- info: 'GoLean.Surface.forkJoinNoRace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinNoRace
/-- info: 'GoLean.Surface.forkJoinTerminatesNormallyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.forkJoinTerminatesNormallyC
/-- info: 'GoLean.Surface.goldenSpecC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenSpecC
/-- info: 'GoLean.Surface.goldenReturnsTwoC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenReturnsTwoC
-- The spec-parity designated pairs (D3 user ruling 2026-08-10,
-- 44 → 48): the class-1 pair on the spec lane (classical trio), the
-- class-3 certificate constructive, its readout on the checker
-- soundness kit's lane (classical trio).
/-- info: 'GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC
/-- info: 'GoLean.ImportedGoose.SemanticsNil.compareNilToNilReadoutC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.ImportedGoose.SemanticsNil.compareNilToNilReadoutC
/-- info: 'GoLean.ImportedGoose.ChannelActris.dspCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.ImportedGoose.ChannelActris.dspCert
/-- info: 'GoLean.ImportedGoose.ChannelActris.dspAllSchedules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.ImportedGoose.ChannelActris.dspAllSchedules
-- The MultiWf discharge (the slice-2 scaffold's owed preservation) and
-- the pool ∀-streams checker soundness kit.
/-- info: 'GoLean.GoCore.Machine.stepMulti_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepMulti_wf
/-- info: 'GoLean.GoCore.Machine.execProgLoop_ok_of_allStreamsOkPool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execProgLoop_ok_of_allStreamsOkPool
/-- info: 'GoLean.GoCore.Machine.execProgLoop_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execProgLoop_mono
-- The slice-6 fuel-independence pair (constructive): sub-bound
-- truncation classification and checker fuel-monotonicity — what
-- lifts every certificate-backed channel-bundle statement off its
-- shipped literal fuel.
/-- info: 'GoLean.GoCore.Machine.execProgLoop_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execProgLoop_le
/-- info: 'GoLean.GoCore.Machine.stepAllBranchesOk_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepAllBranchesOk_mono
/-- info: 'GoLean.GoCore.Machine.allStreamsOkPool_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.allStreamsOkPool_mono
/-- info: 'GoLean.Surface.goSpecC_of_goSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goSpecC_of_goSpec
/-- info: 'GoLean.GoCore.Machine.step_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_det

-- The non-consuming-select checker refinement (spec-parity slice 4,
-- design note 2026-08-10 §6(b)): `poolThreadOblivious` accepts a
-- select apply exactly when partnerless (`.cellPath`) AND
-- `applySelectCore`-`.done`; witnessed same-commit by the golden
-- select-probe program (positive: every `.done` shape exercised on
-- every schedule) and the two-ready NEGATIVE control (the consuming
-- select is still refused — the fail-closed line held). Same
-- name-existence/deletion-tripwire scope as the block below.
/-- info: 'GoLean.GoCore.Machine.stepFn_select_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepFn_select_done
/-- info: 'GoLean.GoCore.Machine.applySelect_of_done' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.applySelect_of_done
/-- info: 'GoLean.GoCore.Machine.applySelectCore_done_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.applySelectCore_done_inv
/-- info: 'GoLean.Surface.selDoneAllStreamsCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.selDoneAllStreamsCert
/-- info: 'GoLean.Surface.selDoneAllSchedules42' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.selDoneAllSchedules42
/-- info: 'GoLean.Surface.selConsumingRefused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.selConsumingRefused

-- The adequacy family.
/-- info: 'GoLean.Iris.go_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.go_adequacy
/-- info: 'GoLean.Iris.go_heap_adequacy_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.go_heap_adequacy_own
/-- info: 'GoLean.Iris.go_heap_invariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.go_heap_invariance
/-- info: 'GoLean.Iris.adequate_seqn_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.adequate_seqn_nil

-- The CONCURRENT Iris layer (channels arc slice 5, LangC.lean): the
-- pool Language over StepE + the marker strip, the fork rule, and the
-- closed end-to-end pool adequacy witness (a program that SPAWNS,
-- NotStuck for parent and forked child).
/-- info: 'GoLean.Iris.wpC_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wpC_fork
/-- info: 'GoLean.Iris.wpC_spawn_noop_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wpC_spawn_noop_witness
/-- info: 'GoLean.Iris.adequateC_spawn_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.adequateC_spawn_noop

-- THE DECOMPOSED D-LANGUAGE (spec-parity slice 4, LangD.lean — the
-- channels-arc successor debt's pipe, design note 2026-08-10 §§3-4):
-- the per-thread StepDC relation, the pairing SIMULATION (every StepM
-- step is 1-2 erased D-steps; applyPairing_shape is its inversion
-- kit), the run erasure, the pool heap-handover adequacy, THE EXIT
-- (goTripleC_of_wpD — consumes the pairing simulation generically),
-- the ported wpD law kit, and the WITNESS: spawnNoopTripleC, the
-- first frame-quantified GoTripleC on a genuinely SPAWNING program,
-- with its seeded first-order readout (non-vacuity — every
-- InitialSplit premise discharged at the concrete seed). The SAFETY
-- half (ProgressExecC at forall-heap strength; GoSpecC assembly) is the
-- pool-reachability lane's recorded owed instance, NOT silently
-- dropped — slice build log. Same name-existence-tripwire scope as
-- the witness blocks above. (S4 audit round: the block now anchors
-- EVERY public LangD theorem — the five simulation-lane helpers were
-- first left out and the registration sentence overstated the
-- anchor's coverage; and the witness is a PAIR since the round — the
-- run-conditioned readout plus the seeded completion pin
-- spawnNoopTerminatesNormallyC, the goldenTerminates /
-- forkJoinTerminatesNormallyC house idiom.)
/-- info: 'GoLean.Iris.applyPairing_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.applyPairing_shape
/-- info: 'GoLean.Iris.stepM_erasedD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.stepM_erasedD
/-- info: 'GoLean.Iris.execProg_erasedD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.execProg_erasedD
/-- info: 'GoLean.Iris.goD_heap_adequacy_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.goD_heap_adequacy_own
/-- info: 'GoLean.Iris.goTripleC_of_wpD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.goTripleC_of_wpD
/-- info: 'GoLean.Iris.wpD_pure_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wpD_pure_det
/-- info: 'GoLean.Iris.wpD_spawned_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wpD_spawned_strip
/-- info: 'GoLean.Iris.wpD_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wpD_fork
/-- info: 'GoLean.Iris.wpD_spawn_noop_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wpD_spawn_noop_witness
/-- info: 'GoLean.Iris.spawnNoopTripleC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.spawnNoopTripleC
/-- info: 'GoLean.Iris.spawnNoopReadoutC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.spawnNoopReadoutC
/-- info: 'GoLean.Iris.spawnNoopAllStreamsCert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.spawnNoopAllStreamsCert
/-- info: 'GoLean.Iris.spawnNoopTerminatesNormallyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.spawnNoopTerminatesNormallyC
/-- info: 'GoLean.Iris.poolStepD_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.poolStepD_at
/-- info: 'GoLean.Iris.pair_erasedD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.pair_erasedD
/-- info: 'GoLean.Iris.execProgLoop_erasedD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.execProgLoop_erasedD
/-- info: 'GoLean.Iris.arrivalCases_of_nonApply' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Iris.arrivalCases_of_nonApply
/-- info: 'GoLean.Iris.stepDC_shape_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.stepDC_shape_cases

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
/-- info: 'GoLean.Surface.quorumOneKnownNotElevenRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownNotElevenRun
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
/-- info: 'GoLean.Surface.quorumThreeAllNotTwelveRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllNotTwelveRun
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
/-- `✓` the frame exits — `wp_frame_return_int` (a four-step spine walk
since BUG-025/BUG-052: no state side-conditions, one syntactic
env-lookup premise `hres`) and its invariant-opening form, both
consumed by the golden walk. -/
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
example := @GoLean.Iris.wp_call_value_start_witness
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
  `wp_stmt_op_apply_store` — NOTHING existed for `stmtOpK` before this
  file; witnessed by the `sortSlice` walk below (`wp_stmt_op_first` +
  the apply-store core `wp_sort_slice` definitionally IS), the
  `makeSlice` walk (`wp_stmt_op_shift_target`, `wp_make_slice_c2`),
  and the golden mapAssign walks (`wp_stmt_op_shift_plain`, fired via
  the registered `go_walk` table on the pinned `c[1] = struct{}{}` /
  `l[1] = 12` statements).
  (`wp_stmt_op_apply_read_store₂` and its `wp_read_store_step₂` core
  were DELETED at the spec-parity-s1 audit-fix round: after the
  BUG-034 spine migration no `StmtOp` has two target cells — see the
  tombstone in `Laws/StmtOps.lean`;)
- `wp_sort_slice` (the `slices.Sort` extern, one apply step over the
  slice's single backing cell) — witness `wp_sort_slice_srt`, the REAL
  `slices.Sort(srt)` statement on `[3,1,2] ↦ [1,2,3]`;
- `wp_map_lookup` (comma-ok read: one cell read, two written — since
  the BUG-034 spine migration the value-source APPLY step reads and
  the two writes are per-target `storeK` store lifts) — witness
  `wp_map_lookup_ackedIndex`, the REAL `idx, ok := m[id]` of
  `main.mapAckIndexer.AckedIndex`. The earlier recorded divergence (the
  `idx` cell declared `uint64` where the lowering declares
  `main.Index`) is CLOSED by the `σ.types` pin: the witness now names the
  faithful `.defined main.Index` cell;
- `wp_map_range_snapshot` (+ the nil form) — the state-reading step
  feeding `Laws/Range`'s nondeterministic `mapIterK` law; witness
  `wp_map_range_snapshot_committed` on the REAL voter loop. (Ledger
  update, sub-branch audit 2026-08-04: the law gained the snapshot
  self-normalization premise `hnorm` — the law-side twin of the
  SEMANTICS' own snapshot-time validation, sem-adequacy slice 3 — and
  the committed witness now PROPAGATES that premise to its callers,
  who discharge it at pinned data by `decide +kernel` and at symbolic
  voter lists from their `hnormk` facts; both discharge shapes are in
  the walk files, so the premise is exhibited satisfiable, not just
  forwarded.)

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

/-! ### sem-adequacy slice 3: the legitimacy invariant and the
stream-obliviousness kit (2026-08-04). The SEMANTICS gained the mapRange
snapshot-time self-normalization check (`mapRangeSnapshotEntries`,
differential-validated 873/873); `MachineWf` is the legitimacy invariant
(locs bounded + in-flight snapshots typed) with per-rule preservation;
the kit transports relation-Progress to the interpreter-level
`ProgressExec`. Axiom pins + deletion-guard references: -/
/-- info: 'GoLean.GoCore.Machine.step_preserves_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_preserves_wf
/-- info: 'GoLean.GoCore.Machine.step_complete_any_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_complete_any_wf
/-- info: 'GoLean.GoCore.Machine.execStmtLoop_ok_or_fuelOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execStmtLoop_ok_or_fuelOut
/-- info: 'GoLean.Surface.progressExec_of_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.progressExec_of_progress
/-- info: 'GoLean.Surface.goSpecT_terminates_and_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goSpecT_terminates_and_post
example := @GoLean.GoCore.Machine.applyStmtOp_ok_any_ch_wf
example := @GoLean.GoCore.Machine.execStmt_mono
example := @GoLean.Surface.Terminates
example := @GoLean.Surface.ProgressExec
example := @GoLean.Surface.GoSpecT
-- The CONCURRENT statement notions (channels arc slice 2; slice 5:
-- no longer an unwitnessed scaffold trio — `goldenSpecC` inhabits
-- `GoSpecC` via the conservation transfer, and the fork/join
-- ∀-schedule family discharges the `∀ ch` quantifier at the seed;
-- the frame-quantified spawning instance is the recorded debt in
-- Surface.lean's witness-status note).
example := @GoLean.Surface.GoTripleC
example := @GoLean.Surface.ProgressExecC
example := @GoLean.Surface.GoSpecC
example := @GoLean.Surface.goSpecC_of_goSpec
example := @GoLean.Surface.TerminatesNormallyC
example := @GoLean.Surface.goldenSpecC
example := @GoLean.Surface.forkJoinAllSchedules42
example := @GoLean.Surface.forkJoinTerminatesNormallyC
-- The pool ∀-streams checker kit (slice 5) and the MultiWf discharge —
-- deletion anchors: the checker, its soundness/obliviousness hinges,
-- the fuel-mono lift, and the preservation theorem the slice-2
-- scaffold owed.
example := @GoLean.GoCore.Machine.allStreamsOkPool
example := @GoLean.GoCore.Machine.execProgLoop_ok_of_allStreamsOkPool
example := @GoLean.GoCore.Machine.stepThread_oblivious
example := @GoLean.GoCore.Machine.raceUpdate_oblivious
example := @GoLean.GoCore.Machine.poolThreadOblivious_sel
example := @GoLean.GoCore.Machine.execProgLoop_mono
-- Slice 6 (fuel-independence lift): sub-bound classification + the
-- checker's fuel-monotonicity pair.
example := @GoLean.GoCore.Machine.execProgLoop_le
example := @GoLean.GoCore.Machine.stepAllBranchesOk_mono
example := @GoLean.GoCore.Machine.allStreamsOkPool_mono
example := @GoLean.GoCore.Machine.stepMulti_wf
example := @GoLean.GoCore.Machine.applyPairing_wf
example := @GoLean.GoCore.Machine.resumeThread_wf
example := @GoLean.GoCore.Machine.spawnStep_wf
example := @GoLean.GoCore.Machine.stepThread_wf
-- The NPDRF reduction obligation's statement layer (channels arc slice
-- 3; scaffold — a Prop-valued DEFINITION in DRAFT form, REFUTABLE as
-- written per NPDRF.lean obstruction 4: nothing may cite it, not even
-- as a proof target, until the recorded weakening decision; marking
-- refreshed at the S3 convergence response — the earlier "awaiting
-- proof" wording understated this): deletion/rename anchors so the
-- recorded proof debt cannot silently drift.
example := @GoLean.GoCore.Machine.NPDRFReduction
example := @GoLean.GoCore.Machine.RacyFine
example := @GoLean.GoCore.Machine.ReachesM
example := @GoLean.GoCore.Machine.ReachesMFine
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

/-! ### sem-adequacy slices 4+5: the statement re-land (2026-08-04).
Slice 4 — relation eviction: `GoSpec := GoTriple ∧ ProgressExec`
(interpreter-side safety; the relation-quantified progress is the
PROOF-layer `ProgressRel`, transported by `goSpec_of_triple_progressRel`),
`GoInvariant` over executable reachability (`ReachableExec`/`stepFnIter`,
transport `stepFnIter_sound`/`steps_of_reachableExec`),
`InitialSplit.bounded` removed (redundant under `wf`;
`InitialSplit.heapBounded` is the derivation), and the statement-TCB gate
above enforces relation-freedom by forbidden constant names.
Slice 5 — the ∀-streams termination checker (`allStreamsOk` +
`stepFn_oblivious` + `execStmtLoop_ok_of_allStreamsOk`, MachineSound):
kernel-checked `Terminates` for all four pinned programs (stream
quantifier discharged by branching the mapIter picks), the per-seed
total forms, and the two UNCONDITIONAL negative twins discharging their
phase-4 `_statement` targets. Axiom pins + deletion-guard references: -/
/-- info: 'GoLean.GoCore.Machine.stepFnIter_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepFnIter_sound
/-- info: 'GoLean.GoCore.Machine.stepFn_oblivious' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.stepFn_oblivious
/-- info: 'GoLean.GoCore.Machine.execStmtLoop_ok_of_allStreamsOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.execStmtLoop_ok_of_allStreamsOk
/-- info: 'GoLean.Surface.goldenTerminates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenTerminates
/-- info: 'GoLean.Surface.recoverTerminates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.recoverTerminates
/-- info: 'GoLean.Surface.quorumOneKnownTerminates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownTerminates
/-- info: 'GoLean.Surface.quorumThreeAllTerminates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllTerminates
/-- info: 'GoLean.Surface.quorumOneKnownNotEleven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownNotEleven
/-- info: 'GoLean.Surface.quorumThreeAllNotTwelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllNotTwelve
example := @GoLean.Surface.ReachableExec
example := @GoLean.Surface.steps_of_reachableExec
example := @GoLean.Surface.InitialSplit.heapBounded
example := @GoLean.Surface.goSpec_of_triple_progressRel
example := @GoLean.GoCore.Machine.allStreamsOk
example := @GoLean.GoCore.Machine.execStmtLoop_step
example := @GoLean.GoCore.Machine.stepFn_mapIter_pick

/-! ### Audit response 2026-08-04 (pre-merge, this branch): the
`.normal` pin. `ProgressExec`'s success disjunct — and with it
`execStmtLoop_ok_or_fuelOut`'s — is pinned to the `.normal` terminal
(the ∃-outcome form silently accepted top-level `.returned`/`.broke`/
`.continued` completions the relation-Progress form rejects; the three
`step_*_stop_elim` lemmas prove no relation rule steps from an
unwound-`.stop` configuration). The four `<pin>TotalReadout` forms are
STRENGTHENED to normal-pinned completion (`TerminatesNormally` =
`Terminates` × `ProgressExec` at the seeded frameless split,
`terminatesNormally_of_progressExec`), and all eight slice-5 headline
deliverables are designated above. Axiom pins + deletion guards: -/
/-- info: 'GoLean.GoCore.Machine.step_returning_stop_elim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_returning_stop_elim
/-- info: 'GoLean.GoCore.Machine.step_breaking_stop_elim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_breaking_stop_elim
/-- info: 'GoLean.GoCore.Machine.step_continuing_stop_elim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.GoCore.Machine.step_continuing_stop_elim
/-- info: 'GoLean.Surface.goldenTotalReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.goldenTotalReadout
/-- info: 'GoLean.Surface.recoverTotalReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.recoverTotalReadout
/-- info: 'GoLean.Surface.quorumOneKnownTotalReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumOneKnownTotalReadout
/-- info: 'GoLean.Surface.quorumThreeAllTotalReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.quorumThreeAllTotalReadout
example := @GoLean.Surface.TerminatesNormally
example := @GoLean.Surface.terminatesNormally_of_progressExec
example := @GoLean.Surface.InitialSplit.noFrame
example := @GoLean.Surface.goldenTerminatesNormally
example := @GoLean.Surface.recoverTerminatesNormally
example := @GoLean.Surface.quorumOneKnownTerminatesNormally
example := @GoLean.Surface.quorumThreeAllTerminatesNormally
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
the first-order readout and `quorumOneKnownNotElevenRun` its
run-conditioned negative twin.

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

`✓ DISCHARGED (sem-adequacy slice 5, 2026-08-04)`: the
`quorumOneKnownNotEleven_statement` target (`39891ae`, phase 4) — the
UNCONDITIONAL `¬ GoFuncSpec … (n = 11)` — is now the theorem
`quorumOneKnownNotEleven` (`Specs/TotalPins.lean`): the ∀-streams
termination checker (`allStreamsOk`, kernel-evaluated) exhibits the
terminating run the old note said this needed, and the wrong spec's
triple at that run contradicts `quorumOneKnownReturnsTwelve`. The
run-conditioned twin is retained as `quorumOneKnownNotElevenRun`. -/
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
example := @GoLean.Iris.wp_call_start
example := @GoLean.Iris.wp_tgtop_stores
example := @GoLean.Iris.wp_call_arg_next
example := @GoLean.Iris.wp_frame_return₂
example := @GoLean.Surface.sat_sep_insert
example := @GoLean.Surface.quorumOneKnownFuncSpec
example := @GoLean.Surface.quorumOneKnownMeetsSpec
example := @GoLean.Surface.quorumOneKnownReturnsTwelve
example := @GoLean.Surface.quorumOneKnownNotElevenRun
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

/-- `✓` **the spec-parity slice-3 laws + their imported-goose witnesses**
(S3 audit round, 2026-08-10 — the slice first shipped these without
registry entries; the deletion tripwire now covers them like their
siblings above). SCOPE OF THE MECHANISM, stated plainly (delta
review): these `example :=` lines are a NAME-EXISTENCE tripwire —
deleting or renaming a law or witness breaks this build, and the
whole-module axiom sweep covers their proofs — but they CANNOT detect
a witness that stops APPLYING its law (witness-citation drift, the
content half of non-vacuity); that detection remains the pre-merge
audit's job, per this file's header. Attribution: `wp_new_value` (the
allocating apply core's third instance, ∀σ `hstore` premise) is
discharged concretely at the exemplar's `$c2 = new(*uint64)` step
(`wp_compareNil_body`, and `_hand`); `wp_init_bool` at the kit
wrapper's call-target declaration (`wp_golean_wrapper_body`);
`wp_init_ptr` at the exemplar's pointer declarations
(`wp_compareNil_body`). `wp_golean_driver` is NOT a witness of any of
the three laws — it is the kit's assembly walk, anchored here as a
deletion tripwire only (delta-review relabel). -/
example := @GoLean.Iris.wp_new_value
example := @GoLean.Iris.wp_init_bool
example := @GoLean.Iris.wp_init_ptr
example := @GoLean.Iris.ImportedGoose.wp_golean_wrapper_body
example := @GoLean.Iris.ImportedGoose.wp_golean_driver
example := @GoLean.ImportedGoose.SemanticsNil.wp_compareNil_body
example := @GoLean.ImportedGoose.SemanticsNil.wp_compareNil_body_hand
/-- `✓` **the P-S3-5 joint-carrier compositions** (slice 6, closing the
recorded carrier gap): the kit's generic
`goSpec_seeded_totalReadout` — `GoSpec` + seeded `MachineWf` + the R2
∀-streams `Terminates` pin ⇒ completes-AND-verdict on the SINGLE
sequential carrier (the `goldenTotalReadout` precedent shape) — and
its six class-1 instances (each a concrete discharge: every premise
is closed at the row's program, so the generic lemma ships nowhere
without an inhabitant). Same name-existence-tripwire scope as the
blocks above: deletion/rename breaks this build and the exhaustive
sweep of axioms covers the proofs; whether each instance still cites its
row's real R2 pin is witness-citation content, which stays the
pre-merge audit's job. The concurrent (channel) rows deliberately
remain two-halves — their joint form needs the frame-quantified
triple (P-S4-1/2), not this kit. -/
example := @GoLean.ImportedGoose.goSpec_seeded_totalReadout
example := @GoLean.ImportedGoose.SemanticsNil.compareNilToNilTotalReadout
example := @GoLean.ImportedGoose.SemanticsNil.compareSliceToNilTotalReadout
example := @GoLean.ImportedGoose.SemanticsNil.comparePointerToNilTotalReadout
example := @GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedToNilTotalReadout
example := @GoLean.ImportedGoose.SemanticsNil.comparePointerWrappedDefaultToNilTotalReadout
example := @GoLean.ImportedGoose.SemanticsBlock.explicitBlockTotalReadout
-- The slice-6 driver-tranche class-1 instances ride the same block
-- (semantics/new — both upstream-Qed parity rows; semantics/vars —
-- coverage rows; per-row records in the manifest).
example := @GoLean.ImportedGoose.SemanticsNew.nilDefaultTotalReadout
example := @GoLean.ImportedGoose.SemanticsNew.nilValTotalReadout
example := @GoLean.ImportedGoose.SemanticsVars.pointerAssignmentTotalReadout
example := @GoLean.ImportedGoose.SemanticsVars.anonymousAssignTotalReadout
/-- `✓` **the spec-parity slice-4 curated channel rows** (manifest
feature class 3; `Specs/GooseParityChannels.lean` over the three
staleness-guarded channel pins). Same name-existence-tripwire scope as
the slice-3 block above: deleting a certificate or its ∀-schedule
readout breaks this build; the exhaustive axiom sweep covers their
proofs; witness-citation drift stays the audit's job. The four
`chanCert_*` kit derivations are generic wrappers over the checker
soundness kit (hoisting candidates, recorded in the module header);
the per-row `NoDeadlock`/`NoRace`/`TerminatesNormallyC` corollaries
are one-liners over the registered certificates, covered by the
sweep. SLICE 6 (fuel-independence lift): every row's bundle is
FUEL-GENERAL — `<row>Cert`/`<row>AllSchedules` in the `∃N, ∀ fuel ≥ N`
form, `NoDeadlock`/`NoRace` at ALL fuels — and the kernel evidence is
the per-row `<row>Cert<bound>` literal at the shipped bound (anchored
below so the `decide +kernel` base cannot silently vanish under the
general form). -/
example := @GoLean.ImportedGoose.chanCert_allSchedules
example := @GoLean.ImportedGoose.chanCert_noDeadlock
example := @GoLean.ImportedGoose.chanCert_noRace
example := @GoLean.ImportedGoose.chanCert_terminatesNormallyC
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbNotReadyCert200
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbNotReadyCert
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbNotReadyAllSchedules
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbGuaranteedReadyCert200
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbGuaranteedReadyCert
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbGuaranteedReadyAllSchedules
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbFullBufferCert200
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbFullBufferCert
example := @GoLean.ImportedGoose.ChannelSelectTricky.nbFullBufferAllSchedules
example := @GoLean.ImportedGoose.ChannelMuxer.asyncCert400
example := @GoLean.ImportedGoose.ChannelMuxer.asyncCert
example := @GoLean.ImportedGoose.ChannelMuxer.asyncAllSchedules
example := @GoLean.ImportedGoose.ChannelMuxer.clientCert800
example := @GoLean.ImportedGoose.ChannelMuxer.clientCert
example := @GoLean.ImportedGoose.ChannelMuxer.clientAllSchedules
example := @GoLean.ImportedGoose.ChannelActris.dspCert400
example := @GoLean.ImportedGoose.ChannelActris.dspCert
example := @GoLean.ImportedGoose.ChannelActris.dspAllSchedules
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
  is DISCHARGED at sem-adequacy slice 5 (2026-08-04) by
  `quorumThreeAllNotTwelve` in `Specs/TotalPins.lean` — the terminating
  run its honesty note demanded is now kernel-exhibited (∀-streams, via
  `allStreamsOk`). The run-conditioned twin is retained as
  `quorumThreeAllNotTwelveRun`.

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
the first-order readout and `quorumThreeAllNotTwelveRun` its
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

`✓ DISCHARGED (sem-adequacy slice 5, 2026-08-04)`: the UNCONDITIONAL
`quorumThreeAllNotTwelve_statement` — the family's honesty note said it
demands EXHIBITING a terminating run; the ∀-streams checker now exhibits
one (all 3! = 6 pick orders explored by kernel evaluation), and
`quorumThreeAllNotTwelve` (`Specs/TotalPins.lean`) discharges the
target. (THE ARC GOAL, `committedIndexAllConfigs_statement`, was
DISCHARGED in phase 4 — the block below.) -/
example := @GoLean.Surface.quorumThreeAllFuncSpec
example := @GoLean.Surface.quorumThreeAllMeetsSpec
example := @GoLean.Surface.quorumThreeAllReturnsSix
example := @GoLean.Surface.quorumThreeAllNotTwelveRun
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
/-- `✓` the CONCURRENT-Language law kit (channels arc slice 5,
`LangC.lean`) — `wpC_fork` (the `go` statement's WP law),
`wpC_pure_det` (the pool carrier's pure-det lift) and
`wpC_spawned_strip` (the BUG-040 marker's thread-local strip), all
witnessed IN THE SAME COMMIT by `wpC_spawn_noop_witness` (the full WP
of a program that spawns — every law premise discharged against the
concrete program; externals = the standard program/method pins) and
closed end-to-end by `adequateC_spawn_noop` (zero hypotheses,
`adequate .NotStuck` over the POOL Language — parent and forked child
both covered). The pairing/wake fragment is deliberately NOT claimed:
LangC's module docstring records the structural obstruction (a pairing
touches two threads; the thread-pool Language steps one) and the
decomposition route. -/
example := @GoLean.Iris.wpC_fork
example := @GoLean.Iris.wpC_pure_det
example := @GoLean.Iris.wpC_spawned_strip
example := @GoLean.Iris.wpC_spawn_noop_witness
example := @GoLean.Iris.goC_adequacy
example := @GoLean.Iris.adequateC_spawn_noop

/-- `✓` the negative pins (trivialization guards). -/
example := @GoLean.GoCore.NegativeSpecs.unbound_ref_stuck
example := @GoLean.GoCore.NegativeSpecs.unbound_var_stuck
example := @GoLean.GoCore.NegativeSpecs.terminal_stuck
example := @GoLean.GoCore.NegativeSpecs.div_nonzero_no_panic

/-! ## The verified-examples exemplar (slice 1, 2026-08-12)

`✓` **the fib exemplar + the break-aware loop spine**
(`Examples/Fib.lean`, `docs/2026-08-12_example-spec-form.md`). The six
new laws ship with the fib walk as their same-commit discharge witness
(non-vacuity): `wp_while_inv_break` (the break-aware invariant rule —
every frontend-lowered `for` loop needs it, since the desugar exits
through `break`) is discharged at the fib loop with the Fibonacci pair
invariant; `wp_break`/`wp_breaking_seq`/`wp_breaking_loop` at the
loop's exit test; `wp_assign_many_start` at `a, b = b, a+b`;
`wp_call_enter₁₁` (+ `wp_alloc_step₂`, `bindParams₁`) at the driver's
one-argument frame entry. Same name-existence-tripwire scope as the
blocks above (the exhaustive sweep covers the proofs; witness-citation
drift stays the audit's job). Scope honesty: the fib theorems are
USABILITY evidence per the verified-examples charter's two-questions
separation — never machine-hardening evidence. -/
example := @GoLean.Iris.wp_while_inv_break
example := @GoLean.Iris.wp_break
example := @GoLean.Iris.wp_breaking_seq
example := @GoLean.Iris.wp_breaking_loop
example := @GoLean.Iris.wp_assign_many_start
example := @GoLean.Iris.wp_call_enter₁₁
example := @GoLean.Iris.wp_alloc_step₂
example := @GoLean.Iris.bindParams₁
example := @GoLean.Examples.Fib.fibGoSpec
example := @GoLean.Examples.Fib.fibTerminates
example := @GoLean.Examples.Fib.fibGoSpecC
example := @GoLean.Examples.Fib.fib_wrapsC

/-! ## The fuel-measure termination kit (slice 1.5, 2026-08-12)

`✓` **the symbolic-termination rule family + its fib witness**
(`FuelMeasure.lean`; checkpoint ruling 2026-08-12 — enumeration is
banned as a proof method, and the 94-seed kernel enumeration that
first discharged `fib_ok`'s completion half is DELETED, replaced by
`completesIn_measure_loop`, the completion-side twin of
`wp_while_inv_break`: loop invariant indexed by a decreasing measure,
per-iteration fuel bound, strong induction over the EXECUTABLE — no
Iris in the termination half by design, see the module docstring).
Same-commit discharge witness: `fibTerminates` (anchored above) now
covers the FULL uint64 domain, and `fib_total` is the full-domain
total-correctness form. Name-existence tripwire scope as usual. -/
example := @GoLean.Surface.CompletesIn
example := @GoLean.Surface.completesIn_measure_loop
example := @GoLean.Surface.completesIn_comp
example := @GoLean.Surface.terminates_of_completesIn
example := @GoLean.Surface.execStmtLoop_of_stepFnIter
example := @GoLean.Surface.stepFnIter_chain
-- HARNESS RESTATEMENT (form note §11, 2026-08-13): `fib_ok`/`fib_total`
-- are now the harness headlines over `runFunctionWithContextM`
-- (three-phase fib_harness; the old cell-readback fib_ok is DELETED;
-- old fib_total/fib_wraps renamed `fib_total_seeded`/`fib_wraps_seeded`
-- — proof-side supporting layer feeding fib_total_framed). NOTE the
-- harness pair's axiom set DROPS Classical.choice (no Iris, no frame
-- layer in its derivation) — the pins below assert the smaller set.
example := @GoLean.Examples.Fib.fibHarnessFunc
example := @GoLean.Examples.Fib.fib_readout
example := @GoLean.Examples.Fib.fib_total_seeded
/-- info: 'GoLean.Examples.Fib.fib_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Fib.fib_ok
/-- info: 'GoLean.Examples.Fib.fib_wraps_seeded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Fib.fib_wraps_seeded
/-- info: 'GoLean.Examples.Fib.fib_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Fib.fib_total
/-- info: 'GoLean.Surface.completesIn_measure_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.completesIn_measure_loop
-- Slice 2a (2026-08-13): the memory-quantified form's fib retrofit —
-- ∀-frame run-conditioned readout + pointwise frame preservation,
-- derived from the GoSpec frame closure at an explicit framed split
-- (form under the slice-2a checkpoint; design note §9).
example := @GoLean.Examples.Fib.fib_framed
/-- info: 'GoLean.Examples.Fib.fib_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Fib.fib_framed

-- The executable frame theorem (slice 2b part 1, 2026-08-13;
-- docs/2026-08-13_executable-frame-theorem.md §1): the ~200-arm
-- per-step simulation, its iteration, the driver-level success-run
-- transfer, and the completion-transfer corollary the ∀-frame TOTAL
-- headlines consume. `Classical.choice` is INHERITED from the core
-- MachineSound layer (root: `Machine.Heap.lookup_set_ne`, which every
-- heap-touching commutation lemma consumes) — not introduced by the
-- Frame layer's own proofs (e.g. `loadLoc_sim` is choice-free).
example := @GoLean.Frame.FrameSim
example := @GoLean.Frame.ShiftSpec
example := @GoLean.Frame.uniformShift_spec
/-- info: 'GoLean.Frame.stepFn_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFn_sim
/-- info: 'GoLean.Frame.stepFnIter_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFnIter_sim
/-- info: 'GoLean.Frame.execStmtLoop_ren' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.execStmtLoop_ren
/-- info: 'GoLean.Frame.completesIn_ren' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.completesIn_ren

-- The frame theorem CONSUMED (slice 2b consumption, 2026-08-13):
-- fib's ∀-frame TOTAL form — fib_total's completion transferred to
-- every admissible framed placement through the seed FrameSim (tight
-- canonical seed, dom = {0}, na₀ = 1); readout + frame clauses from
-- the terminal FrameSim. Same-commit discharge witness for the
-- transfer corollaries.
example := @GoLean.Examples.Fib.fib_total_framed
/-- info: 'GoLean.Examples.Fib.fib_total_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Fib.fib_total_framed

-- Allocator independence (user direction 2026-08-13): the sequential
-- allocator is a QUOTIENT REPRESENTATIVE of Go's unpromised address
-- choices — every conforming relabeling (any ShiftSpec injection;
-- swapShift witnesses the non-uniform width) yields an observationally
-- equal execution. The allocation-addressing pin's re-envelope
-- obligation is DISCHARGED BY THEOREM (latitude inventory, envelope-
-- by-quotient disposition).
example := @GoLean.Frame.allocatorIndependence
example := @GoLean.Frame.swapShift_spec
example := @GoLean.Frame.swapShift_not_uniform
/-- info: 'GoLean.Frame.allocatorIndependence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.allocatorIndependence

/-! ## The §9e slice-index WP laws (slice 2b, 2026-08-13)

`✓` **the slice-index law family + witnesses** (`Laws/Slice.lean`,
`GoLeanProofs/SliceMem.lean`; build list in
`docs/2026-08-12_example-spec-form.md` §9e). Same-commit discharge
witnesses (non-vacuity): `wp_index_get_witness` (the read law on a
concrete two-element slice), `wp_len_slice_witness` (`len(s)`), and
`wp_swap_witness` — the FULL two-target index-shape multi-assign
`s[0], s[1] = s[1], s[0]`, which discharges `wp_store_index_slice_u64`
(both stores) and doubles as the build list's item 4: the tgtOpK spine
at index-step target shapes needs NO new law (the spine laws are
shape-generic; `completeTargetRef` at `.chain [.index]` discharges by
`rfl`) — the witness exercises those instances rather than merely
claiming them. `sliceCells`/`sliceVal` are the §9a shared corpus
vocabulary. Scope honesty: the store law is stated on the `[]uint64`
fragment (the store path re-normalizes the whole backing array at the
cell's declared type; a value/type-generic law is a recorded growth
point, `Laws/Slice.lean` docstring). -/
example := @GoLean.SliceMem.sliceCells
example := @GoLean.SliceMem.sliceVal
example := @GoLean.Iris.wp_index_get_slice
example := @GoLean.Iris.wp_len_slice
example := @GoLean.Iris.wp_store_index_slice_u64
example := @GoLean.Iris.wp_index_get_witness
example := @GoLean.Iris.wp_len_slice_witness
example := @GoLean.Iris.wp_swap_witness
/-- info: 'GoLean.Iris.wp_store_index_slice_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_store_index_slice_u64
/-- info: 'GoLean.Iris.wp_swap_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Iris.wp_swap_witness

/-! ## Per-example axiom gates — sharded (slice 0 lever 3, 2026-08-14)

The per-example `example :=` witness references and
`#guard_msgs #print axioms` pins live in `proofs/Audit/<Example>.lean`,
imported at the top of this file and moved there VERBATIM. Each shard
imports only its own example module (the `deps/brick-wp` per-file
dependency shape), so one example's change re-checks one shard instead
of every pin in the tree. The exhaustive sweep at the top of THIS file
is unaffected: it walks the whole environment of the audited build, and
the shards are in it by import. `scripts/ci`'s proofs-file
audit-coverage step fails closed if a shard ever falls out of the
closure. Shards: Reverse, Gcd, MinMax, InsertionSort, BinSearch,
WordCount, Histogram, PowMod, DotProduct. Fib's references stay in the exemplar section
above — that section pins the WP-law kit, not the example.
-/
/-! ## The harness-entry glue (form note §11; FuelMeasure)

`✓` fuel monotonicity of the native entry + the D1 readout bridge for
harness headlines — same-commit discharge witnesses `fib_readout` /
`reverse_readout` (and the gcd/minmax twins). -/
example := @GoLean.Surface.runConfig_unfold
example := @GoLean.Surface.runConfig_of_stepFnIter
example := @GoLean.Surface.runConfig_next_stop
example := @GoLean.Surface.runConfig_mono
example := @GoLean.Surface.runFunctionWithContextM_mono
example := @GoLean.Surface.harness_readout_of_total
/-- info: 'GoLean.Surface.harness_readout_of_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.harness_readout_of_total

/-! ## The harness lowering pins (audit fix round, 2026-08-14)

`✓` the seven `<example>_harness` lowering pins — each one an `rfl`
tying the harness `Func` the proofs step through to the frontend's
lowering of the corpus program (`findFunctionIn? <lowered>.funcs
⟨"<name>_harness"⟩ = some <name>HarnessFunc`). They were anonymous
`example`s in their modules, so nothing could cite them and nothing
noticed if one disappeared; naming them makes the "the theorem's
subject IS the lowering" step referenceable from the gallery and the
design notes. Name-existence tripwire scope, as for every block here —
the pins are load-bearing for the headlines above, whose statements
mention the same `*HarnessFunc` constants. -/
example := @GoLean.Examples.Fib.fibHarness_pin
example := @GoLean.Examples.Gcd.gcdHarness_pin
example := @GoLean.Examples.Reverse.reverseHarness_pin
example := @GoLean.Examples.MinMax.minmaxHarness_pin
example := @GoLean.Examples.BinSearch.searchHarness_pin
example := @GoLean.Examples.InsertionSort.isortHarness_pin
example := @GoLean.Examples.WordCount.wordcountHarness_pin

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
