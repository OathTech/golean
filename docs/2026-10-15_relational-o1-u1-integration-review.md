# Independent I2 integration review

Reviewer: independent i2_integration_review, 2026-10-15. Scope unrestricted.
Reviewed charter: frozen logic lane docs/2026-10-15_relational-o1-u1-integration-charter.md.
Reviewed implementation: `4731d491999e113e5016ad975d1747614d100bd4`.

Inputs: I1 5d8e53e9f1a046fb645fce49901de714591e0819; O1 56168ed59da4c8972169bcaee778b767f35c6005; U1 82a2ff3139053c2a23d97cc90d8f21bb2400d96f; logic 5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42.

## Source review

No new integration correctness finding after source review and independent compiled/replay checks. The inherited implementation scan still FAILS with 21 open, unwaived findings. Read all new public U1 modules, O1 Event/EventFrame/EventSound/History/Observation, exact O1 and U1 RD8 adapters, joint source and controls. Earlier review verdicts were not used as assumptions.

O1 independent stack-depth classification is retained, including normal exits vs panic unwind; actual entry/return event payloads and pre-stores survive the sum adapter. Finite histories require actual successful transitions and support unfinished prefixes.

U1 ranked traversal carries real source paths and every ready branch. Domain.all_schedules interprets it into admission, all-tape progress and all-successor safety. The resource adapter separately interprets the same traversal; it consumes source paths, scheduler coverage, actual binder writes and completion glue. Canonical realization retains ordered labels and scheduler records; only final control/store are equated. Real entry allocation is distinct from post-allocation invariant preservation. The restricted domain excludes stores, calls, regions and internal picks. Neither arbitrary sequentialization nor concurrent transport follows.

The joint identity observer reflects complete BoundaryEvent values. quiet_iff consequently establishes raw semantic event-list emptiness, stronger than Observer.none or access/output silence. source_paths/source_traversal consume the actual read/read/add laws; plan_source applies to non-final residual Plan sources including allocation/scheduling/binder/completion/glue. The arbitrary final continuation has no silence premise. This suffices for the requested source-policy compatibility, once compiled. It is not itself a new theorem that every actual SegmentPrefix has a residual Plan or an empty Boundary.History; such a whole-segment history claim must not be attributed to these statements.

The alias control remains an invocation/write/read case outside the independent expression class and asks the actual explorer and certificate checker for exactly {-2, 7}. Output-order and allocator-bound controls remain distinct.

## Independent source identity checks

Python/subprocess git-show comparison against immutable objects, executed from the candidate root:
- All 10 changed O1 source/client files (excluding shared facade) match O1 exactly.
- All 25 changed U1 source/client files (excluding shared facade) match U1 exactly.
- Among existing GoLean/, tools/, Tests/, scripts/ files from I1, only RelationalObservation.lean, GoLean/Relational.lean and Tests/GoCoreAudit.lean differ. Runtime, detector, frontend and driver sources are unchanged.
- All 125 frozen RD8 package files were compared, including 115 Lean sources; only generated lakefile.toml and removed/regenerated lake-manifest.json differ. No frozen Lean source differs.
- Static facade import walk reaches 73 local modules and four toolchain leaves; no Iris, GoLeanIris, RelationalCodeX or U1RD8 dependency. Text scan finds no executable escape hatch (one implemented_by mention occurs in a documentation comment).

Exact reproduction: enumerate `git ls-tree -r --name-only <pin>`, compare each selected path with `git show <pin>:<path>` as bytes. For frozen logic use prefix experiments/2026-10-14_relational-codex/ and compare to candidate .tmp/rd8. For facade recursively read import lines from GoLean.Relational.

## Independent compiled checks

- Independently compiled current Joint.lean into reviewer-owned .tmp/i2-review/Joint.olean, reading existing candidate/frozen dependency outputs only. No root or peer rebuild was launched.
- Independently compiled Review.lean importing the complete frozen aggregate and the private Joint output. Exact EventAgreement, SimulationLaw and GuardedTarget applications compile with no added hypotheses. The observable-final-tail control proves an ordinary normal return emits an event and is not EventQuiet; completion remains valid without requiring final-tail silence.
- Exhaustive project-closure axiom scan passed for **26,922 declarations**, including reviewer declarations and private helper/generated declarations. Only propext, Classical.choice and Quot.sound occur. This count belongs to the reviewer import context, not the author's separate audit.
- The fresh implementation scan **FAILS: 21 findings**, all inherited and unwaived. Exact freshly reported names are below. This remains a failure despite successful axiom checks and replay.
- Independent proof-body assertions passed: quiet_iff -> O1Compatibility.emit_projection/reflects; source_paths -> U1RD8.paths/path_policy; source_traversal -> U1RD8.traversal/traversal_policy; projected_source -> plan_source; simulation -> traversal/interpret; interpret -> Traversal.rec/scheduler_cover/binder_effect/completion_path.
- Independent exact kernel replay passed for eight requested modules, each once: Joint, Review, O1Compatibility, RD8Acceptance, U1RD8.Base, U1RD8.Source, U1RD8.Simulation, U1RD8.Audit. Separate earlier RootReview compilation/replay also passed.
- The reviewer harness initially failed twice due to missing CoreM/Nat/Bool type annotations in its audit code. These were local harness failures, corrected without any product change; subsequent elaboration and replay exited zero.

Reproduction of independent checks: obtain the RD8 package's `lake env printenv LEAN_PATH` and `lake env which lean`; prepend the reviewer output directory to LEAN_PATH; run `LEAN_NUM_THREADS=2 capped <lean> -R <scratch> -o <scratch>/Joint.olean <scratch>/Joint.lean`, then the analogous Review command. Run the same toolchain's `leanchecker --verbose` on the eight exact module names above, with the same path and cap. Check the replay-name multiset exactly.

## Inspected author evidence and remaining handoff validation

Inspected the fresh alias log: exact {-2, 7}, eight explorer leaves, and certified exact set (226 nodes, 231 edges). Inspected the U1 control build: 79 jobs passed, including output-order/allocation controls and headline axiom reports. Source identity establishes no new runtime/detector/frontend/driver change; independent facade import inspection found no customer dependency.

The final author joint build passed 446 jobs. Independently inspected its 26,808-declaration reused core/customer scan and 120-declaration supplemental scan, which includes GoLeanIrisExamples as well as Joint/O1Compatibility/RD8Acceptance. All axiom checks pass; the implementation scan remains FAIL21. The first reviewer audit had omitted the 48 GoLeanIrisExamples declarations too; this was corrected by expanding the selection and rerunning the complete reviewer audit and Review replay, yielding the 26,922 count above. No additional implementation finding or forbidden axiom was found.

Independently compared exact finding-name sets from fresh U1 and D1 logs and the final combined log: U1 = D1 = 16 names; combined = reviewer = those sixteen plus exactly the five frozen downstream declarations. This is an exact set comparison, not a count-only claim.

Inspected successful RD6/RD7 builds (426 jobs each). RD6 reports 5,940 original aggregate and 5,943 original-acceptance declarations, RD7 6,058. Independently matched all completed replay-name multisets to actual built `.olean` inventories and checked an output exists for every local/upstream source: RD6 exactly 417 (110 upstream + 101 local + 206 dependencies), RD7 exactly 420 (110 + 104 + 206), RD8 exactly 439 (110 + 123 + 206), with no missing, extra or duplicate names. Dependency inventory is 174 Iris + 18 Batteries + 14 Qq. These full runs are author evidence, not independent full rebuilds/replays; the independent reviewer checked their inventories. The author subsequently confirmed all three replay sessions exited zero. The additional fresh JointAudit replay also exited zero according to the author; its inspected log records `replaying JointAudit with --fresh`. This reconstructs the imported environment from empty but was not rerun by the reviewer.

Inspected the completed full CI log: RESULT PASS, 1,394 seconds; 255 warning-free build jobs, 110-module kernel replay (explicit exit zero), 396 eval tests, frontend/boundary/declaration and whole-tape scheduler controls, every gate and speedbump green. Fresh differential: 4,025 cases = 3,767 PASS + 258 tracked FAIL; fresh negative: 415 PASS. Baseline comparisons report no regression or cause drift and unchanged baselines. The raw differential runner's exit 1 represents that tracked failing set, not a claim that all cases passed. The author confirmed full CI exited zero. The log explicitly certifies the dirty tested worktree; it was not an invocation at the later immutable commit. The independent source binding below supplies that separate connection.

Final immutable binding: independently verified **all 4,385** entries in the complete tested-source SHA-256 manifest against both the implementation commit's actual blobs and the final worktree bytes. All match `4731d491999e113e5016ad975d1747614d100bd4`. The earlier 4,363-entry source freeze is an unchanged subset. The independently compiled reviewer copy of Joint.lean matches the committed blob exactly, as do the final JointAudit source and the inspected stage. Git status was clean. These checks bind the tested source bytes to the immutable result without erasing CI's dirty-tree qualification.

Rechecked all frozen original package files against immutable logic objects: RD6 106 files / 98 Lean sources at bbb372e2b97eec663f55a01ee4993f98be829e1b; RD7 113 / 104 at f314a4f7ce69f8e5dc1c835298d4f1a2832a996f; RD8 125 / 115 at 5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42. Every original Lean source is identical; only private pins.json, lakefile.toml and generated lake-manifest.json differ. No uncommitted peer source was used.

To reproduce source binding at a claim point, collect the checked file SHA-256 values before the check, preserve that ephemeral manifest through the commit, and compare each digest with `git cat-file` of `<implementation-pin>:<path>` and the worktree bytes; require exact equality and preserve the earlier manifest as a subset. The manifests and logs are disposable; the conclusion and the immutable pin are retained here. For a fresh independent reproduction after scratch cleanup, use the experiment README at the reviewed implementation pin and rerun its checks.

The inherited Memory warning and recorded live 35 NOT-PUBLIC failure remain. No live run, renderer correspondence, arbitrary sequentialization, concurrency transport, or main landing is approved by this review. No new load-bearing dependency was introduced beyond the explicitly private O1/U1 frozen acceptance adapters; the joint quiet policy depends substantively on O1's checked observer agreement.

## Fresh implementation findings (all open and unwaived)

- `GoLean.GoCore.instReprTy.repr._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.instReprGoValue.repr._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Machine.instReprSeedValue.repr._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprTy.repr_3._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.IrisCustomer.pathTags_persistent._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.instBEqStmt.beq._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.Logic.Source.instReprFieldTys.repr_1._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprField.repr_2._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprTy.repr_2._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprMethod.repr_2._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprMethod.repr_1._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprMethod.repr_3._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.instReprStmt.repr._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.instBEqExpr.beq._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprTy.repr_1._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprField.repr_3._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.instReprExpr.repr._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.Logic.Source.instReprScalarTy.repr_1._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.Logic.Source.instReprScalarTy.repr_2._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.GoCore.Declaration.instReprField.repr_1._unsafe_rec` — partial implementation without transparent total parent.
- `GoLean.Logic.Source.instReprFieldTys.repr_2._unsafe_rec` — partial implementation without transparent total parent.

Reviewed Joint source SHA-256: `a9d73a4e41ee8abceff70807117e1fff84bb4b6def6d6536c4eb065c1fb3dab0`.

## Self-contained reviewer reproduction source

After the experiment README reconstructs and builds the combined frozen package, save the following as `.tmp/i2-review/Review.lean`. The original RootReview controls are included here, so their separate disposable source is unnecessary. This is a small review client, not a new gate or validation framework.

```lean
import RelationalCodeX
import Joint
import Lean
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

namespace I2IndependentReview
open GoLean GoCore GoCore.Machine GoCore.Relational
open GoLean.Logic RelationalCodeX.Sweep

-- A boundary that emits an event is a legal arbitrary finished tail.
theorem final_tail_observable (ctx : ProgramCtx) (fid : FuncId)
    (k : Continuation) (s : Store) :
    Boundary.events ctx (returning fid k s) = [.returned ⟨fid, [], s⟩] := by
  rfl

theorem final_tail_not_quiet (ctx : ProgramCtx) (fid : FuncId)
    (k : Continuation) (s : Store) :
    ¬ I2.EventQuiet ctx (returning fid k s).control := by
  intro quiet
  have h := quiet s
  change Boundary.events ctx (returning fid k s) = [] at h
  rw [final_tail_observable] at h
  contradiction

-- Prefix lifting stops immediately at a reached boundary even if that tail emits.
theorem finished_observation_allowed (ctx : ProgramCtx) (a : State) :
    SafeUntil ctx (fun x _ _ => Boundary.events ctx x = []) (fun _ => True) a :=
  .done trivial

-- Exact existing consumers, with no new semantic-law parameters.
example : RelationalCodeX.Observed.EventAgreement RD8Acceptance.events := I2.agreement
example : SimulationLaw := I2.simulation
example : GuardedTarget := I2.guarded

#print axioms final_tail_observable
#print axioms final_tail_not_quiet
#print axioms finished_observation_allowed
#print axioms I2.quiet_iff
#print axioms I2.source_traversal
#print axioms I2.projected_source
#print axioms RD8Acceptance.prefix_history
#print axioms RD8Acceptance.guarded
#print axioms U1RD8.simulation
#print axioms U1RD8.closed_guarded
end I2IndependentReview

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let expected := [``I2.quiet_iff, ``I2.path_policy, ``I2.traversal_policy,
    ``I2.source_paths, ``I2.source_traversal, ``I2.plan_source,
    ``I2.projected_source, ``I2.agreement, ``I2.simulation, ``I2.guarded]
  for n in expected do
    unless env.contains n do throwError "Missing joint theorem: {n}"
  let mut count : Nat := 0
  let mut findings : Nat := 0
  for (n, info) in env.constants.toList do
    let selected := match env.getModuleIdxFor? n with
      | none => true
      | some i => let m := env.header.moduleNames[i.toNat]!
                  [ `GoLean, `GoLeanIris, `GoLeanIrisExamples, `RelationalCodeX, `O1Compatibility,
                    `RD8Acceptance, `U1RD8, `Joint].contains m.getRoot
    unless selected do continue
    count := count + 1
    for ax in (← collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Forbidden axiom: {n} -> {ax}"
    if info.isUnsafe then
      findings := findings + 1
      logInfo m!"TRUST FINDING unsafe: {n}"
    if let .defnInfo d := info then
      if d.safety == .partial then
        let totalParent : Bool := match env.find? n.getPrefix with
          | some (.defnInfo parent) => parent.safety == .safe
          | _ => false
        unless totalParent do
          findings := findings + 1
          logInfo m!"TRUST FINDING partial without transparent total parent: {n}"
    if (Lean.Compiler.getImplementedBy? env n).isSome then
      findings := findings + 1
      logInfo m!"TRUST FINDING implemented_by: {n}"
    if Lean.isExtern env n then
      findings := findings + 1
      logInfo m!"TRUST FINDING extern: {n}"
  logInfo m!"Independent complete imported project axiom audit: PASS {count} declarations"
  if findings > 0 then logInfo m!"Implementation scan: FAIL {findings} findings; all unwaived"
  else logInfo "Implementation scan: PASS"
  for (n, deps) in [
    (``I2.quiet_iff, [``O1Compatibility.emit_projection, ``I2.reflects]),
    (``I2.source_paths, [``U1RD8.paths, ``I2.path_policy]),
    (``I2.source_traversal, [``U1RD8.traversal, ``I2.traversal_policy]),
    (``I2.projected_source, [``I2.plan_source]),
    (``U1RD8.simulation, [``U1RD8.traversal, ``U1RD8.interpret]),
    (``U1RD8.interpret, [``GoLean.GoCore.Relational.Unseq.Traversal.rec,
      ``GoLean.GoCore.Relational.Unseq.scheduler_cover,
      ``GoLean.GoCore.Relational.Unseq.binder_effect,
      ``GoLean.GoCore.Relational.Unseq.completion_path]) ] do
    let info ← getConstInfo n
    let some body := info.value? (allowOpaque := true) | throwError "No body: {n}"
    for dep in deps do
      unless body.getUsedConstants.contains dep do throwError "Missing body dependency: {n} -> {dep}"
    logInfo m!"Independent proof-body dependencies: {n} -> {deps}"
```

Run this Python from the candidate root to compile into independent reviewer outputs and replay the exact checked modules. It reads the existing candidate/package outputs and does not build or modify peers. It requires successful combined package setup/build from the experiment README first.

```python
from pathlib import Path
import os, shutil, subprocess
from collections import Counter
root = Path.cwd()
scratch = root / ".tmp/i2-review"
package = root / ".tmp/rd8"
scratch.mkdir(parents=True, exist_ok=True)
shutil.copyfile(root / "experiments/2026-10-15-o1-u1-integration/Joint.lean", scratch / "Joint.lean")
paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=package, text=True).strip()
lean = Path(subprocess.check_output(["lake", "env", "which", "lean"], cwd=package, text=True).strip())
env = {**os.environ, "LEAN_NUM_THREADS": "2", "LEAN_PATH": str(scratch) + ":" + paths}
for name in ["Joint", "Review"]:
    subprocess.run(["capped", str(lean), "-R", str(scratch), "-o",
        str(scratch / (name + ".olean")), str(scratch / (name + ".lean"))], env=env, check=True)
modules = ["Joint", "Review", "O1Compatibility", "RD8Acceptance", "U1RD8.Base",
           "U1RD8.Source", "U1RD8.Simulation", "U1RD8.Audit"]
result = subprocess.run(["capped", str(lean.parent / "leanchecker"), "--verbose", *modules],
    env=env, check=True, text=True, capture_output=True)
print(result.stdout)
assert Counter(line[10:] for line in result.stdout.splitlines() if line.startswith("replaying ")) == Counter(modules)
```

For the author scan-name comparison, extract the text after the last `: ` from each `TRUST FINDING` line of the fresh U1, D1 and combined audit output. Compare sets, not counts: U1 must equal D1; combined must equal that set union the five downstream names listed above. The independent Review output must give the same combined set. For full replay inventory, enumerate `.olean` module names under candidate `GoLean`, the entire private local library output, and each exact private dependency library; compare the complete multiset against `replaying NAME` lines and separately require successful process exit. Check all local/upstream `.lean` source paths have corresponding outputs.
