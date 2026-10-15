# RD6/C2 acceptance reproduction

Checked semantic implementation: `626faca5a26f57fbf367aa9655e2aef08f20143a`.
Use an independent GoLean worktree at that pin and a private scratch directory.
The logic repository is an input source only. The commands below extract its
immutable objects without changing its files or pins. All source snippets are
acceptance clients, not permanent upstream imports or an Iris API.

```sh
mkdir -p .tmp/c2-consumer
python3 - <<'PYSETUP'
import io, json, subprocess, tarfile
from pathlib import Path
root = Path('.tmp/c2-consumer').resolve()
source = '/home/mike/projects/golean-logic'
prefix = 'experiments/2026-10-14_relational-codex/'
archive = subprocess.check_output(['git', '-C', source, 'archive',
    'bbb372e2b97eec663f55a01ee4993f98be829e1b', prefix])
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
    for member in tf.getmembers():
        if member.isfile():
            dest = root / member.name.removeprefix(prefix)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(tf.extractfile(member).read())
pins = json.loads((root / 'pins.json').read_text())
pins['GoLean'] = '626faca5a26f57fbf367aa9655e2aef08f20143a'
(root / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
with (root / 'lakefile.toml').open('a') as f:
    f.write('\n[[lean_lib]]\nname = "C2Adapter"\n[[lean_lib]]\nname = "C2Acceptance"\n')
PYSETUP
```

Save the two files below in that scratch package. Then, from the package,
prepare exact independent dependency clones using its frozen setup script:

```sh
python3 setup.py --golean-source ../.. \
  --seeds /home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages
mkdir -p .tmp
export TMPDIR="$PWD/.tmp"
export LEAN_NUM_THREADS=2
capped lake update
capped lake build GoLean RelationalCodeX C2Adapter C2Acceptance
capped lake env lean RelationalCodeX.lean
capped lake env lean C2Acceptance.lean
capped lake env leanchecker --verbose GoLean RelationalCodeX GoLeanIris \
  GoLeanIrisExamples C2Adapter C2Acceptance Iris Batteries Qq
```

The installed pinned toolchain is Lean 4.32.2. The seed repositories must
contain the frozen commits in `pins.json`. `setup.py` checks independent clones,
exact heads, clean source and absence of object alternates. Its optional
`--copy-cache` copies build artifacts only after checking source compatibility;
this checked run copied compatible caches and rebuilt the aggregate. Omitting
it rebuilds dependencies. Do not use shared writable build symlinks.

Require all commands to exit zero. Axiom reports must contain only `propext`,
`Classical.choice`, `Quot.sound`. Aggregate audit: 5,940 declarations; acceptance
audit: 5,943. In addition, both adapter theorem axioms are printed explicitly.
For exact replay, compare each `replaying NAME` line, including multiplicity,
with built `.olean` names under the requested roots in this private package
and its four dependencies. The checked run has 399 names: 93 GoLean, 59
RelationalCodeX, 34 GoLeanIris, 5 GoLeanIrisExamples, 1 each adapter/acceptance,
174 Iris, 18 Batteries and 14 Qq. All source modules under the consumer roots
must have built outputs. The inherited `Memory.lean:1625` unused-variable
warning remains visible; the recorded live 35 NOT-PUBLIC failure is not a
result of this isolated build and is not resolved by it.

## C2Adapter.lean

```lean
import RelationalCodeX.ProgramRequests
namespace C2Acceptance
open GoLean GoCore Relational

theorem phases : RelationalCodeX.C2.ProgramPhases :=
  ProgramExecution.Correspondence.phase_projection

-- Existing wrapper compatibility; not a new upstream request.
theorem invocation : RelationalCodeX.C2.InitInvocation := RelationalCodeX.C2.initInvocation

#print axioms phases
#print axioms invocation
end C2Acceptance
```

## C2Acceptance.lean

```lean
import RelationalCodeX
import C2Adapter

namespace C2Acceptance
open GoLean GoCore GoCore.Machine GoLean.Logic GoLean.Logic.ProgramExecution
open Procedure Frame

-- The exact phase consumer with its semantic parameter discharged. Original
-- Definition/ValuesTyped/seed premises, captures, bases, fuel and tape remain.
theorem phaseAcceptance (D : Definition ctx h ats rts)
    (reserved : ctx.program.typeDefs.hasReservedPrefix = true)
    {vs : List GoValue} (typed : ValuesTyped ats vs) {s₀ : Store}
    (hseed : seedGlobals ctx {} ctx.program.globals = .ok s₀) (fuel : Nat) (choices : Choices) :
    runProgramM fuel ctx.program D.fid.key (D.captures.val ++ vs).toArray choices =
      (runPkgInitM ctx fuel s₀ choices).bind (fun (s₁, ch₁) =>
        (execStmtLoop ctx fuel (entryState D s₁ vs) (entryConfig D s₁) ch₁).bind
          (fun (sf, _) => (loadMany ctx sf (roots (s₁.heap.size + D.arguments.length) D.results.length)).map
            (fun values => ({ values := values.toArray } : Readout)))) :=
  program_phase_acceptance phases D reserved typed hseed fuel choices

-- This retains the substantive downstream Iris obligation, explicitly.
theorem programAcceptance (assembly : InitAssembly) : @ProgramTarget ctx h ats rts :=
  closed_program_init_outcomes_conditional phases assembly

#print axioms phaseAcceptance
#print axioms programAcceptance
#eval RelationalCodeX.audit
end C2Acceptance
```

## Original-header compatibility

The independent reviewer also checked the verbatim original header at logic
`14cef5e62c7b42a1e0e1eae3a12c2d8674968c01`, retaining only the explicit
downstream assembly parameter. Its reproduction source is:

```lean
import C2Acceptance
namespace GoLean.Logic.ProgramExecution
open GoCore GoCore.Machine Procedure Frame IrisCustomer
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open scoped AssertionModel
noncomputable section
variable {ctx : ProgramCtx}
theorem originalAcceptance (assembly : InitAssembly) {α : Type} (GF : BundledGFunctors) {FS : List GFunctor} (O : Observer)
    [GoGpreSE GF O.Ev] [ClientGpre FS GF] (hinv : O.Inv []) (cp : ClosedInitProgram ctx)
    (GInit : ∀ [GoGSO GF O], (model ctx GF).Assertion 0 0) (init : InitContract ctx GF O GInit)
    (D : Definition ctx h ats rts) (argv : α → List GoValue)
    (Pre : ∀ [GoGSO GF O], (model ctx GF).Assertion 0 0)
    (pre : ∀ [GoGSO GF O], (model ctx GF).Entails ((model ctx GF).sep GInit ((model ctx GF).hist []))
      ((model ctx GF).update Pre))
    (φ : α → List GoValue → List O.Ev → Prop) (ψ : α → GoValue → List GoValue → List O.Ev → Prop)
    (z : α) (ht : ValuesTyped ats (argv z)) (exitSilent : ReturnSilent O.obs D.fid)
    (code : ∀ [GoGSO GF O], ⊩ HistContractP ((model ctx GF).at (.globals .main)) h ats rts argv Pre φ ψ)
    (fuel : Nat) (choices : Choices) :
    runProgramM fuel ctx.program D.fid.key (D.captures.val ++ argv z).toArray choices = .error .fuelOut ∨
      (∃ out, runProgramM fuel ctx.program D.fid.key (D.captures.val ++ argv z).toArray choices = .ok out ∧
        ValuesTyped rts out.values.toList ∧ out.output = .empty ∧
        ∃ s₀ s₁ ch₁, InitRun ctx fuel choices s₀ s₁ ch₁ ∧
        ∃ ls sf chf, Safe.NormalRun ctx fuel (entryState D s₁ (argv z)) (entryConfig D s₁) ch₁ ls sf chf ∧
          EntryResultsAt D s₁ sf out.values.toList ∧
          φ z out.values.toList (Safe.Obs ctx O.obs (entryState D s₁ (argv z)) (entryConfig D s₁) ch₁ ls)) ∨
      (∃ first rest text, runProgramM fuel ctx.program D.fid.key (D.captures.val ++ argv z).toArray choices =
          .error (.panic text) ∧
        ∃ s₀ s₁ ch₁, InitRun ctx fuel choices s₀ s₁ ch₁ ∧
        ∃ ls sf, Safe.AbortRun ctx fuel (entryState D s₁ (argv z)) (entryConfig D s₁) ch₁ first rest text ls sf ∧
          EntryPanicState D s₁ (ψ z) first rest text sf
            (Safe.Obs ctx O.obs (entryState D s₁ (argv z)) (entryConfig D s₁) ch₁ ls)) := by
  exact C2Acceptance.programAcceptance assembly GF (FS := FS) O hinv cp GInit init D argv Pre pre φ ψ z ht exitSilent code fuel choices
#print axioms originalAcceptance
end
end GoLean.Logic.ProgramExecution
```

Save as `OriginalAcceptance.lean`, compile to a private output root with `-o`,
print its axioms, and replay `OriginalAcceptance` with that root first in
`LEAN_PATH`. See the [independent review](2026-10-15-c2-consumer-audit.md) for
checked source hashes and the exact six-module independent replay scope.

Remove these private clones and outputs when finished; retain the source
recipe and conclusions in git. No live dependency pin is changed.
