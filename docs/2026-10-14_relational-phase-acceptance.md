# RD4 phase acceptance — 2026-10-14

[USER] 2026-10-14: implement the concrete phase relay against frozen logic
`a1ddc673e03d91060c51f451dc5cd274916f9a4f` and reviewed handoff
`4c868845ee91c068e63e0c63e78598cf5815b345`. Retain RD3's audited
`95f1eb64ca3bfa3c39fd5aa0792d516e76a31089` as the baseline. No merge,
push, live pin change or logic-worktree writes.

## Exports and exact compatibility

All production exports are in `GoLean.GoCore.Relational`, through
`import GoLean.Relational`. They import no downstream module or Iris.

| Frozen request | Upstream theorem | Checked adapter |
| --- | --- | --- |
| `AssignmentPhases` | `pointer_assignment_phases` | `RD4Acceptance.assignment` |
| `EntryPhases` | `SavedCaller.entry_phases` | `RD4Acceptance.entry` |
| `VariablePhases` | `variable_assignment_phases` | `RD4Acceptance.variableAssignment` |

[AGENT] 2026-10-14: use one `StorePath` for uniform, pick-free,
store-preserving steps with source admission, plus `StoreEffect` for an
operation-derived write and `OperandPaths` for argument preparation.
This exposes the information needed at each downstream state interpretation.
`StorePath.trans`, `.weaken`, `.pure` and `.run` support composition;
`OperandPaths.values` recovers the older endpoint premise at a selected store.

The existing endpoint contracts do not themselves carry intermediate store
preservation or initialization admission. Their internal proofs supply the
transitions used here. The new proofs reuse `read_variable`, `reference`,
`sequence_done` and `LocalEntry.declared`; pointer and variable assignments
share their effect and unconditional suffix. Existing contracts are retained:
notably RD3 `OperandValues` allows runs with equal endpoint stores without
requiring each intermediate store to be equal. Replacing that premise with
`OperandPaths` would improperly strengthen the old caller contract.

Before/after controls are independent of stores; entry's boundary is also
independent of the eventual function and activation. Read facts are used only
before the write. Actual labels, interior locations, arbitrary aliases,
symbolic binders and arbitrary operand lists remain. Every traversed source,
including the write/activation source, has terminal/init guard evidence.
No admission is required of the arbitrary final caller continuation or final
callee body state. Admission alone is not a progress claim, and no statement
infers client-observer silence. All three exact requested statements hold;
no correction or stronger client premise is needed. Successful `loadRoot`
premises restrict read bindings to roots; write targets and variable
destinations genuinely support interior locations and aliases.

## Frozen inputs

Export `experiments/2026-10-14_relational-codex/` from the immutable logic
implementation above. All 59 original files were frozen before implementation;
only the independent scratch `pins.json` GoLean entry selects the candidate.
All original Lean, request and target sources remain byte-for-byte unchanged.

- `RelationalCodeX/Phases.lean` SHA-256:
  `ecaf8f4c43a225b62e34fa368d2b0466899e483640bb1e8989a603f688f37161`.
- `RelationalCodeX/Targets.lean` SHA-256:
  `2e953a5cfe26967d367c25cad9c8545dd0815e06680de53486a5bc762f5c79fd`.
- Lean `v4.32.2`; Iris `e7a0a43814c4f1154ca0c8049883ca56c2288b86`;
  Batteries `023ce7d62a0531e22a5331e20b587817a80d49ff`;
  Qq `38d591e778f100aec9762bb582f9c7f55f50e9dc`.

## Compatibility source

Save this block as `PhaseAdapters.lean` in an independent package containing
the exact frozen `RelationalCodeX/Phases.lean`. It requires GoLean only.

```lean
import RelationalCodeX.Phases

namespace RD4Acceptance
open GoLean GoLean.GoCore GoLean.GoCore.Relational RelationalCodeX

theorem toReadPhase {ctx : ProgramCtx} {fact : Store → Prop} {c d : Machine.Config}
    (h : StorePath ctx fact c d) : ReadPhase ctx fact c d := by
  induction h with
  | refl => exact .done
  | step transition admitted _ ih =>
    exact .step transition admitted.nonterminal admitted.initializes ih

theorem toStorePath {ctx : ProgramCtx} {fact : Store → Prop} {c d : Machine.Config}
    (h : ReadPhase ctx fact c d) : StorePath ctx fact c d := by
  induction h with
  | done => exact .refl
  | step transition hn hi _ ih => exact .step transition ⟨hn, hi⟩ ih

theorem assignment : AssignmentPhases := by
  intro ctx env k pId vId pSlot vSlot target value hp hv
  obtain ⟨before, after, pre, effect, post⟩ :=
    pointer_assignment_phases ctx env k pId vId pSlot vSlot target value hp hv
  exact ⟨before, after, toReadPhase pre, effect.transition,
    effect.admission.nonterminal, effect.admission.initializes, toReadPhase post⟩

theorem variableAssignment : VariablePhases := by
  intro ctx env k dst src target source value hd hs
  obtain ⟨before, after, pre, effect, post⟩ :=
    variable_assignment_phases ctx env k dst src target source value hd hs
  exact ⟨before, after, toReadPhase pre, effect.transition,
    effect.admission.nonterminal, effect.admission.initializes, toReadPhase post⟩

theorem operands {ctx : ProgramCtx} {fact : Store → Prop} {env : LocalEnv}
    {es : List Expr} {vs : List GoValue} (h : OperandPhases ctx fact env es vs) :
    OperandPaths ctx fact env es vs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (fun k => toStorePath (he k)) ih

theorem entry : EntryPhases := by
  intro ctx caller fid es vs fact h
  obtain ⟨before, pre, admitted, activate⟩ :=
    caller.entry_phases ctx fid es vs fact (operands h)
  exact ⟨before, toReadPhase pre, admitted.nonterminal, admitted.initializes, activate⟩

#print axioms assignment
#print axioms variableAssignment
#print axioms entry
end RD4Acceptance
```

The guarded wrapper `ClosedTargets.lean` adds no premises to either target:

```lean
import RelationalCodeX
import PhaseAdapters

namespace RD4Acceptance
open RelationalCodeX

theorem setTarget : SetTarget := set_body_at_acceptance assignment
theorem keepTarget : KeepTarget := keep_body_at_acceptance entry variableAssignment

#print axioms setTarget
#print axioms keepTarget
#eval RelationalCodeX.audit
end RD4Acceptance
```

## Reproduction

Start in a clean checkout of the implementation commit below. Use the frozen
logic repository only as a read source. All build/dependency state is private
to `.tmp`; dependency caches are copied by the frozen setup script only when
source/configuration/toolchain match. Do not use writable shared cache links.

```sh
mkdir -p .tmp/rd4 .tmp/rd4-phases/RelationalCodeX
git -C /home/mike/projects/golean-logic/.claude/worktrees/relational-demo \
  archive a1ddc673e03d91060c51f451dc5cd274916f9a4f \
  experiments/2026-10-14_relational-codex/ |
  tar -x -C .tmp/rd4 --strip-components=2
cp .tmp/rd4/RelationalCodeX/Phases.lean .tmp/rd4-phases/RelationalCodeX/
cp lean-toolchain .tmp/rd4-phases/
```

Save the adapter block in both scratch packages. The semantic-only package's
`lakefile.toml` is:

```toml
name = "RD4Phases"
version = "0.1.0"
defaultTargets = ["PhaseAdapters"]
[[require]]
name = "GoLean"
path = "../.."
[[lean_lib]]
name = "RelationalCodeX"
globs = ["RelationalCodeX.Phases"]
[[lean_lib]]
name = "PhaseAdapters"
```

Run `LEAN_NUM_THREADS=2 capped lake build` in `.tmp/rd4-phases`.
For full acceptance change only the scratch `pins.json` GoLean value to the
implementation commit below, then run from the upstream checkout:

```sh
python3 .tmp/rd4/setup.py --golean-source "$PWD" \
  --seeds /home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages \
  --copy-cache
```

In `.tmp/rd4`, save the guarded wrapper above and append these two library
targets to the frozen `lakefile.toml`:

```toml
[[lean_lib]]
name = "PhaseAdapters"
[[lean_lib]]
name = "ClosedTargets"
```

Then run from that package:

```sh
LEAN_NUM_THREADS=2 capped lake build RelationalCodeX PhaseAdapters ClosedTargets
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose \
  GoLean RelationalCodeX GoLeanIris GoLeanIrisExamples PhaseAdapters ClosedTargets
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose Iris Batteries Qq
```

Compare replay names exactly against all `.golean-ws/GoLean/**/*.lean`,
`.golean-ws/GoLean.lean`, the 52 frozen local Lean sources and both wrappers:
no missing, extra or duplicate replayed modules. The aggregate and wrapper
print headline axioms and execute the frozen exhaustive local axiom audit.
The third-party replay covers every built Iris/Batteries/Qq module in the
independent package caches; compare that replay set to their built `.olean`
files. It includes the acceptance dependency closure, not a claim that every
source module in those repositories was built. Run upstream checks from its checkout:

```sh
LEAN_NUM_THREADS=2 capped scripts/ci --diff
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean
```

The GoLean replay set must equal its source module set, including `GoLean.lean`.
Discard private scratch, caches and CI artifacts after checking; preserve the
committed conclusions and these reproduction inputs, not generated logs.

## Validation status at implementation freeze

The exact three semantic-only adapters build (50 jobs), with standard-trio
axioms only. The unchanged frozen guarded package also rebuilds at the RD3
baseline (307 jobs; 5,571 local declarations pass its exhaustive axiom audit).
That baseline rebuild still has the three law premises: it is not the closed
Set/Keep acceptance. Its pre-existing unused-variable warning in
`GoLeanIris/Memory.lean:1625` is retained rather than editing frozen sources.

Upstream headline axioms and the full core audit pass. Direct kernel replay
passes for exactly 83 GoLean source modules, and separate replay passes for
the 206 built frozen dependency modules (174 Iris, 18 Batteries, 14 Qq).
Full `scripts/ci --diff` passed in 725s (198 build jobs, 396 eval tests,
3,989 corpus cases: 3,749 passes and 240 baseline-known failures; all 405
negative cases; no regression or red speedbump). This certifies the pre-commit
worktree proof/runtime content. A later admission-docstring clarification
was separately rebuilt with the contract/core audits. Fresh independent
review is in progress. The
immutable candidate pin and its closed guarded acceptance/replay results
will be recorded here once checked; no final delivery claim is made yet.
