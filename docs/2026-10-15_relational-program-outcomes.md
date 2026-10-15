# C2: all-outcome sequential program correspondence

[USER] 2026-10-15: proceed under the relayed program-outcomes charter, building
on independently consumable audited C1. Compile an early phase-interface
checkpoint, then complete all-outcome sequential correspondence and use logic's
exact initialized-program constraint before final consumer acceptance. Iris
reasoning and the concurrency repair remain separate. No merge, push, live
repin, peer writes, global changes or standing-rule changes.

Baseline implementation: `55ad72493061b59363e846341380a9edce12a2de`.
Baseline audit/handoff: `cb8f2809b73edccddc5494a422e2c3b2b428180e`.
The lane is `refactor/relational-surface-1013`; no baseline pin is rewritten.

## Candidate interface

[AGENT] 2026-10-15: compose semantic phase carriers with C1 local executions.
Retain separate optional initialization/body segments and an explicit failure
phase/cause. Keep tapes, successful executable prefixes and program-driver
names in correspondence propositions/proofs. The common supplied budget is
passed in full to each local phase, not split or subtracted across phases.

The candidate lives in `experiments/2026-10-15-program-outcomes/` under
`GoLean.GoCore.Relational.ProgramExecution`. It is not exported by the facade
yet. `ProgramOutcomeConstraint.lean` contains the carriers and exact named
coverage/realization/exclusion propositions; `ProgramOutcomeSound.lean` is the
implementation draft. No axiom, hole or assumed instance supplies an obligation.

- `Validation` preserves entry lookup, arity, then reserved-type-prefix order.
- `Seeding` starts at the empty store and retains the actual post-seed validity
  check. Its invalid branch is proved unreachable after successful seeding by
  the existing `SetupSound.seedGlobals_wf`; no well-formedness premise is added
  to coverage or moved ahead of validation/seeding.
- `Initialization` accounts for absence, malformed shape, normal execution and
  every stopped local outcome. Only actual execution errors receive `initStop`,
  which agrees exactly with `markInitPhase`; shape refusal is unwrapped.
- `ActivationPhase` reuses `LocalEntry` and retains the parameter-binding,
  result-allocation and result-location failure sites.
- `Setup` composes these phases in order and exposes the resulting activation.
- `Segment` retains start/end states, actual successful labels, finishing
  selections, local outcome and cost. Its `Runs` is concrete `Local.Execution`.
- `Execution` composes setup, body and fallible readback. `History` keeps init
  and body segments separate. Normal program projection returns only values,
  with empty output, exactly as `runProgramM` does; it does not fold labels.
- `Avoids` quantifies over every admitted program alternative and budget.
  Refusal and fatal exclusions are separate predicates and obligations.

`Correspondence.Coverage` covers arbitrary program, name, arguments, fuel and
selected tape. It yields an execution, exact phase/prefix/selection replay and
the projected driver result. `Realization` realizes each admitted execution
with any prescribed final semantic suffix. No executable result returns that
suffix; errors return neither endpoint nor labels either.

## Status and checks

The early interface checkpoint compiles against the unchanged C1 facade. Its
only two theorem declarations (`Seeding.invalid_unreachable` and
`initialization_projection`) report only standard axioms, and exact kernel
replay of `ProgramOutcomeConstraint` passes. The C1 dependency build passes
54 jobs without warnings. The correspondence implementation is still a draft;
no completed coverage, C2 completeness or consumer acceptance claim is made
at this checkpoint. Full CI/differential checks belong to the implementation
handoff, not this experimental interface checkpoint.

Reproduce from this worktree:

```sh
mkdir -p .tmp/c2
LEAN_NUM_THREADS=2 capped lake build GoLean.Relational
LEAN_NUM_THREADS=2 capped lake env lean -o .tmp/c2/ProgramOutcomeConstraint.olean \
  experiments/2026-10-15-program-outcomes/ProgramOutcomeConstraint.lean
LEAN_NUM_THREADS=2 LEAN_PATH="$PWD/.tmp/c2" capped lake env leanchecker \
  ProgramOutcomeConstraint
``` C1's completed scope and audit remain at their
unchanged pins; its success-only `ProgramNormal` and earlier RD5 contracts are
retained.

The exact downstream `closed_program_init_outcomes` constraint has not yet
been relayed. It is required before final consumer acceptance; upstream work
continues meanwhile. Do not infer an Iris migration or observed adequacy result
from this semantic development.

## Remaining work

Check the interface checkpoint; finish all-outcome coverage/realization and
phase/error/exclusion laws; preserve successful-program compatibility; export
and test facade clients; consume the relayed initialized-program constraint;
run required CI/differential, headline/exhaustive axioms and exact kernel replay;
obtain fresh independent implementation review and disposition findings.

Sequential finite program correspondence remains distinct from full observed
adequacy, CLI/frontend correctness, concurrency, infinite-run bisimilarity,
locality and sequentialization. All heavy commands use `LEAN_NUM_THREADS=2`
and `capped`; disposable artifacts are removed after conclusions are recorded.
