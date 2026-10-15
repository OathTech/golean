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

## Interface and early checkpoint

[AGENT] 2026-10-15: compose semantic phase carriers with C1 local executions.
Retain separate optional initialization/body segments and an explicit failure
phase/cause. Keep tapes, successful executable prefixes and program-driver
names in correspondence propositions/proofs. The common supplied budget is
passed in full to each local phase, not split or subtracted across phases.

Early checked interface checkpoint:
`bd2e6c391778d3ca7cbac92fbafdfa7e586655c6`. At that pin the candidate carriers
and named obligations live in `experiments/2026-10-15-program-outcomes/`.
Its two theorem declarations compile, print standard axioms and replay exactly.

The implementation now exports `GoLean.GoCore.Relational.ProgramExecution`
through `GoLean.Relational`. Semantic carriers live in
`GoLean/GoCore/RelationalProgramOutcome.lean`; bridge statements and closed
proofs live in `RelationalProgramOutcomeSound.lean`. The experimental constraint
is retained as a facade-only client of its exact original bridge propositions;
`Tests/RelationalProgramOutcomes.lean` checks those same propositions in the
default build. No axiom, hole or assumed instance supplies an obligation.

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

The production modules, facade and clients compile warning-free. Closed laws
are:

- `Correspondence.coverage : Coverage`: for every program, name, arguments,
  fuel and selected tape, there exist history, outcome and semantic suffix with
  `Execution`, exact `HistoryReplay`, and equality to the projected driver result.
- `Correspondence.realization : Realization`: every admitted execution is
  realizable with any prescribed final suffix, preserving the supplied history.
- `Correspondence.initialization_coverage` / `.initialization_realization`:
  component correspondence for arbitrary context, supplied store and budget,
  retaining absent/malformed/executed initialization and exact wrapping.
- `Correspondence.setup_coverage` / `.setup_realization`: ordered validation,
  empty-store globals, initialization and activation, including every failure.
- `Correspondence.initialization_projection`: `initStop e = markInitPhase e`.
- `Correspondence.refusal_exclusion : RefusalExclusion` and
  `.fatal_exclusion : FatalExclusion`: separate transfers from semantic
  `Avoids` over all alternatives and budgets. Coverage has neither premise.
- `normal_iff`: semantic successful existence is equivalent to the existing
  `ProgramNormal` with independent initialization/body label-length bounds.
  This is behavior-set compatibility, not equality of an arbitrarily supplied
  original success history.

The default facade client supplies the four exact early obligations, a generic
selected-history realization, and the normal-body/readback composition law.
Its controls cover lookup before invalid type prefix, arity before invalid
prefix, malformed initializer before fuel, exact initialization wrapping and
priority over main failure, ordinary initialization failure after the fuel
guard, and three init steps plus three main steps succeeding with budget three.
A valid print reaches the initialization guard with no remaining fuel and is
refused before exhaustion. C1's existing local clients remain in the build.

Full CI/differential and whole-project exhaustive axiom/replay checks pass.
Fresh independent implementation review has completed with no concrete semantic
or proof defect; exact-pin confirmation follows the implementation commit. No C2 completeness or consumer acceptance
claim is made yet. C1's completed scope and audit remain at their unchanged pins;
its success-only `ProgramNormal` and earlier RD5 contracts are retained.

[USER] 2026-10-15: consume the exact RD6 `C2.ProgramPhases` batch from logic
implementation `bbb372e2b97eec663f55a01ee4993f98be829e1b`, reviewed handoff
`e584674d3b62042c5f082318dc8332ab96593b47`, under the existing charter. Preserve
the exact supplied tape, budgets, errors and original premises. Retain
`InitAssembly` as a downstream Iris parameter; `InitInvocation` is already
proved and is not another request.

The initial upstream implementation is
`fcebf85ccabd4caae101ac656b3ae149caf02f70`, independently confirmed at that pin.
The concrete consumer batch below is now being checked. Do not infer an Iris
initialization-assembly proof or live migration from this semantic development.

## Validation at the implementation source freeze

- Default build: PASS, 220 jobs, warning-free; all 396 interpreter checks pass.
  Existing core totality audit: PASS, covering all 92 `GoLean/` modules and
  imported local declarations, including the new facade client.
- All headline/client axiom reports contain only the standard trio.
- Exact kernel replay: PASS for 93 GoLean modules including the root and the
  four named Tests modules, 97 total. Requested and replayed name sets and
  multiplicities agree: no missing, extra or duplicated module.
- Frozen GoLean-only RD5 A–F adapters: PASS, 64 jobs; seven headline laws and
  all 67 local request/adapter/audit declarations use standard axioms only.
  Replay of all three request modules, two adapters and scratch audit passes.
  The inputs are unchanged at logic `8cf7c1652587366f324c1159a89d72cd0d297cf8`.
  No fresh downstream Iris result is claimed.
- Independent implementation reviewer: separate rebuild/replay of the two
  production modules, facade and client; all 281 owned declarations checked
  with standard axioms only. Additional independent ordering, output and
  inversion controls pass. No concrete semantic/proof defect found. This is
  separate evidence from the author's full CI and RD5 regression.
- `scripts/ci --diff`: PASS, 1,073 seconds. Fresh differential: 3,989 cases,
  3,749 PASS and 240 tracked FAIL; all 405 negative cases pass. Both full
  baseline comparisons report no regression. Scheduler whole-tape checks and
  derived-artifact comparisons pass. The run certifies the precommit source
  freeze; its metadata honestly records the dirty worktree, then the immutable
  commit is compared with the reviewed source hashes.

The first CI invocation's citation **speedbump failed** because it enumerated
the tracked early constraint during its temporary relocation. The retained
facade-only constraint restored that path; rerunning `scripts/check-spec-anchors`
passes (1,108 spec, 262 memory and 26 Go documentation citations). No gate was
waived or weakened. The original speedbump red is not relabeled as a pass.

The shell supplied `TMPDIR=/home/mike/projects/golean/.tmp`; existing CI
scripts used it for transient script-owned manifest scratch, then removed those
files. Reproduction below explicitly scopes `TMPDIR` to the lane. No logic or
concurrency worktree, tracked primary source or live pin was modified.

## Preparatory review disposition

The independent phase-interface review examined exact checkpoint `bd2e6c39`,
compiled it and independent ordering/budget controls, and replayed both modules.
It found no concrete carrier mismatch; this is not the final implementation
review. The control source has been incorporated into the maintained facade
client, where the author also rebuilds it.

**R1 — readback reachability:** answered with explicit scope. Successful body
execution does not make arbitrary supplied result locations readable: the
component control combines a zero-cost normal execution with failing readback.
The generic `after_normal_body` client also constructs the whole-program
readback-failure case from an actual `Setup`, body execution and readback
failure. Neither is presented as a concrete program reaching an invented bad
store. Whole-program readback-failure reachability or impossibility has not
been proved. The unrestricted coverage theorem retains this branch, without
assuming readback success. This remains a limitation of the concrete control,
not an established impossibility or a weakened program correspondence claim.

## Concrete RD6 acceptance batch

All 106 package files were copied from the immutable logic implementation
before building into the lane's private `.tmp/c2-consumer`. Original request,
consumer and target SHA-256 hashes:

- `ProgramRequests.lean`: `b0c77eebeff8a50e2a597fb5b8ebe218d98580100bdaeb5a2f5301ba06ab9a91`.
- `ProgramConditional.lean`: `a3f9c2579768f6f1049399ff5d9ff846294ebf528311b39b4934c4e6226857c7`.
- `ProgramFrozen.lean`: `d9db7e3e008a1e455e9620e033a5152c80bd7acee0c55dc55b4647a926aeaeab`.

`ProgramExecution.Correspondence.phase_projection` is the general checked
boundary corollary. It consumes `Validation`, `Seeding` and `LocalEntry`
soundness through the checked `setup_eq`; it does not narrow `coverage`.
The original seeding equation derives the actual seeded-state guard internally.
The full supplied fuel is retained in both local drivers, the supplied tape
is unchanged, and init/body/readback errors propagate exactly. No successful
initialization, no-refusal or additional well-formedness premise is introduced.
The activation function remains arbitrary and total on supplied stores, as in
the frozen request; the downstream `entry_ready` derives that premise from
its original typed argument/definition hypotheses, including captures and bases.

The exact GoLean-only adapter already compiles:

```lean
import RelationalCodeX.ProgramRequests
namespace C2Acceptance
open GoLean GoCore Relational
theorem phases : RelationalCodeX.C2.ProgramPhases :=
  ProgramExecution.Correspondence.phase_projection
theorem invocation : RelationalCodeX.C2.InitInvocation := RelationalCodeX.C2.initInvocation
#print axioms phases
#print axioms invocation
end C2Acceptance
```

Both print only standard axioms; exact replay of the request, adapter and
updated correspondence module passes. After adding the theorem, upstream fast
CI passes in 139 seconds, including the exhaustive core audit and all speedbumps.
The fresh corpus evidence above is retained for the unchanged operational
sources; the integration adds only this theorem and an axiom print, without
changing the carriers or executable semantics.

`invocation` checks the existing compatibility
law; no new upstream initialization wrapper is introduced. The private full
acceptance supplies `phases` to `program_phase_acceptance` and to
`closed_program_init_outcomes_conditional`. Its program target retains
`(assembly : InitAssembly)` explicitly. Full aggregate/consumer validation and
fresh independent consumer review are in progress.

## Reproduction

From this worktree using the installed pinned Lean 4.32.2 toolchain:

```sh
TMPDIR="$PWD/.tmp" LEAN_NUM_THREADS=2 capped scripts/ci --diff
LEAN_NUM_THREADS=2 capped lake env lean Tests/RelationalProgramOutcomes.lean
TMPDIR="$PWD/.tmp" LEAN_NUM_THREADS=2 capped scripts/check-core-audit
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean \
  Tests.RelationalContracts Tests.RelationalOutcomes \
  Tests.RelationalProgramOutcomes Tests.GoCoreAudit
```

The core audit discovers every `GoLean/` source module on disk and checks all
imported local declarations, including generated/private declarations and the
new facade client. The allowed axiom set remains `propext`, `Classical.choice`,
`Quot.sound`. No newer `lake check` claim is made for this toolchain. Exact
replay names and multiplicities are compared with the GoLean source set plus
the four named Tests modules.

The early checkpoint can be independently reproduced at `bd2e6c39` with:

```sh
mkdir -p .tmp/c2
LEAN_NUM_THREADS=2 capped lake build GoLean.Relational
LEAN_NUM_THREADS=2 capped lake env lean -o .tmp/c2/ProgramOutcomeConstraint.olean \
  experiments/2026-10-15-program-outcomes/ProgramOutcomeConstraint.lean
LEAN_NUM_THREADS=2 LEAN_PATH="$PWD/.tmp/c2" capped lake env leanchecker \
  ProgramOutcomeConstraint
```

The same commands at the implementation pin instead check the four completed
facade bridge obligations. The original checkpoint remains independently
consumable; it is not rewritten.

Frozen RD5 semantic regression uses logic
`8cf7c1652587366f324c1159a89d72cd0d297cf8` read-only. Follow the
[RD5 reproduction](2026-10-14_relational-composition-acceptance.md#reproduction)
in independent scratch, copying `CompositionRequests`, `ContinuationRequests`
and `ResidualRequests`, and both documented exact adapters. Require this
GoLean worktree by local path; build both adapters, print their headline axioms,
audit all owned request/adapter declarations, and replay those five local
modules. This is a GoLean-only A–F regression, not a new Iris acceptance run.

## Remaining work

Initial upstream implementation and checks are complete and independently
confirmed at `fcebf85c`. Finish the relayed consumer acceptance and its fresh
review at an immutable pin. The downstream Iris `InitAssembly` remains a real
premise and is not part of the upstream request. The readback control's
reachability limitation above is retained.

Sequential finite program correspondence remains distinct from full observed
adequacy, CLI/frontend correctness, concurrency, infinite-run bisimilarity,
locality and sequentialization. All heavy commands use `LEAN_NUM_THREADS=2`
and `capped`; disposable artifacts are removed after conclusions are recorded.
