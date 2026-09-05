# Experimental semantic interface

[AGENT], 2026-09-05. The [USER] authorized landing reviewed A2 and BUG-103,
then promoting A1's semantic bridges and implementing the first A3 slice.
This lane starts from A2's landing, `700128f3`; BUG-103 integrates separately.

## Contract before implementation

Move the reviewed `Trace`, `PoolTrace`, and `ProgramTrace` definitions and
proofs into `GoLean/GoCore/`, under `GoLean.Semantics`. Expose them through
`GoLean/Interface.lean`, an experimental import facade with no Iris dependency.
Preserve their statements, including fuel bounds, fixed and residual choices,
detector state, output prefixes, setup and result readout. This is relocation
of existing semantic correspondence proofs, with no interpreter change.

The sequential trace covers successful counted steps; its successful-run
bridge ends at `.next .stop`. The pool trace covers every current driver
outcome and retains the driver's detector and main-exit policy. Its erasure
only goes to pool reachability; no converse is promised. Program observations
include normal readout and terminal output; refusal and fuel exhaustion are
excluded. Setup is an executable premise, not typed admission. These are
finite may-observation contracts, not termination, full Go equivalence or
general Iris adequacy.

Move semantic counterexamples and driver examples into an Iris-free core
regression module. Leave the `Language` instance, Iris resources, WP and
adequacy in the opt-in packages. Migrate customer bridge references to the
facade, and retain exact exported theorem obligations and poisoned-import
audit regressions. A semantics-only audit must cover every promoted module,
private/generated/trailing declarations included, in the ordinary core gate.

The facade exposes existing low-level machine types. It is not a stable pin
or a claim of representation independence. Consumer continuations, heap
normalization, immutable context equality, entry setup and singleton-pool
transfer still depend on internal representation. B7, C1 and composition
work remain owed. A3 is a separate lane; its admission predicate will be
exposed only with an explicit account of its restricted domain.

## Completion criteria

- Core build and ordinary `scripts/ci` pass, with no Iris in their dependency
  graph. No executable or corpus baseline change is intended.
- Semantic regression theorems and a post-import transitive axiom audit pass;
  an isolated compiled forbidden declaration is rejected by that same audit.
- Both opt-in A1 and A2 gates pass; A2's native artifact comparison and three
  differential examples remain intact.
- Record the exact source fingerprint, commands, cache scope, result counts,
  remaining internal dependencies and independent review disposition.

General typed admission, refusal freedom, concurrent adequacy, unconditional
evaluation-context laws and G-PIN are not completion claims of this lane.

## Remaining representation dependencies

| Customer surface | Current dependency and owed work |
|---|---|
| A1 `Language` | `Config`, `Step`, `.next .stop`, `Cont` and `recoverResult`; no generic context law |
| A2 `Heap` | Dense `Array HeapCell`, root addresses as indices, append allocation and whole-cell ownership; B7/C1 must retain the stated lookup/update correspondence |
| A2 `Ghost` | All five immutable `ExecState` context fields pinned by equality; B7 should replace this obligation with an explicit context parameter |
| A2 `Lifting`, `Rules` | `stepFn_sound`, `step_complete`, loads, normalization, store and initialization equations; semantic memory/lifting lemmas still owed |
| A2 `Examples` | Concrete function bodies and continuation constructors, closure/defer entry equations and recovery paths; reusable statement/call composition still owed |
| A2 `Readout`, `Driver` | `runProgramSetupM`, `loadMany`, singleton transfer and zero `seqOpCount`, bounded computation for termination and silence; general labelled/concurrent adequacy still owed |
| Test helpers | A1 imports `Tests.InterfaceContract`; A2's panic control uses its `panicObservation_sound`. These proof regressions are Iris-free but not a stable application API |

The regression namespace `GoLean.GateA1` is retained for example names; the
promoted contract types/theorems use `GoLean.Semantics`. Old A1 bridge files
are import shims, not aliases preserving the old fully qualified names. The
experimental customer is migrated explicitly, and its audit requires the
new names. This is a documented pre-pin API change.
