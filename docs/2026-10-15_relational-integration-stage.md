# I1 development integration

[USER] 2026-10-15: rebase this development lane onto current main and integrate
reviewed D1 under the relayed integration charter. Preserve immutable inputs,
current-main behavior/checks and exact customer contracts; validate and obtain
fresh independent review. No main merge, push, live repin or peer writes.
The landing target remains the full replacement reasoning interface for finite
non-concurrent runs, demonstrated with golean-logic. RD7 plus integration does
not meet that target. Concurrent/infinite extensions must remain possible.

## Immutable inputs and reconciliation

All input refs below were created before rebasing, under `refs/integration/i1/`:

| Ref suffix | Commit |
| --- | --- |
| `main` | `31a6069d9dd457e1adb0b3a6060713002ab50480` |
| `c2-implementation` | `626faca5a26f57fbf367aa9655e2aef08f20143a` |
| `c2-handoff` | `826fb7fbfd9b6f7747116913efffa0097b78b3d2` |
| `d1-implementation` | `9c6efcfcf9dc6f4b96cf6b2d8bb052f1fa4d9124` |
| `d1-handoff` | `b4282cffc19dbb092c3c54bd83d56996a808ba45` |

The author lane and primary checkout were tracked-clean on inspection. C2's
25 commits were rebased onto the recorded main; result
`1c91f59ff9a9c74d1ee44d5efad75a96c17ca618` is also retained at
`refs/integration/i1/rebased-c2`. Main and historical D1 branches are untouched.

[AGENT] 2026-10-15: resolve the two changelog conflicts by retaining all
current-main rows and both relational rows. No code conflict occurred.
The automatic script/charter merge retains main's kernel-replay and extern
checks while preserving the authorized equation-API removal. No new standing
rule or toolchain change is introduced.

D1's carry, implementation and handoff commits (`6f27dc09`, `9c6efcfc`,
`b4282cff`) are applied together without changing their historical branches.
The facade and inventory merge includes both C2 and detector contracts.
Stale small-demo/consumer-pending descriptions are corrected; the historical
stage and audit documents continue to describe their immutable inputs.

## Checked implementation

Integration implementation: `5d8e53e9f1a046fb645fce49901de714591e0819`.
It descends from the recorded main and contains the rebased C2 plus reviewed
D1 implementation/acceptance. The final handoff commit changes documentation
only; consumers pin this implementation.

## Validation and acceptance

Full current-main `scripts/ci --diff` passes in 1,233 seconds: 226 build jobs,
warning-free; exact replay of all 96 GoLean modules; exhaustive core audit;
396 interpreter tests; frontend/Go/boundary checks; and whole-tape scheduler
checks. Fresh differential: 4,025 cases, 3,767 PASS and 258 tracked FAIL.
Fresh negative: 415/415 PASS. Both full baseline comparisons report no
regression or cause drift; no baseline is repinned. All speedbumps pass.
The old 3,989-row results are not used for this combined-tree claim.

This run correctly records a dirty precommit source tree. Its tested code,
configuration and script hashes are checked against the implementation commit;
the source-freeze evidence is not mislabeled as an exact-commit CI invocation.
All 370 frozen code/configuration/script hashes match committed blobs at
`5d8e53e9`; the reviewer independently matches 122 reviewed Lean sources to
that pin. All 29 relational core modules and the program-outcome acceptance
client are byte-identical to C2. Main frontend, CLI, corpus, baseline and
replay/escape-scan files and the D1 production/experiment Lean sources retain
their recorded input contents.
Use lane-local temporary directories/caches, `capped` and `LEAN_NUM_THREADS=2`.
The cold full CI run deliberately uses the documented 64 GB cap.

RD6 compatibility uses frozen logic `bbb372e2b97eec663f55a01ee4993f98be829e1b`
and reviewed handoff `e584674d3b62042c5f082318dc8332ab96593b47`, copied into
private scratch following the C2 reproduction recipe. The two consumers
retain their original premises and explicit downstream `InitAssembly`.
All 106 original inputs match, except the private dependency pin and three
appended library targets; no original Lean source is edited.
RD7 completed while I1 validation was running: immutable implementation
`f314a4f7ce69f8e5dc1c835298d4f1a2832a996f`, reviewed handoff
`97426cab7c87ca52a5e3c480c9cb9b30ac534dde`. In accordance with I1, its
113-file package is separately frozen into `.tmp/i1-rd7`; only its private
GoLean pin changes. Its original C2 pin and worktree are untouched.
Both private builds pass (412 jobs each). RD6's direct aggregate audit covers
5,940 local declarations and its acceptance wrapper 5,943; RD7's direct
aggregate covers 6,058, all standard axioms only. Both preserve closed RD5
Add/Alias/Pair/Set/Keep and frozen compatibility. The sole build warning is
the inherited unused `h` in `GoLeanIris/Memory.lean:1625`. The recorded live
**FAIL: 35 NOT-PUBLIC** remains visible and unchanged; no live gate is rerun
or claimed green. Exact dependency replay results are recorded below.

## Trust and design limits

D1's comparator preservation remains checked defining equations and uniqueness,
reviewed generated-source correspondence, and finite executable controls. It
is not kernel equality to the old opaque constant. Its 16 remaining findings
are individually open in the D1 stage; their freshly checked combined-tree status and concrete
dependencies are recorded below. Neither a green axiom audit nor kernel
replay waives those implementation findings.

I1 is a development checkpoint. Complete observations, general locality,
useful unseq sequentialization, broad customer replacement and load-bearing
trust obligations remain required before landing. Paths are not atomic under
interference; local sequential outcomes imply no global pool termination or
deadlock. Full concurrent/infinite adequacy is later work, while compatible
steps/prefixes, effects, choices, observations and scheduling boundaries are
requirements now. No agreed guarantee is dropped because its proof is hard.


## Concrete compatibility inspection

The combined `Transition` is still one labelled `Step`, and `Run` is its
fuel-free closure with `append` and `split`. Every step's full `StepLabel`
remains available. `StorePath.step` quantifies over every store satisfying its
fact and exposes one transition plus the remaining path; `StoreEffect` exposes
one operation-related pre/post store pair. `OrderedWrites` retains order and
intermediate stores. None makes a whole path atomic or supplies stability of
its fact against other threads. C1/C2's bounded driver outcomes sit above these
relations and do not impose termination on the underlying steps.

Existing `StepML` and `StepsML` retain per-thread attribution, scheduling
consultations and spawn/pair actions. `PoolPrefix` remains counted and records
the driver's continue/window choice and successful detector fold on each step;
it has no global fuel/termination premise. `PoolDeadlock` has a separate global
condition. The reuse experiment exposes the concrete `Ordinary` schedule and
thread premises, proves that a variable read is not itself a scheduling switch,
and reconstructs a read after an actual successful disjoint-root write. Its
rendezvous example retains an actual changed post-handoff read. These are
useful compatibility checks, not general pool lifting or infinite adequacy.

The public facade still exposes foundational machine control in `State` and
some source views. Later observation/locality/unseq work must remove remaining
consumer bookkeeping where appropriate without hiding effects or scheduling
boundaries. I1 introduces no new specialized fixture API.


## Remaining implementation dependencies

A fresh declaration-value dependency probe on the combined build reaches no
unresolved opaque-generated endpoint from `raceUpdate`. From `stepFn`,
`stepMulti` and `runProgramM` it reaches `instReprTy.repr`,
`GoLean.instReprGoValue.repr` and `instReprExpr.repr`. More specifically,
`preprintDispatch` reaches the value printer, `unseqAtom` reaches the value
and expression printers, and `valueEq` reaches the value and type printers.
The probe follows kernel-visible declaration values and stops at opaque
endpoints; it does not certify their compiled bodies or their further
implementation dependencies.

Consequently exact executed error/printing correspondence, including the
remaining observation/panic-printing coverage, must account for those renderers
before the full replacement claim lands. The closed C1/C2 kernel theorems
relate the operations/constants as defined; replay and standard axioms do not
supply missing compiled-implementation correspondence for an opaque operator.
Derived expression/statement `BEq` remains separate from the proved
`Expr.eqbF`/`Stmt.eqbF` tower: any wider consumer using the derived equality
needs its own lawful contract or the existing checked tower. Seed-value and
Declaration-family representation findings remain open for contracts observing
those representations; this integration supplies no rendering theorem and
claims no absence of hidden dependencies through opaque printers.

The archived-C1 comparator/shadow/detector control was rerun against the
combined candidate: complete output matches byte-for-byte. This supports the
preservation argument but does not prove equality to the old opaque constant.
The independent review additionally ran its own regenerated-comparator control;
those results are separate evidence in the review.


The combined D1 audit freshly reports **21,777 declarations, standard axioms
only**, and separately **implementation scan FAIL: 16 unwaived findings**.
Each reported name was compared against the D1 table; none is missing or added,
and `instOrdLoc.ord._unsafe_rec` is no longer an unresolved endpoint. The
individual current dispositions follow (all names end in `._unsafe_rec`):

| Declaration prefix | Current status and dependent contract |
| --- | --- |
| `GoLean.GoCore.instBEqExpr.beq` | **Open:** generated structural expression equality and composite instances. Not used by the detector fold. The checked comparison tower uses `Expr.eqbF`/soundness (`SyntaxEqb.lean`); this is not a lawfulness theorem for the derived instance. Future consumers using `==` on expressions need such a contract or the checked tower. |
| `GoLean.GoCore.instBEqStmt.beq` | **Open:** corresponding statement equality/composite instances; the checked tower uses `Stmt.eqbF`/soundness. No derived-equality adequacy claim. |
| `GoLean.GoCore.instReprTy.repr` | **Open:** type rendering, including `valueEq` refusal diagnostics reached from `stepFn`. Not in `raceUpdate`; exact diagnostic correspondence remains an adequacy obligation. |
| `GoLean.instReprGoValue.repr` | **Open:** value rendering, including `preprintDispatch` and malformed-operation diagnostics in the executed semantics. Not dismissed as unobservable; general text correspondence remains unproved. |
| `GoLean.GoCore.instReprExpr.repr` | **Open:** expression rendering, including `unseqAtom` refusal text. Not in the detector; future exact refusal-text claims must account for it. |
| `GoLean.GoCore.instReprStmt.repr` | **Open:** statement rendering, including nested syntax representations. No total representation correspondence supplied. |
| `GoLean.GoCore.Machine.instReprSeedValue.repr` | **Open:** seeded-fixture value representation. The detector consumes emitted keys/clocks, not this representation. Future claims observing seed-value rendering need a total account. |
| `GoLean.GoCore.Declaration.instReprTy.repr_1` | **Open:** takes `Declaration.Ty`, in the mutual printer family generated by deriving Repr for Ty. Identity uses `Ty.eqb`, not this printer. No total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprTy.repr_2` | **Open:** takes `Declaration.Field`, in the Ty-derived family; displays member/type/tag data. Identity uses `Field.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprTy.repr_3` | **Open:** takes `Declaration.Method`, in the Ty-derived family; signature identity uses `Method.eqb`. No total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprField.repr_1` | **Open:** takes `Declaration.Ty`, in the separate mutual family generated by deriving Repr for Field. Identity uses `Ty.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprField.repr_2` | **Open:** takes `Declaration.Field`, in the Field-derived family; identity uses `Field.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprField.repr_3` | **Open:** takes `Declaration.Method`, in the Field-derived family; identity uses `Method.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprMethod.repr_1` | **Open:** takes `Declaration.Ty`, in the separate mutual family generated by deriving Repr for Method. Identity uses `Ty.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprMethod.repr_2` | **Open:** takes `Declaration.Field`, in the Method-derived family; identity uses `Field.eqb`. No detector dependence or total rendering theorem. |
| `GoLean.GoCore.Declaration.instReprMethod.repr_3` | **Open:** takes `Declaration.Method`, in the Method-derived family; identity uses `Method.eqb`. No detector dependence or total rendering theorem. |


D1 acceptance on this combined source: build PASS (79 jobs, warning-free);
all headline laws use standard axioms. The original positive executions and
unconditional `Concurrency.Sync.pre_pair_rejection` compile unchanged. Exact
replay of all eight experiment modules plus the four relational Tests clients
passes (12 names, each exactly once). Every one of the audit's 76 imported
project/experiment modules is in CI's 96-module GoLean set or that eight-module
experiment set. No dependency is omitted by splitting these replay scopes.


RD7's new frozen consumer closes `initAssembly` and the exact original
initialized-program outcome theorem, using C1/C2 and the downstream Iris
assembly. I1 consumes that proof as an immutable customer acceptance; it does
not move Iris reasoning upstream or change the historical RD6 conditional
consumer. Its supplied source and existing review distinguish one-world Iris
sequencing, unchanged observer/history premises and actual driver coverage
from remaining boundary bookkeeping and opaque renderer obligations. The
full replacement landing threshold is unchanged by this additional example.

## Final acceptance and review disposition

At `5d8e53e9f1a046fb645fce49901de714591e0819`, exact full dependency replay
passes with successful exit and complete module multiset equality: RD6 403
modules (96 GoLean, 101 local including the three acceptance clients, 206
Iris/Batteries/Qq dependencies); RD7 406 (96 GoLean, 104 local, the same 206
dependencies). Every module occurs once; every GoLean/local source module has
a built output. Direct headline axiom reports cover 141 RD6 and 155 RD7
theorems, with only the standard trio (two in each require no axioms).

The unchanged public semantic exports include unrestricted
`ProgramExecution.Correspondence.coverage` and `realization`, and the exact
RD6 adapter `ProgramExecution.Correspondence.phase_projection`.
`RelationalCodeX.C2.initInvocation` is reused downstream. The frozen RD6
program consumer keeps `InitAssembly`; RD7's
`GoLean.Logic.ProgramExecution.initAssembly`, `closed_program_init_outcomes`
and `original_program_acceptance` close the original initialized-program
contract without assembly or pending-law parameters. Original observer,
history, typing, ReturnSilent, seed and program premises remain; this does not
turn the logically guarded customer theorem into unrestricted safety.
Unrestricted all-program semantic outcome coverage remains the primary API.

D1 adds the actual location comparator's checked equations, general shadow
order/lookup/preservation laws and `PoolPrefix.shadow_ordered` /
`PoolPrefix.preserves_lookup` through the facade. The selected positive
executions and unconditional reached-state rejection remain controls, not
all-schedule adequacy. No fixture-specific semantic export was introduced.

Fresh independent review rebuilt the five inspected upstream modules,
all eight concurrency modules, all three RD6 acceptance clients, all six new
RD7 modules and two reviewer probes in separate outputs, with exact replay
of each scope. It independently checked the original RD7 header, exhaustive
local axioms and eight proof-body dependencies linking program assembly and
adequacy to the actual C1/C2 coverage exports. It also inspected the author's
full CI and complete dependency replay evidence; it did not rerun the full
differential corpus independently.

Finding **I1-R1** (stale scope/acceptance descriptions) is **fixed**: the public
guide now distinguishes completed C2/RD6 conditional acceptance, RD7's closed
assembly, and the unfinished replacement landing target. The fresh review
records no remaining new integration finding. The 16 individually listed
implementation findings remain **open and unwaived**, along with the Memory
warning and recorded live NOT-PUBLIC failure; green mathematical checks do
not dispose of them.

See the [independent review](2026-10-15-relational-integration-review.md) and
[reproduction instructions](2026-10-15-relational-integration-reproduction.md).
This handoff provides a pin for subsequent customer uptake, not main landing. Main,
historical audited refs and peer worktrees remain unchanged; there is no
merge, push or live repin. Disposable private packages, builds and logs are
removed after recording these conclusions.
