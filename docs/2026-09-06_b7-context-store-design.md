# B7 implementation design: fixed context, mutable store, preserved behavior

[AGENT], 2026-09-06. Design within the approved typed-consumer sprint's
K1/K3 scope; no representation implementation has started in this lane.
The coordinator agreed with the fixed-context API, heap-only store, and
context-indexed Iris expression wrapper. This document adds no user gate
and waives no existing completion criterion.

Authority: [charter §4](2026-09-05_typed-consumer-sprint-charter.md),
[master plan §3.A and §7](2026-09-05_master-plan.md), and the Platform
obligations in `GoLean/GoCore/Platform.lean`. The charter explicitly separates
pure B7 correspondence from I1's earlier refusals, superseding the older
combined-work-item wording. The broad proposed reasoning-surface contracts
are historical design inputs; rejected context laws and general admission
claims are not revived by this migration.

## Starting point and dependency checkpoint

The accepted helper increment proves actual Boolean storage/setup at
`f251abcb`. The exact `BooleanInitialization` module and the runtime lane's
`BooleanControlTyping`, `BooleanControl`, `BooleanInvariant`,
`BooleanPreservation`, `BooleanProgress`, and `BooleanSafety` implementations
were inspected as work in progress. Their current declarations guide this
plan; inspection is not acceptance or a claim that their integration gates
have passed. The [design source inventory](evidence/2026-09-06_b7-design/source-inventory.json)
records the exact snapshots and worktree status.

Begin representation edits only after exact setup and the Boolean invariant
have been reviewed and integrated. Freeze the migration's before-commit
after any separately reviewed panic-rendering repair has landed. O2 can
continue using the stable contract shapes while the split is developed, but
final B7 integration must carry both required recovery fixtures and customers.

The current `ExecState` has five immutable tables (`types`, `functions`,
`methods`, `methodSets`, `typeDisplays`) and one dense-array heap. Choices are
already external. `MultiConfig` contains threads, shared state and the current
thread; race state and output are driver data. The heap representation,
address identities, control constructors and scheduler policy need no change.

## Concrete target API

Use one immutable `ProgramCtx` with a `program : Program` and explicit
`platform : Platform`, exposing read-only projections for the five tables.
Keeping the program in one field avoids two copies of the function/type
tables and retains the global declarations used by setup. No admission proof
is silently required by constructing a context: malformed hand-built input
must still reach the existing explicit boundary checks. A boundary helper
constructs a context from the program and selected platform.

`Store` contains only `heap : Array HeapCell`; `Store.nextAddr` remains the
array size. It has no program, platform, choice tape, output buffer, race
history, or thread array. Core functions that read immutable facts take
`ctx : ProgramCtx`; their mutation results contain only a store. Indicative
signatures, preserving existing constructor/result order where practical:

```lean
stepFn (ctx : ProgramCtx) (s : Store) (c : Config) (ch : Choices) :
  Except Stop (Config × Store × Choices)
Step (ctx : ProgramCtx) : Config → Store → Config → Store → Prop
Steps (ctx : ProgramCtx) : Config → Store → Config → Store → Prop
runConfig (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) :
  Except Stop (Store × Choices)
runProgramSetupAt (ctx : ProgramCtx) (fuel : Nat) (name : String)
    (args : Array GoValue) (ch : Choices) :
  Except Stop (Config × Store × List Loc × Choices)
```

The actual definitions must remain structurally/well-founded recursive;
these sketches do not license a new evaluator or a successful-run premise.
`StepM`, pool stepping, consumption projections and bounded pool drivers
likewise receive a fixed context; `MultiConfig.shared` becomes `Store`.
Default public driver wrappers select `gcAmd64` once and use the same context
for setup, execution, observation and readout. Core operators must not quietly
select that default again.

Pure type/normalization/default/rendering queries receive the smallest
immutable inputs they need. `Store.allocCell` and the dense-array allocation
primitives need no context. Path-based `loadLoc`/`storeLoc` and runtime
operations receive context where they consult types or normalization.
Preserve current allocation behavior, including its existing lack of generic
allocation-time normalization; fixing that during B7 would invalidate the
representation-only claim.

An `ExecState` record merely containing `ctx` and `store` would still permit
context-changing transitions. A new step implemented by packing an old state,
running the old engine and unpacking it would retain the old design. Neither
is the final implementation. A read-only old-state representation belongs
only in the migration correspondence evidence.

## What the existing contracts become

| Current surface | Required migration |
|---|---|
| `BoolRoot`, `BoolHeap`, `EnvRoots`, `NamesPresent` | Heap and environment predicates over `Store`; every hidden binding still checked. No new ownership or value-preservation claim. |
| `SameContext` and `Extension.context` | Remove from the live runtime contract: `ctx` is shared by type/signature. Keep only compatibility lemmas in migration evidence. `Extension` retains typed heap and nondecreasing size. |
| `initialEnv`, `initialResults`, exact binder/allocator equations | Preserve names, allocation order, argument/result offsets, actual argument values, initial false values, and distinctness under the same admission premises. No address renaming. |
| `Inv context results s c` | A store/control invariant under the fixed semantic context, retaining heap, pinned roots, typed continuations and `MachineWf`; drop only context equality. Preserve `Covers` versus `EnvRoots` and staged sequence initialization. |
| `Inv.step`, `Inv.steps`, progress and bounded safety | Same quantifiers over every relational successor, arbitrary choices and fuel. Preserve terminal-before-step checking, explicit fuel-out, actual `runConfig`/`loadMany`, and the Boolean unchanged-choice/silent-output statements. |
| State/configuration bounds | Prove equivalence before removing the identically zero stored-function-body term and the already proved vacuous `itersNormalized` conjunct. Heap/value/configuration address bounds remain explicit predicates. |
| `Trace`, `PoolTrace`, `ProgramTrace` | Fix context throughout a trace. Preserve legal choice realization, consumed and residual choices, event order, terminal/refusal/fuel classification and output. |
| Iris `Ghost.ContextEq` | Remove context equality from mutable state interpretation after the language itself fixes context. Heap ownership remains exclusively in the customer. |

The current Iris `Language` instance is keyed by `Config`. Giving that same
instance type an unconstrained context argument would make two programs'
languages ambiguous. Introduce a genuine customer-side structure
`Expr (ctx : ProgramCtx)` containing the actual `Config`, with the language
instance on `Expr ctx` and `Store`. A reducible alias to `Config` is
insufficient. The wrapper adds no semantic step and is erased by a direct
relation theorem. Retain the adapter's existing normal-terminal value and
uncaught-panic policy; this is not an `EctxLanguage` or unconditional bind-law
change. Test two contexts in one Lean file to challenge accidental instance
capture.

## Platform threading without a new fidelity claim

The old machine is pinned to `gcAmd64`. The correspondence theorem therefore
specializes the new context to that same platform. A parameter appearing in
a record is insufficient: migrate `IntKind.normalize` and `bits?` callers,
type-directed normalization/conversion, arithmetic and shifts, integer
construction at runtime, `tySizeBytes`, allocation-size/int-limit checks,
channel header checks, and their proof/driver consumers. Produce a dependency
census to detect remaining runtime reads of the global `platform`.

`tySizeAlignTy` currently accepts a platform but its four sync arms return
literal pairs: mutex `(8,4)`, RWMutex `(24,4)`, WaitGroup `(16,8)`, Once
`(12,4)`. Represent those layout parameters explicitly and retain these exact
default values. Do not infer another target's layout by scaling amd64
constants. Parameter-sensitivity kernel tests should exercise integer width,
allocation limits, ordinary layout and all four sync layouts; these establish
that the parameters are used, not Go conformance for an invented platform.

Keep Go1.26.5/Lean4.32.2 pins, frontend `go/types` sizing and the default CLI
behavior fixed. A second supported architecture still needs its own coherent
platform, frontend/oracle setup and differential evidence. A `gc386` fidelity
claim is outside this migration and the existing host-capability ruling.

## Kernel correspondence and reviewable implementation order

First retain a source-bound before-model for proof comparison. The proof must
refer to definitions from the frozen before-commit, not define “old step” as
the new step through a conversion. Prefer an audit-only namespace containing
the old changed runtime definitions and their complete changed-dependency
closure; share genuinely unchanged syntax/value/control definitions. Preserve
the original source inventory and record the mechanical namespace/import
transformation. Do not copy unrelated old proof infrastructure or place this
reference engine in the executable customer path. Its imported declarations
need the same foundational-axiom audit. Prototype one load/store and one
choice-sensitive step correspondence before committing to a large rewrite;
this checks the cost and adequacy of the reference mechanism early.
Independent review must verify that the reference snapshot is unchanged
modulo the recorded name/import transformation; proving correspondence to an
edited substitute would not establish preservation of the frozen baseline.

The concrete migration units are:

| Files / dependency family | Work and local completion evidence |
|---|---|
| `Platform`, `Value`, `Ops` | Thread layout/width inputs through the full operator call graph; prove default-platform helper equations and parameter-sensitivity controls. `Syntax.Program` remains the source data; its I1 constructors stay during B7. |
| `State`, `StateEqb`, `StateWf` | Define context/store and exact representation map; migrate equality and allocation helpers; prove bound-predicate equivalence before simplification. |
| `Machine`, `MachineEqb`, `StepFn`, `MachineSound` | Fixed-context relation and evaluator with matching helper premises; state/result and consumed-choice correspondence; retain soundness/completeness. |
| `Race`, `Multi`, `MultiSound`, `MultiStreams`, `MultiWfSound`, `NPDRF` | Context-parametric pool/detector operations and proofs with unchanged scheduler events, footprints and race outcomes. |
| `Trace`, `PoolTrace`, `ProgramTrace` | Same context across fixed-choice traces, actual driver setup and terminal observations; preserve the counterexamples to invalid converses. |
| `EnumSpec`, `EnumDedupSound`, `EnumDedupCheck`, enumeration/choice-trace/CLI entrypoints | Pass the selected context once; retain search state equality, driver coupling, complete traces and certificate dependency fingerprints. |
| `Admission*`, `Boolean*`, `Interface`, `Tests/GoCore*`, interface/Boolean audit modules | Preserve structural judgment meanings and full claimed theorem families; migrate hand-built state fixtures with explicit context defaults. Expand audits to all new local modules, including the before-model evidence. |
| `spikes/gate-a1`, `spikes/iris-customer` | Context-indexed language and heap state interpretation; transport WP/setup/readout and both recovery fixtures, preserving adapter policy and dependency-poison controls. |

The source inventory includes per-file import edges so runtime/evaluator
dependencies can be migrated before their proofs and customer modules. A
changed CLI construction site is not permission to move frontend refusal
stages during the pure B7 slice. The final import graph must keep the
before-model and Iris outside the executable semantic consumer dependencies.

For fixed `ctx` at the old platform define `pack ctx s` with precisely the
old five context fields and identical heap. Prove store round-trip and old
state round-trip on the fiber agreeing with those fields. An arbitrary
`ProgramCtx` has globals/platform information that old `ExecState` lacked;
do not claim a bijection between all contexts and old states.

Carry the following proof obligations in dependency order:

1. Exact helper-result correspondence, including each error/panic/refusal
   constructor and diagnostic text; preserve operation order and normalization.
2. `stepFn` result correspondence for every configuration/store/choice stream
   in the stated domain. Successful results preserve the exact configuration,
   heap, consumed labels/picks and residual tape. Error cases also correspond.
3. Both directions of `Step` and `Steps` correspondence with total premises;
   keep the existing soundness/completeness and well-formedness theorems live.
   No equality only on the Boolean fragment can replace this machine-wide
   representation obligation.
4. Pool/extended-step, scheduler, race-update and consumption correspondence,
   including spawn/park/wake, boundary flags, tombstones and main-exit policy.
   Preserve `StepEvent` and access-reporting projections; C1 changes their
   production later.
5. Setup and bounded driver correspondence by the same fuel, entry arguments
   and choice tape, including all refusal guards in the existing order,
   package-initialization/body phase bounds, terminal outcomes, emitted output
   and final pinned readout. Preserve enumeration/CLI setup coupling.
6. Transport Boolean and recovery contracts and both customers, with their
   current audits. Remove live context-equality lemmas and wrapper residue;
   retain a source-bound map from old exports to new exports.

Use focused tests between these slices and full prescribed CI/differential
gates for runtime commits. If a correspondence proof exposes a wrong answer,
stop that slice, record a red witness, and send the repair through its separate
review lane before freezing a new before-commit. No baseline change, weakened
invariant, altered refusal, or dropped trace field can discharge B7.

## I1 companion and the current marker inventory

I1 follows as a separate change/evidence set. The master plan's current
`Value.lean:202` citation names `Refusal.unsupported`, which is an outcome and
must remain. The actual executable-IR removal inventory is:

| Carrier | Current site | Intended action |
|---|---|---|
| `Expr.unsupported` | `Syntax.lean:304` | Refuse at lowering instead of constructing executable IR. |
| `Assignee.unsupported` | `Syntax.lean:319` | Same. |
| `Stmt.unsupported` | `Syntax.lean:530` | Same. |
| `Ty.unsupported` | `Value.lean:585` | Same, including nested type occurrences. |
| `TypeDef.opaqueDecl` | `Syntax.lean:76` | Relocate legitimate reserved opaque runtime-error information to an explicit context fact; other unsupported declarations fail at the boundary. |

Thus the historical “five” comprises four `unsupported` IR constructors and
the opaque declaration carrier. It does not authorize removal of model
refusals. `TypeEnv.reserved` currently uses opaque index 1 for runtime-error
payload identity. Preserve that semantic identity, the empty-struct entry,
reserved-prefix checks, type indices and runtime-error behavior; do not turn
the sentinel into an ordinary user struct or delete its runtime meaning.
Keep display metadata separate from type identity.

Before editing I1, census emitter/lowerer construction sites and all deep
consumers (`Ty.mentionsUnsupported`, equality/type-resolution/normalization,
admission and rendering). Determine exactly which currently emitted artifacts
contain markers, including unreachable bodies. Run GoLean lowering on
negative wire/source controls. Record each case's old/new status and stage,
cause, and unchanged supported meaning; Go-oracle compile rejection is not
GoLean rejection evidence. No PASS may become refusal to simplify this work.
If preserving the reserved descriptor needs an unresolved semantic-policy
decision, isolate that issue under charter §7; O4 remains incomplete.

## Evidence gate and the outstanding capture gap

The [sealed preflight](evidence/2026-09-06_typed-preflight/README.md) establishes
all baseline gates and a practical full-manifest capture mechanism, but is
at `10fefeb3`, before any renderer repair. Freeze fresh before/after capture
inputs at the actual B7 base. Compare full case status/stage with the existing
baseline policy and exact observation/choice bytes with the capture tool.
Freeze wire inputs and their diagnostic paths, record every status/refusal/
timeout, and retain all bytes; never normalize away semantic data. Slow
certificate reuse remains explicitly cached unless freshly re-certified.

BUG-090's `strings/trimspace-repeat/repeat-bound-refused` has no completed
observation/choice capture despite the original five 240-second attempts.
The current comparator deliberately fails whole-capture completeness on it.
This design does not change that result or declare a timeout equivalent to
the missing trace. Machine-wide correspondence would cover the modeled
execution mathematically, but accepting that plus an explicit measurement
gap as the charter's capture criterion is still a review decision, not a
decision this plan makes. Preserve the gap through implementation and closing
review; report B7's measured scope precisely.

Final integration requires source-bound ordinary/fresh full CI, admission,
interface, A1, A2, Boolean and recovery gates; existing detector/certificate
obligations when their consumers change; both-sided byte evidence with its
explicit completeness verdict; kernel correspondence and dependency audits;
and an independent adversarial review. Main merge and push remain unapproved.

The resulting C1 handoff should name the fixed-context/store API and list
root/path loads and stores, aggregate materialization/copy, map/channel
payload accesses, allocation/defaulting, atomic/sync operations, pairing and
wake writes, `Race.stepAccesses`, and sequential/pool consumption projections.
For each family record its store/context inputs, typed/bounds premises and
existing access-reporting site. C1's new emitted access trace and its
`accesses_eq_stepAccesses` proof are the next block's work, not a B7 shortcut.
