# Relational interface

Import `GoLean.Relational`; open `GoLean.GoCore.Relational`. This is an
developing reasoning surface with checked construct laws and complete bounded
local/sequential-program outcomes. Full replacement of the customer's finite
non-concurrent reasoning interface remains the landing target; the current
integration checkpoint does not establish it. Build semantic arguments over the contracts below, then use
driver correspondence for executable conclusions. No Iris representation is
imported. The implementation request and provenance are recorded in
`2026-10-13_relational-surface-refactor.md`.

## Checked contracts

| Contract | Main exports | Scope |
| --- | --- | --- |
| Labelled finite execution | `Transition`, `Run`, `.append`, `.split`, `.realize`, `run_iff_prefix`, `of_prefix` | Direct closure of `Step`; no tape/evaluator in the carrier. Exact labels, one realizing tape, arbitrary residual. No infinite-run/fairness claim. |
| Determinism | `Transition.deterministic_by_picks`, `Run.deterministic_by_picks` | Equal per-step pick records imply equal successful endpoints and full labels. |
| Pick-free progress | `PickFreeProgress.run` | Every reachable point is normal or has a pick-free step; every tape returns normally or exhausts fuel. No `MachineWf` assumption. This is a sufficient deterministic-fragment domain. |
| Control | `Pure`, `.unique`, `PureFor.all_successors`, literal laws, `conditional`, sequence laws | Store preservation, silent base labels, existence and uniqueness, symbolic store and continuation. `PureFor` adds silence under the client's observation projection. |
| Variable read | `read_variable` | Binding lookup and successful `loadRoot` imply the source transition, with its actual continuation-dependent trace, no picks/output and unchanged store. |
| Sequence entry | `sequence_splice` | Pure entry of `.seqn ss` into a governing sequence with the same environment; preserves arbitrary tail, store and continuation. |
| Pointer assignment | `assign_pointer_variables` | Source `*p = v` from symbolic variable lookup and read/write operation premises; arbitrary target `Loc`, including interior and aliasing cases; actual ordered labels, each pick-free and output-free. No general assignment claim. |
| Declared call/return | `SavedCaller`, `CallBoundary`, `NormalExit`, `SavedCaller.enter`, `.invoke`, `CallBoundary.deliver` | Store-preserving pick-free operands, bound-variable destinations, no pending defers. Entry, independent callee body and ordered readback/writeback compose without client frame/target/signal construction. |
| Uniform store phases | `StorePath`, `.trans`, `.weaken`, `.run`, `StepAdmission`, `StoreEffect`, `OperandPaths` | Every traversed source is nonterminal and init-admitted; every path step preserves each store satisfying its fact. Actual labels remain pick-free, with no observer-silence claim. Final controls are unrestricted. |
| Assignment/entry phases | `pointer_assignment_phases`, `variable_assignment_phases`, `SavedCaller.entry_phases` | Existential write/activation boundaries independent of stores; successful operations justify the effect. Assignment suffixes require no pre-write read facts. Symbolic aliases/interiors and arbitrary argument lists retained. |
| Ordered delivery phases | `OrderedWrites`, `.run`, `CallBoundary.delivery_phases` | Snapshot all results before ordered write effects; repeated/interior destinations, both normal exits, arbitrary caller tail. Root result validity comes from activation; read facts are not retained after writes. |
| Read-only RHS composition | `ReadOnlyExpr`, `.weaken`, `.variable`, `.reference`, `.int_literal`, `.deref`, `.add_int`, `variable_expression_phases`, `pointer_rhs_phases` | Uniform over stores and continuations, preserving intermediate stores/admission. General RHS for a bound variable or `*p`; typed integer normalization, interior dereference. Assignment address-former chains and other operators are not covered. |
| While control | `WhileControl`, `while_control` | Real admitted entry step; Boolean selection and normal/unlabelled continue/break/return paths. No body/tail safety, invariant, termination or full-loop theorem is assumed or supplied. |
| Activation result validity | `LocalEntry.resultSlots`, `Readback.traced` | Every successful activation pins root result slots; no signature-distinctness or `MachineWf` premise. The composed call law derives validity internally. |
| Address/variable assignment/return | `reference`, `assign_variable`, `return_start`, `return_sequence`, `empty_sequence_run` | Symbolic semantic premises, actual labels, explicit normal-return exit view and exact cleanup endpoint. |
| Block entry | `block_enter` | Allocation, heap growth, old-cell and outer-binding preservation. Silence does not imply purity. |
| Memory | `PreservesOutside`, `write_support`, `allocate`, `write_read_root` | Whole-root write support, explicit normalization, allocation above the old bound. Separate from race instrumentation. |
| Commutation | `root_writes_commute` | Two successful writes to different root cells, fixed normalized values, no allocation/output/control effects. Not an `unseq` theorem. |
| Terminal boundaries | `Boundary`, `Completed`, `.realize`, `panic_run_iff`, `deadlock_run_iff`, `.rendering_refusal` | Exact panic/deadlock driver correspondences and sound rendering refusal; actual panic chain, terminal records and finishing cost 0/1. |
| Fuel exhaustion | `Exhausted`, `exhaustion_iff` | Exactly the available number of transitions, ending somewhere that cannot finish at zero cost. A different choice may finish earlier. |
| Complete local outcomes | `Local.OperationFailure`, `Local.Finish`, `Local.Execution`, `Local.Avoids`; `Local.Correspondence.main_coverage`, `.main_realization`, `.initialization_coverage`, `.initialization_realization` | Arbitrary supplied context/store/control/budget/tape. Normal, deadlock, admitted panic, every refusal, fatal and selected exhaustion. Exact successful labels, finishing selections and costs; no error-return tape/store invented. Separate refusal/fatal exclusion transfers. |
| Selected faults | `LocalFault`, `.no_successor` | Unsupported statements, declarations, unbound locals/addresses, binding reads and Boolean conditions; actual stop cause. Not exhaustive. |
| Local entry | `LocalEntry`, `.total`, `.deterministic`, `.layout`, `.declared` | Supplied store; ordered success/error cases for binding, allocation and pinning. Distinct-id, arity and non-interface-anchor premises explicit where needed. |
| Local run | `LocalNormalRun`, `local_normal_iff` | Normal body completion with still-fallible readback; final values separate from return events. |
| Initialization | `Initializes`, `initializes_iff`, `init_print_at_zero` | Exact successful guarded run. Printing refuses even at zero fuel. No premise that all alternative paths avoid printing. |
| Program success | `ProgramNormal`, `.realize`, `program_normal_of_run` | Both directions for the successful sequential driver: validation, globals, initialization, entry and readback. Separate init/body fuel bounds. No pool/CLI claim. |
| All sequential program outcomes | `ProgramExecution.Validation`, `Seeding`, `Initialization`, `ActivationPhase`, `Setup`, `Execution`, `History`; `ProgramExecution.Correspondence.coverage`, `.realization` | Arbitrary program/name/arguments/fuel/tape. Exact ordered failure phases and causes, separate initialization/body segments with full independent budgets, labels and finishing selections. Closed refusal/fatal exclusion transfers; no logical safety admission premise. |
| Entry events | `EntrySite`, `Enters`, `.transition`, `.all_successors` | Seven sequential call/defer sites; resolved callee, supplied arguments, pre-store. Re-dispatch is not entry. |
| Initial return events | `ReturnsDiscarded`, `.pure` | Normal exits without targets/results after cleanup drains, payload `[]`; includes deferred and top-level frames. |
| Invariants | `WellFormed`, `Run.preserves_wellFormed`, `Run.heap_size_mono` | Address bound and heap normalization, with initial premise. Not typing or refusal freedom. |

`Tests/RelationalContracts.lean` composes a symbolic conditional using source
views and laws alone, checks finite realization, and checks allocation silence
versus purity. This is an upstream semantic contract test. The representative
Iris program proof remains downstream.

The logic demo's three concrete requests are discharged by `read_variable`,
`sequence_splice` and `assign_pointer_variables`, respectively. Their types
match `ReadVariableLaw`, `SequenceSpliceLaw` and `AssignPointerVariablesLaw`
without stronger premises. The GoLean-only downstream acceptance example
checks with both law parameters supplied, proving its symbolic root-write,
frame, normal-run and progress conclusions. This is still not an Iris
ownership proof. Reproduction and precise scope:
`2026-10-14_relational-demo-laws.md`. The RD3 call/return interface and exact
compatibility checks are in `2026-10-14_relational-call-acceptance.md`.

The RD4 phases expose intermediate preservation, not just equality of endpoint
stores. `OperandPaths` is stronger than RD3's `OperandValues`; the older entry
and invocation laws retain their original domains. A path's `StepAdmission`
records terminal/init guards only; transition existence is supplied separately.
Successful `loadRoot` premises restrict read bindings to root locations; write
targets and variable destinations may be interior and aliased.
The three frozen phase requests and guarded Set/Keep acceptance are recorded in
`2026-10-14_relational-phase-acceptance.md`. Client ownership updates and
observer obligations remain downstream. RD5 delivery/expression/loop adapters
and the exact acceptance scope are recorded in
`2026-10-14_relational-composition-acceptance.md`; the compound uint64 increment
is derived there from expression and assignment exports, not a primitive API.

`Pure` concerns the store and `StepLabel` only. A client may observe control
as well: `ReturnsDiscarded.pure` is the concrete example of a base-label
pure step with a return event. Use `PureFor` with the chosen observation
projection before deriving an observation-free logic rule.

## Detector history contracts

The same facade exports `GoLean.GoCore.LocationOrder`, `ShadowOrder` and
`ShadowHistory` (module names under `GoLean/GoCore/`; declarations live
in `GoLean.GoCore` and `GoLean.GoCore.Machine`). `Loc` and `ShadowKey` have checked `Std.LawfulEqOrd`
and `Std.TransOrd` instances. Location comparison preserves the pinned
derived constructor/component order for arbitrary base, field and index
paths; `loc_compare_unfold` and `loc_comparison_unique` specify the source
algorithm. They do not prove equality to the former opaque constant.

`shadowSet_lookup_self`, `shadowSet_lookup_other` and `shadowSet_other_mem`
give exact replacement/retention observations. `ShadowOrdered` is strict
key order; `.keys_nodup` derives uniqueness. `shadowSet_ordered` preserves
it, and `PoolPrefix.shadow_ordered_empty` establishes it for every actual
detector-checked prefix from the empty detector. `PoolPrefix.preserves_lookup`
retains a key's history across successful prefixes whose events avoid that
exact key, including attributed accesses and HB actions. Different keys can
overlap: the premise is key inequality, not memory separation, and detector
success is still required. Canonicalization erases static field type spelling
at emission; comparison itself is structural on all supplied keys.

These are detector data-structure laws, not a general race-freedom or Iris
ownership theorem. The two retained experimental executions and the now
unconditional negative control are described in
`2026-10-15_relational-detector-contracts.md`, including remaining implementation
findings and the limits of old/new preservation evidence.

## Limits that matter to the demo

The foundational `State` still contains machine control. `Continuation` and
source views hide ordinary frame bookkeeping, but `EntrySite` still exposes
concrete configurations. This is not insulation from every representation
change. Report where the demo needs raw control details so the next construct
law can remove that dependency.

`Boundary` alone and the older `LocalFault` remain non-exhaustive. The complete
local interface is `Local.Execution`, using the concrete `Local.OperationFailure`
for ordinary failures and `Boundary` for terminal finishes. Its classification
needs no `MachineWf`, `NoRefusal` or successful-operation premise. Safety is a
separate claim: `Local.Avoids` quantifies over every reachable admitted prefix
and finishing alternative. Refusal exclusion covers operation, rendering and
initialization refusals; fatal exclusion has its own premise. A successful
successor does not establish either all-choice premise.

`ProgramExecution.Execution` composes validation, global setup, initialization,
activation, body and final readback for all sequential driver outcomes.
`Correspondence.coverage` and `.realization` preserve phase histories and exact
choice replay. Initialization and body each get the entire supplied budget;
the program driver returns neither a tape suffix nor an error endpoint.
`normal_iff` establishes successful behavior-set compatibility with the existing
`ProgramNormal` and separate label-length bounds; it does not assert identity
of an arbitrary supplied original success history. The validated-entry corollary
`ProgramExecution.Correspondence.phase_projection` preserves the exact supplied
tape and both full phase budgets; its exact RD6 consumer acceptance is checked
at the immutable C2 pin. Its entry premises do not narrow unrestricted coverage. This is not an
Iris adequacy theorem or an observation-completeness claim.

The observation API lacks a complete entry census theorem, general target
writeback returns and panic-printing returns. It must not replace the
logic's audited observer/census yet. Panic unwinding is not normal return;
discarded-result frames report `[]` even with a result-bearing signature.

Root support is deliberately coarse. Path non-overlap, context extension
across allocator bounds, a whole-step effect census and general `unseq`
sequentialization remain open. Primitive write commutation does not equate
ordered labels, prove every schedule safe, or supply a WP rule. General
concurrency remains on the existing pool relations; no new pool abstraction
is claimed here.

## Removed interface and separate asks

`Equations`, `EquationsAttr`, `stepFn_eqns`, `Tests.EquationClient`, its target
and `scripts/check-equations` are gone, along with their `BridgeSet` rows
and audit entries. Remaining `BridgeSet` pins are internal regression
contracts. Three setup helpers moved privately into `SetupSound`. The old
pinned logic development continues to use its old revision.

Numeric locals, useful frame/slot/unwinding laws, setup proofs, seeded entry
for the separate consumer, and pool correspondence remain. No executable
Go behavior or differential baseline changes are intended.

Companion asks B/C remain proposals/questions: stable type/package identity,
self-contained `unseq`, field-load lowering, labelled loops, probe retirement,
current raft coverage, recursive type layout and variadic/format lowering.
They have not been silently included here, and old coverage figures have
not been re-certified at this branch.


The RD5 residual comparison/sequence laws are documented with exact adapters
in the [composition handoff](2026-10-14_relational-composition-acceptance.md#residual-ef--full-add-acceptance):
`ReadOnlyExpr.less_int`, `sequence_signal_path`, `sequence_break_path`.
They retain store-uniform paths and source admission; less-than compares the
supplied integer values and sequence propagation leaves the tail unrestricted.


The [C1 local-outcome handoff](2026-10-14_relational-outcome-completeness.md)
records the exact public contracts and checks. Semantic declarations live in
`Local`; tapes and drivers occur in `Local.Correspondence`. `OperationCheck`
composes guard-ordered checks and `Selection` witnesses; passing a check means
only absence of its failure, not a successful transition. Failed operations
have semantic consultation witnesses, while actual error results erase the
endpoint and suffix. Main and initialization coverage/realization are proved
separately, preserving zero-cost normal/deadlock priority, one-step finishing
cost for panic rendering/operation failure, and init-print-before-fuel refusal.
`Tests/RelationalOutcomes.lean` is the facade-only classification, realization
and exclusion client. No Iris or downstream module enters this interface.

The [C2 program-outcome stage](2026-10-15_relational-program-outcomes.md)
records the independently consumable C1 baseline and early interface checkpoint.
`Tests/RelationalProgramOutcomes.lean` checks the exact early obligations through
the facade and exercises ordering, phase budgets and projection. Readback failure
has a generic program composition law and an arbitrary-state component control;
no concrete whole-program readback-failure reachability claim is made.

C2 also exports `ProgramExecution.Correspondence.phase_projection`, checked
against the frozen RD6 `RelationalCodeX.C2.ProgramPhases` request at logic
`bbb372e2b97eec663f55a01ee4993f98be829e1b`. It keeps the supplied tape, full
independent phase budgets and exact errors under the request's original
validation/seeding/total-activation premises. These premises do not restrict
unconditional all-program `coverage`. Both frozen phase and original program
consumers compile with the law supplied; the frozen RD6 program consumer explicitly
requires downstream Iris `InitAssembly`. `InitInvocation` is reused unchanged.
See the stage's independent audit and exact private-package reproduction.

RD7's immutable logic implementation `f314a4f7` supplies that Iris assembly
downstream and closes the original initialized-program contract without an
assembly or pending-law parameter. Its unchanged acceptance also builds on
the combined I1 pin. This is one customer program acceptance, not completion
of the full replacement reasoning interface.

The [development integration stage](2026-10-15_relational-integration-stage.md)
records reconciliation with current main and D1, combined validation and the
remaining landing obligations. Concurrent and infinite-run extensions must
remain possible: transitions and compositional prefixes have no driver-fuel
or termination premise. A store path is a sequence of steps, not an atomic
pool action; read stability under interference requires preservation of its
actual store fact. Access labels, observations, picks and registered scheduling
boundaries remain available to pool reasoning. Selected concurrency controls
do not prove all-schedule safety, fairness or infinite-run adequacy.
