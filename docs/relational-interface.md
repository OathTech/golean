# Relational interface

Import `GoLean.Relational`; open `GoLean.GoCore.Relational`. This is an
initial surface for a small logic demo, not a replacement for all existing
adequacy roots. Build semantic arguments over the contracts below, then use
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
| Block entry | `block_enter` | Allocation, heap growth, old-cell and outer-binding preservation. Silence does not imply purity. |
| Memory | `PreservesOutside`, `write_support`, `allocate`, `write_read_root` | Whole-root write support, explicit normalization, allocation above the old bound. Separate from race instrumentation. |
| Commutation | `root_writes_commute` | Two successful writes to different root cells, fixed normalized values, no allocation/output/control effects. Not an `unseq` theorem. |
| Terminal boundaries | `Boundary`, `Completed`, `.realize`, `panic_run_iff`, `deadlock_run_iff`, `.rendering_refusal` | Exact panic/deadlock driver correspondences and sound rendering refusal; actual panic chain, terminal records and finishing cost 0/1. |
| Fuel exhaustion | `Exhausted`, `exhaustion_iff` | Exactly the available number of transitions, ending somewhere that cannot finish at zero cost. A different choice may finish earlier. |
| Selected faults | `LocalFault`, `.no_successor` | Unsupported statements, declarations, unbound locals/addresses, binding reads and Boolean conditions; actual stop cause. Not exhaustive. |
| Local entry | `LocalEntry`, `.total`, `.deterministic`, `.layout`, `.declared` | Supplied store; ordered success/error cases for binding, allocation and pinning. Distinct-id, arity and non-interface-anchor premises explicit where needed. |
| Local run | `LocalNormalRun`, `local_normal_iff` | Normal body completion with still-fallible readback; final values separate from return events. |
| Initialization | `Initializes`, `initializes_iff`, `init_print_at_zero` | Exact successful guarded run. Printing refuses even at zero fuel. No premise that all alternative paths avoid printing. |
| Program success | `ProgramNormal`, `.realize`, `program_normal_of_run` | Both directions for the successful sequential driver: validation, globals, initialization, entry and readback. Separate init/body fuel bounds. No pool/CLI claim. |
| Entry events | `EntrySite`, `Enters`, `.transition`, `.all_successors` | Seven sequential call/defer sites; resolved callee, supplied arguments, pre-store. Re-dispatch is not entry. |
| Initial return events | `ReturnsDiscarded`, `.pure` | Normal exits without targets/results after cleanup drains, payload `[]`; includes deferred and top-level frames. |
| Invariants | `WellFormed`, `Run.preserves_wellFormed`, `Run.heap_size_mono` | Address bound and heap normalization, with initial premise. Not typing or refusal freedom. |

`Tests/RelationalContracts.lean` composes a symbolic conditional using source
views and laws alone, checks finite realization, and checks allocation silence
versus purity. This is an upstream semantic contract test. The representative
Iris program proof remains downstream.

`Pure` concerns the store and `StepLabel` only. A client may observe control
as well: `ReturnsDiscarded.pure` is the concrete example of a base-label
pure step with a return event. Use `PureFor` with the chosen observation
projection before deriving an observation-free logic rule.

## Limits that matter to the demo

The foundational `State` still contains machine control. `Continuation` and
source views hide ordinary frame bookkeeping, but `EntrySite` still exposes
concrete configurations. This is not insulation from every representation
change. Report where the demo needs raw control details so the next construct
law can remove that dependency.

`Boundary` is **not exhaustive**. Ordinary operation refusals and fatal
failures still need an independent failure relation. `LocalFault` covers
only its named sites; its absence does not establish safety. Existence of
an arbitrary successful successor does not exclude refusing choices. Use
the proved pick-free progress result only where its premises hold. Do not
weaken a logic root or silently add `MachineWf`/`NoRefusal` to bypass this gap.

`ProgramNormal` is the successful-program subset, not the requested
all-outcome bridge. Setup failures, initializer failures, body faults,
fuel exhaustion and readback failure still need unified relational program
classification. Entry/readback errors are retained in the local API and the
init-print boundary is proved separately. Existing internal driver proofs
retain complete executable classification while that relation is built.

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
