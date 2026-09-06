# Shared recovery customer

This increment makes two complete native artifacts consume the same
admission, setup, call-allocation, recovery and adequacy contracts. The
second artifact's result depends on its Boolean argument and on the order
of two handlers sharing one captured result cell. The complete artifact,
including its indirect-recovery and reversed-order controls, is admitted.
This document describes the draft implementation; acceptance requires its
dedicated gate, source-bound independent review and integration gates.

## Semantic contracts

`RecoveryCallLayout` gives exact equations for actual `enterFrame`,
`enterFramePick` and `runProgramSetupM`. The common vocabulary is
`callEnv`, `callResults` and `callCells`. Argument slots precede
zero-initialized result slots. Result pins refer to those actual roots,
using independently checked distinct signature keys. Setup requires
`RecoveryAdmission`; calls require whole-program typing, actual callee
lookup, an independently typed argument vector and a zero-value vector.
No theorem assumes successful execution of the callee body.

The pure layout equations do not prove that an address stored in an
argument points to a live cell in the actual heap. The runtime invariant
supplies that fact for admitted execution. An Iris client instead supplies
the actual pointee resource when its proof reads or mutates that cell.
Allocating a capture slot creates ownership of that fresh slot only.

`RecoverySingleton` derives the absence of spawn, select, blocking,
registry commits and post-operation flags from the structural control
grammar. `RecoveryPool.Inv.pool_eq_runConfig` then proves equality with the
actual output-folding singleton driver at the same fuel, state, race state,
choice stream and output prefix. It explicitly handles the abort-to-tombstone
transition. It preserves renderer refusals, so this correspondence theorem
does not itself discharge the separately required renderer-totality issue.
`runProgramPool_eq_sequential` derives the initial invariant from admission.

`RecoveryChoices.Inv.no_seq_consumption` checks the actual sequential
consultation projection. The source profile excludes methods, so the
nil-receiver wrapper-text choice cannot occur; the control grammar excludes
the remaining consultation sites. `Inv.loop_all_choices` transfers a
successful run to every other original stream, with the same final state
and that stream unchanged. This is not a general determinism theorem for Go.

## Customer resources and rules

The existing concrete `GoResources` instance supplies Iris ghost state.
`GoGS.context` pins the complete immutable machine context; the state
interpretation owns the actual heap map. It does not hide a typed-control
invariant or a future-success premise inside the Iris resource model.

The generic vector allocator `heap_alloc_cells` exposes each fresh root
once. `wp_alloc_cells_step` lifts an actual, uniform single-step allocation
equation and uses the existing relational uniqueness theorem for every
successor. Ordinary call targets, captured addresses and result writeback
destinations remain explicit. Pointee ownership is framed across the
allocation, not recreated from a copy of the pointer value.

`CallSite` inventories all seven actual frame-entry forms: a nullary direct
call, the last direct-call argument, a nullary closure call, the last closure
argument, and deferred entry during fallthrough, return or panic.
`wp_call` is the common rule for all seven. Callee continuations receive the
actual new environment, result pins and wrapper flag. Deferred barriers
discard the returned pin vector exactly as the machine does.

The recovery rules use explicit local continuation facts. `FrameRecovery`
records the actual `recoverThroughWrappers` result or its absence.
`wp_recover_rhs_frame` consumes that fact at the actual RHS/sequence/frame
position. Indirect recovery requires the ordinary call barrier and returns
nil. Panic stripping, frame exit, chain merge and resumption each have a
named rule over the actual machine operation. No universal evaluation-context
bind law is assumed for call, return or unwinding.

`wp_frame_result` reads an owned pinned result cell and continues into the
actual caller target evaluation and later writeback. It returns the result
cell resource. `wp_deref_cell` separately requires ownership of the pointee.
The kernel challenge `full_root_exclusive` proves that two full ownership
claims for the same address entail false. Shared captures retain one mutable
resource through both handlers and return it once.

## Functional exercise

The existing A2 recovered/normal entry setup uses the same `setup_layout`
as the second customer, for arbitrary fuel and choices. Its ordinary `fail`
call and deferred handler entry use `wp_call`. Recovery uses the reusable
RHS rule over arbitrary panic chains.

The second source is `Tests/recovery-typing-fixture/main.go`; the customer
imports the entire `Tests.RecoveryTypingFixture.nativeRecovery` artifact.
Its ordinary `flip` helper negates a Boolean and returns through an actual
named result. The final deferred handler calls `flip` on the shared result.
The preceding handler first calls an ordinary helper whose indirect
`recover()` returns nil, then performs direct recovery and writes the shared
result when a panic was recovered. Registering the handlers in the opposite
order changes the result, and wrongly effective indirect recovery does too.

`wp_shared` proves the result for arbitrary Boolean input, actual argument
and result root addresses, and old result contents. It composes the common
call/allocation/writeback/recovery rules; it does not reduce a whole evaluator
run or assume the final value. Its concrete `shared_adequate` theorem
allocates the resource model and supplies the actual initial cells.

`adequate_typed_program_all_choices` is shared by both customers. Iris
adequacy supplies the result readout. An independent bounded sequential
success projection supplies termination; the semantic invariant extends it
to every choice stream. The generic same-fuel pool theorem supplies empty
output. Therefore `recovered_program_all_choices` returns true at fuel 60,
`normal_program_all_choices` returns true at fuel 60, and
`shared_program_all_choices b` returns `!b` at fuel 200, for every stream.
These fuel bounds are witnessed for these fixtures; the profile checker
does not claim a general sufficient fuel bound.

The old optional whole-pool reduction that exhausted its cap remains
historical failed evidence. The second customer's new functional proof is
the composed Iris proof. Only its separate bounded sequential termination
projection uses kernel evaluation. Uncaught panic remains a semantic
terminal control, not a universal Iris `NotStuck` claim from admission.

## Reference lessons and validation boundary

The static evidence's `references.tsv` pins refined-cerberus, BRiCk,
RefinedC, archived GoLean experiments, the Go specification and iris-lean.
Refined-cerberus's actual-step/resource-update separation informed the
lifting rule. BRiCk and RefinedC's ordered call vectors and separation of
parameter setup from callee execution informed the common layout. The
archived GoLean proofs reinforced the separation of functional WP,
adequacy, termination and readout; their old entry-frame assumptions were
not reused as facts about the current machine.

The gate freshly elaborates every new local semantic helper and the entire
customer, checks dependency revisions, and audits all imported local origins,
including unused declarations. Its compiled poisons target every new
semantic and customer helper, the aggregate, audit module and trailing
ownership test. Fresh native emission/lowering compares both whole artifacts;
focused differential runs check A2 plus the second fixture's five outcomes.
Those executable checks are compiler/fidelity evidence, not a theorem about
native source translation. Final semantic facade promotion and the complete
typed normal/panic/fuel classification remain separate integration work.
