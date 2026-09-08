# Recovery structural control contract

> [AGENT] 2026-09-08: historical contract note selected from committed
> `typed-consumer-sprint` at `7edc298f`. The landed definitions and theorem
> statements on main take precedence; current compatibility and limits are
> recorded in `docs/2026-09-08_typed-test-gates-landing.md`. Validation
> counts below belong to the original sprint. Unlanded references are
> identified as paths at that source commit, not as files present on main.


[AGENT] 2026-09-06. Bounded O2 control increment, based on reviewed static
admission, mixed storage, and actual entry at `63769964`. This document does
not claim the complete O2 outcome or the functional Iris customer.

## Statement and scope

`RecoveryRuntime.setup_inv` (module `RecoveryInvariant`) starts with `RecoveryAdmission`, arbitrary
setup fuel and choices, and proves the existing `runProgramSetupM` creates
the structural invariant at the canonical actual environment, heap and
external result locations. The caller supplies neither an invariant nor a
future execution premise.

`Inv.step` quantifies over an arbitrary supplied relational `Step` and
preserves the invariant. `Inv.steps` and `Inv.iter` extend this to all
relational and executable prefixes. `Inv.progress` classifies every such
configuration as normal termination, a nonempty semantic abort, or a
configuration with a relational successor. Successful `runConfig` and
`execStmtLoop` executions have typed readout of exactly the pinned result
arity and retain the original choice stream. Reachable configurations emit
no print events.

The invariant has only structural components: `ProgramTyped`, immutable
non-heap context, `MachineWf`, and an existential address schema connecting
the actual heap, continuation/configuration, and pinned result locations.
It is not defined by evaluation success, a concrete artifact, future
safety, termination, or the ability to prove a WP.

## Control grammar and preservation

The grammar distinguishes source values from intermediate machine values:
typed parameter values, live root addresses, explicit boxed strings, and
statically identified closure values with their complete captured vectors.
Operator frames retain evaluated and pending input vectors and their output
class. Target and RHS frames retain the exact result signature, ordered
plans/references, and pending or already evaluated assignment values.

`ReturnCont` contains a real non-wrapper frame barrier. `ExitCont` also
permits `.stop` and suspended panic chains. A frame with nonempty result
writeback plans additionally requires a real caller `ReturnCont`; actual
ordinary calls discharge it, while entry/deferred barriers have empty
plans. This extra condition was added when frame-exit proof development
exposed an overly permissive initial grammar. Synthetic writeback to stop
and directly to a panic-resume marker are now negative kernel controls.

The joint sequence constructor types the current statement in its actual
pre-context and the remaining statements in its post-context. A sequential
declaration allocates its binding before that tail becomes executable.
Nested `seqn` splices declarations into the same scope; blocks restore their
saved outer continuation. Neutral sequences under the same actual environment
use only the previously proved sort-compatible context union. Declarations
never carry an arbitrary old heterogeneous context across a shadowing update.

Calls use the actual `enterFramePick_typed` theorem. Captured values are
prepended to explicit arguments, pointer slots preserve their live Boolean
pointees, and fresh parameters/results extend the address schema. Deferred
invocations retain their complete typed argument vector and are prepended
to the nearest frame. Normal frame exit and panic unwinding drain that list
using the same actual call entry; deferred results are discarded.

Recovery proofs unfold the real continuation walk. An ordinary called
function blocks indirect recovery; direct recovery changes the newest
suspended panic entry's recovered flag and rebuilds the actual continuation.
Chain typing permits arbitrary GoString bytes, repeated equal payloads,
recovered entries, and re-panic. No ASCII, valid-UTF8, or no-re-panic
restriction was introduced.

The local proof `Advances` is a theorem conclusion: for every choice stream,
the actual `stepFn` succeeds, preserves that stream, and constructs a typed
successor and schema extension. `control_step` applies `step_complete` to
the arbitrary supplied relational successor and then uses this uniform
executable result. It therefore proves preservation for every relational
successor, rather than selecting a convenient successor.

## Boundaries and remaining work

The abort configuration `.panicking (first :: rest) .stop` has no relational
successor. Its conversion to a driver error calls the panic renderer. The
current source may refuse some invalid-UTF8 or repeated-recovered-payload
observations; this increment leaves those payloads admitted and makes no
unconditional abort-rendering or driver no-refusal theorem. That renderer and
observer repair remains an explicit sprint obligation.

Typed readout is a shape/type/arity statement, not the functional answer of
the recovery customer. The shared-root Iris customer still needs reusable
call/defer/unwind rules, alias ownership discipline, functional normal and
recovered contracts, actual observer/pool bridges, and the remaining sprint
audits. The small execution regression is a test, not a replacement for
those reusable proofs. Termination bounds are not claimed here.

## Validation boundary

`Tests/RecoveryInvariant.lean` includes generic kernel controls for malformed
writeback, return-to-stop, empty panic chains, foreign initialization scopes,
dangling target addresses, and nil panic arguments. Generic equations
distinguish LIFO registration, direct/indirect recovery and equal re-panic
history. A small both-input real-driver test checks mixed-type shadowing,
zero initialization, and same-scope sequence declarations. Whole native
A2 and Shared artifacts instantiate the generic setup-to-invariant theorem.

`scripts/check-recovery-control` hashes all fifteen new core modules and
both test/audit modules, builds them, freshly elaborates their source, and
runs a post-import audit over every imported local GoLean/Tests declaration,
including unused private declarations. Its negative controls compile an
unused private axiom in each core module, one in the audit module, and a
trailing test `sorry`, then require the audit to reject each compiled poison.
The ordinary CI invokes this bounded gate. Final execution/review provenance
is recorded in the increment's evidence directory when sealed.

## Public integration

The bounded implementation is independently reviewed at `9e6c4234` plus
reproducibility follow-up `ba930ba2`, and its source is committed at
`f160d7ca`. Four facade/audit promotion files passed independent review
`62377799`. Fresh integrated ordinary CI and both spike gates passed;
the interface checks 102 exports and all twenty-two compiled poison
controls. Source-bound evidence is in
`docs/evidence/2026-09-06_recovery-control-integration/`. These checks
preserve the successful-run and renderer limits stated above. The generic
terminal witness and shared functional Iris customer remain required work.

## Landing compatibility addendum

[AGENT] 2026-09-08. The supporting entry/control modules described here
remain byte-identical to the selected sprint source. Later L3 work has
restated recovery terminal classification over the actual reached abort
record and its choice-selected panic text, with a named invalid-UTF-8
refusal. The historical renderer debts above do not supersede that landed
contract; see `GoLean/Interface.lean` and
[the L3 landing record](2026-09-07_land-panic-text-tape.md). This gate
restoration changes neither those statements nor the admitted profile.
