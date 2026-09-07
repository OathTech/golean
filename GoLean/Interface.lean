import GoLean.GoCore.Trace
import GoLean.GoCore.PoolTrace
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.Admission
import GoLean.GoCore.BooleanTyping
import GoLean.GoCore.BooleanStore
import GoLean.GoCore.BooleanSetup
import GoLean.GoCore.BooleanInitialization
import GoLean.GoCore.BooleanPool
import GoLean.GoCore.RecoveryAdmission
import GoLean.GoCore.RecoverySuccessfulRuns
import GoLean.GoCore.RecoveryChoices
import GoLean.GoCore.RecoveryProgramObservation
import GoLean.GoCore.RecoveryCallLayout
import GoLean.GoCore.RecoveryObservation
import GoLean.GoCore.StringPanic
import GoLean.GoCore.RecoveryTerminal
import GoLean.GoCore.RecoveryPoolObservationTyped

/-!
# Experimental semantic consumer interface

Import this module for `GoLean.Semantics`' choice-labelled sequential trace,
detector-checked pool trace, complete program-driver bridge and observations.
It has no dependency on Iris, the frontend, or either customer package.

* `iter_iff_trace` describes exactly `n` successful steps at a fixed stream.
* `run_ok_iff` relates sequential success to a trace bounded by the supplied
  fuel, retaining both initial and residual choices. `Trace.erase` yields
  unlabelled `Steps`; no converse to erasure is supplied.
* `Pool.run_iff` includes detector state, main-exit choices, output prefixes,
  terminal outcomes, refusals and fuel exhaustion for the current driver.
* `Pool.program_run_iff` includes executable setup and result-cell readout.
* `Pool.observation_iff` quantifies fuel and choices on both sides and keeps
  normal readout or terminal output. Refusal and exhaustion are not observations.

These are correspondence theorems about the current machine. They do not
establish Go frontend correctness, termination, refusal
freedom, scheduler completeness, generic context laws or Iris adequacy.

The separate opt-in `GoCore.Admission.checkBoolean` API checks exactly
`IndexStructure ∧ Entry ∧ BooleanSyntax`, as proved by `checkBoolean_iff`.
It checks all syntactic type indices, Boolean entry arguments, and every
function body against the small Boolean syntax policy. It is not invoked
automatically by the frontend or drivers. It does not check lexical typing,
definite return, general name validity, method-set/display metadata, or
typed runtime states. An admitted unbound-variable program can still refuse;
the core regression suite proves this boundary. The A2 recovery program is
outside this first profile. There is no general `Accepted` guarantee here.

`GoCore.BooleanTyping.checkTypedBoolean` is a separate, stronger opt-in
profile. Its sound/complete checker enforces Boolean lexical typing, scoped
declarations and the stated structural return policy. It preserves A3a's
weaker meaning. `GoCore.BooleanRuntime.setup_boolean` derives actual driver
setup success and typed argument/result storage already from A3a; it preserves
the choice stream and accounts for allocated cells. `loadMany_bool` proves
typed readout from valid pinned roots. These storage facts alone do not prove
typed control, preservation, progress, or refusal freedom during execution.

`BooleanRuntime.setup_typed_exact` strengthens entry setup under scoped
admission: the actual driver constructs a canonical environment/heap and
distinct result pins, with `MachineWf` and typed storage established. The
`initialEnv_*` and `initialState_*` lemmas expose exact argument bindings,
argument values and initially false result cells.

`BooleanRuntime.setup_typed` and `setup_typed_exact_inv` now derive the
structural runtime `Inv` from the stronger admission. `Inv.step` preserves it
for every relational successor, and `Inv.reachable_progress` gives a legal
continuation or normal terminal. `runProgramPool_typed` covers the shipped
whole-program driver: Boolean readout at the declared arity with empty output,
or explicit fuel exhaustion with empty output, for every supplied stream.
`Inv.pool_eq_runConfig` keeps the same fuel, store, residual choices and byte
prefix; `Control.singleton_step` pins empty event picks/output. `Inv.run_choices`
and `Inv.success_contract` retain the original stream in successful execution
and counted traces. No termination bound or Iris ownership is manufactured.
These are Boolean-profile guarantees, not general admission or recovery
safety. See `docs/2026-09-06_boolean-program-contract.md` for their premises.

`GoCore.RecoveryTyping.checkRecovery` checks the separate, bounded recovery
profile against an independent judgment, with soundness and completeness.
It checks all signatures/bodies, scoped bindings, call and capture vectors,
deferred registrations and a finite call-graph certificate. Surface/placement
diagnostics are proved consequences of typing and do not narrow admission.
This static contract admits the complete A2 and shared-capture native fixtures.
Its own claims remain those in `docs/2026-09-06_recovery-static-claims.md`.

`GoCore.RecoveryRuntime.setup_typed_wf` connects that admission to actual
program setup, canonical argument and zero-result cells, typed environments,
result locations and structural `MachineWf`, for every setup fuel and choice
list. `enterFramePick_typed` supplies reusable actual call/defer entry from
typed incoming arguments and heap, preserving root aliases and the original
choices. `ResultRoots.load` and the `initialState_*` contracts expose actual
typed and exact initialized readout; `EnvTyped.pushedDecls` handles block
allocation with heterogeneous shadowing. These entry/storage guarantees do
not establish whole recovery control preservation, renderer success or Iris
ownership. See `docs/2026-09-06_recovery-entry-contract.md`.

`RecoveryRuntime.setup_inv` additionally establishes the structural recovery
invariant from actual admitted setup. `Inv.step` preserves it for every
relational successor; `Inv.reachable_progress` distinguishes normal terminal,
a nonempty semantic abort, and a legal successor. Call/defer entry and actual
direct/indirect recovery have reusable control contracts. Successful
`runConfig` executions have typed pinned-result readout, retain their original
choices, and traverse configurations with no print events. These successful-
execution facts remain separate from termination. No Iris resources or
functional result are provided by typing.
See `docs/2026-09-06_recovery-control-contract.md`.

`RecoveryRuntime.setup_layout` and `enterFramePick_layout` expose the actual
argument/result allocation, environments and result pins used by both
customers. Captured pointers preserve root identity; allocating their slots
does not supply ownership of the pointee. `Inv.pool_eq_runConfig` gives the
same-fuel singleton driver correspondence with unchanged output prefix, and
`Inv.loop_all_choices` transfers a successful run to every original list.

The recovery profile's whole-driver TERMINAL classification
(`RecoveryRuntime.Inv.run_classified`, `runProgram_typed`,
`runProgramPool_typed`; landing chunk L3,
`docs/2026-09-07_land-panic-text-tape.md`) has FOUR outcomes for every
admitted run, fuel and stream: typed readout with empty output; a `panic`
terminal whose text is `Machine.stringPanicHead` — the explicit-string
MEMBER function — at the collapse bit the stream's `repanicCollapse` pick
selects; the NAMED refusal `Stop.unsupported (Machine.abortRefusal …)` of a
string payload whose FIRST LINE is not valid UTF-8 (landing decision D5: gc
writes the raw bytes and the `String`-valued observation cannot carry them);
or fuel exhaustion. `Inv.run_refusal_named` / `runProgramPool_refusal_named`
say the third outcome is the ONLY refusal the profile reaches — the sprint's
`*_no_refusal` theorems were true only of a total renderer that emitted a
`"\xHH"` form Go never prints, and are not restated. The computed observer
(`runConfigWithAbort`, `execPoolWithAbort`, `runProgramPoolWithAbort`)
erases exactly to the shipped drivers for every input (`*_erasure`), every
emitted record has a source-bound provenance witness (`*_witness`) carrying
the abort event's own recorded pick (`abortEventPick?`), every actual panic
result in the typed recovery domain receives a record
(`Inv.observation_complete`), and every record's text is the member at some
collapse bit (`Inv.observed_abort_member`, `stepAbortRecord?_member`,
`runProgramPoolWithAbort_member`). The member's bytes are the payload's
first line (`utf8String?_bytes`, `stringFirstLine?_bytes`).

Both typed profiles are CHOICE-FREE on every STEP: `Control.no_spawn`,
`Control.no_select`, `Control.no_seq_consumption` (a `none` projection, or
an ABORT) and `Inv.run_choices` (in `BooleanRuntime` and `RecoveryRuntime`
alike) mean a successful execution retains its stream verbatim. The
recovery profile's ABORT is not choice-free since landing chunk L3: on the
recovered-equal re-panic shape (`Tests/RecoveryTyping.lean`'s
`repanicProgram`) the abort draws the `repanicCollapse` pick and the
terminal text is genuinely two-valued (`Tests/RecoveryTerminal.lean`'s
`equal_repanic_two_members`) — the first TYPED two-outcome driver
demonstration; the untyped `two_choice_pool_bridge` in
`Tests/InterfaceContract.lean` remains the driver↔relation one, and the
2026-09-05 gate audit's F2 stays OPEN for the typed contract in that sense.

The profiles' grammars (exactly what each admission judgment admits, and
what it excludes) are stated in `docs/2026-09-07_land-typed-core-proofs.md`
until the sprint's contract notes cited above land with the records chunk.

The underlying `GoCore` and `GoCore.Machine` types remain representation
dependent. This facade is experimental: B7, C1 and the composition work may
change that representation. A customer must state any stronger domain and
observation assumptions explicitly. See the dated interface design note.
-/
