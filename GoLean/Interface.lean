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
import GoLean.GoCore.RecoveryCallEntry

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

The underlying `GoCore` and `GoCore.Machine` types remain representation
dependent. This facade is experimental: B7, C1 and the composition work may
change that representation. A customer must state any stronger domain and
observation assumptions explicitly. See the dated interface design note.
-/
