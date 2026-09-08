# Recovery entry and initialized-storage contract

> [AGENT] 2026-09-08: historical contract note selected from committed
> `typed-consumer-sprint` at `7edc298f`. The landed definitions and theorem
> statements on main take precedence; current compatibility and limits are
> recorded in `docs/2026-09-08_typed-test-gates-landing.md`. Validation
> counts below belong to the original sprint. Unlanded references are
> identified as paths at that source commit, not as files present on main.


[AGENT] coordinator, 2026-09-06. **Bounded entry increment validated and
independently reviewed at `997d74ed`; storage base `4f7aedef`.**
This implements the setup part of O2. The full recovery control invariant,
all-successor preservation, terminal-aware drivers and reusable Iris rules
remain separate requirements. Static admission is unchanged.

## Contract and limits

`RecoveryRuntime.setup_typed_wf` takes the independently defined
`RecoveryTyping.RecoveryAdmission p name args`. It proves the real
`runProgramSetupM` succeeds, for every setup fuel and every incoming choice
list, with canonical parameter cells containing exactly the supplied values,
canonical result cells containing their Go zero values, distinct result
locations, a typed heap/environment and structural `MachineWf`.
It has no setup-success or future-execution premise. The admitted profile
has no globals or package initializer, so setup needs no fuel and consumes
no choices. External arguments retain the existing Boolean-only `Entry`
policy; internal call/capture arguments additionally permit the separately
checked live Boolean roots and payloads.

`enterFrame_typed` and `enterFramePick_typed` take a typed existing heap,
the program context, actual function lookup and typed complete argument
vector. They prove the shipped frame entry allocates parameter/result slots,
extends the world, establishes the callee's actual first-match environment,
pins typed result locations and preserves non-heap context. Every old root
alias remains typed through the world extension. Successful `enterFramePick`
returns the entire original choice list. Its `Result.ok` constructor is
distinct from runtime panic and model refusal. The admitted empty method
table makes dynamic dispatch inert.

The schema allows an arbitrary number of Lean array cells; the model's
allocator in this profile has no additional capacity failure. The setup
theorems expose the exact number of new slots. This is not a physical-memory
resource theorem or an unbounded program-termination claim. The current
driver's default platform remains unchanged; B7 must migrate these APIs to
its explicit immutable context and remove representation-enforced equality
premises without changing the statements' meaning.

Semantic root liveness is weaker than exclusive Iris ownership. Multiple
captures may share a Boolean pointee; each has its own allocated parameter
slot. These theorems grant no duplicate exclusive assertion, ghost resource,
WP, `NotStuck` result or successful panic rendering. Uncaught panic and
invalid-byte/equal-repanic renderer obligations remain visible.

## Claim ledger

All rows below are kernel-proved against the current model. Their source
is under `GoLean/GoCore/`; all auxiliary declarations and imported local
dependencies are included by the dedicated post-import audit.

| Guarantee / definitions and theorems | Source | Domain and explicit premises | Choices, output and status |
| --- | --- | --- | --- |
| `expr_locSup`, `target_locSup`, `arguments_locSup`, `targets_locSup`, `statement_locSup`, `statements_locSup`, `program_funcListSup`, `programState_wf`, `program_no_init` | `RecoverySetupShape.lean` | Independent source typing; no literal preallocated addresses or package initializer in the profile | Structural facts, no execution/output claim |
| `declareMany_append`, `declareMany_lookup_absent`, `declareMany_lookup_member`, `scopeLookup_member`, `scopeLookup_none_iff`, `EnvTyped.initialContext`, `EnvTyped.pushedDecls` | `RecoverySetupShape.lean` | Exact first-match lookup; distinct signature/block keys; all hidden bindings remain typed | Reconciles source ordering with actual reverse declaration order; allows outer heterogeneous shadowing |
| `ZeroValues`, `.exists`, `.typed`, `.length`, `.unique`, `boolean_type_eq`, `payload_default`, `parameterCells`, `parameterCells_length`, `bindParams_exact`, `allocDecls_exact`, `ParamsValues.booleans` | `RecoveryInitialization.lean` | Real typed argument vector or structurally specified Boolean-false/interface-nil zeros; no zero live pointer | Actual helper equations, exact cells and allocation order; no body execution |
| `ResultRoots`, `.length`, `.mono`, `.load`, `pinResultLocs_typed` | `RecoveryResultRoots.lean` | Typed real addresses; typed heap for readout; actual environment lookups for pinning | Actual `loadMany` success with typed result vector; no termination premise manufactured |
| `initialState`, `setup_typed` | `RecoverySetup.lean` | Full static recovery admission, actual external argument array | All setup fuels/choice lists; exact initialized state/environment/pins; unchanged choices; no output phase |
| `ValueTyped.locSup_le`, `HeapTyped.heapLocSup_le`, `BindingsTyped.locSup_le`, `typedState_wf`, `typedEntry_wf`, `setup_typed_wf` | `RecoverySetupWf.lean` | Source typing plus typed heap/environment and explicit context identity; admission supplies these at setup | Structural address well-formedness and actual setup success, not full runtime safety |
| `initialState_argument`, `initialState_result`, `loadMany_of_lookup`, `initialState_readout` | `RecoverySetupReadout.lean` | Explicit argument/result lengths and location bounds | Pointwise exact values and complete actual initialized-result readout; no final-body claim |
| `enterFrame_typed`, `enterFramePick_typed` | `RecoveryCallEntry.lean` | Whole-program typing, actual callee lookup, typed current heap/argument vector, same program context | Exact ordinary/deferred entry helper; all incoming choices preserved; world extension, typed cells/pins and slot count |

The two customer families remain independently authored native artifacts.
Tests apply the same generic setup to all three A2 entries and both values
of `Shared`, including the uncaught-panic entry whose later outcome is not
`NotStuck` in the current Iris adapter. Additional kernel controls cover
mixed result zeros, exact argument readout, colliding signature rejection,
pointer-shaped external arguments, empty-signature/fuel-zero setup, actual
capture slots and a block that shadows an outer Boolean with a payload.

## Validation and integration obligations

`scripts/check-recovery-setup` builds and freshly elaborates all seven
semantic modules plus tests/audit, then performs a post-import axiom sweep.
Compiled poison controls cover every new semantic module, an unused private
declaration after the audit definition, and a trailing test theorem. It is
wired into ordinary CI. The final dedicated gate passed with 37 required
exports, 11,241 checked declarations and all nine compiled poison controls.
Ordinary CI completed with exit 0, including 202 evals. The independent
review freshly checked eight additional kernel probes; no blocking finding
remains within this entry scope. Tracked source-bound evidence is in
`docs/evidence/2026-09-06_recovery-entry/`. Full corpus records used by this proof increment are
explicitly cached renderer evidence, verified against unchanged runtime,
frontend and harness source. Final sprint runtime gates remain mandatory.

The integration facade now imports these reusable contracts, with expanded
module/export/poison coverage. Public promotion passed independent review
`29ac266d`, fresh ordinary CI, the full recovery native gate, Gate A1 and
the Iris spike gate. The public audit checks 84 exports and rejects all
19 compiled poisons. Separate source-bound promotion evidence is in
`docs/evidence/2026-09-06_recovery-entry-integration/`; the original entry
evidence remains bound to its earlier source. There is no stable-interface
claim. The recovery control author consumes the same
`ResultRoots`, block lookup and actual call-entry contracts; custom fixture
entry-state assumptions are not an alternative implementation.

## Landing compatibility addendum

[AGENT] 2026-09-08. The supporting entry/control modules described here
remain byte-identical to the selected sprint source. Later L3 work has
restated recovery terminal classification over the actual reached abort
record and its choice-selected panic text, with a named invalid-UTF-8
refusal. The historical renderer debts above do not supersede that landed
contract; see `GoLean/Interface.lean` and
[the L3 landing record](2026-09-07_land-panic-text-tape.md). This gate
restoration changes neither those statements nor the admitted profile.
