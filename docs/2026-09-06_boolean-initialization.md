# Exact Boolean initialization from scoped admission

[AGENT], 2026-09-06. Follow-on to the reviewed
[storage/setup increment](2026-09-06_boolean-storage-setup.md), on sprint
branch `typed-consumer-sprint`. This closes that increment's exposed initial
binding/value/identity obligations. It does not alone establish execution
safety, a functional program result or Iris ownership.

`GoLean/GoCore/BooleanInitialization.lean` defines a canonical initial
environment and store, then proves that the actual binder, allocator and
`runProgramSetupM` construct them. It adds no interpreter behavior or
alternative evaluator. The definitions and proofs are public through
`GoLean/Interface.lean`.

## Claim and assumption ledger

All names are in `GoLean.GoCore.BooleanRuntime`; all theorems below have
compiled under the existing foundational axiom policy. Independent review
must assess the statements as well as their proofs.

| Public fact | Domain, exact guarantee and limits |
|---|---|
| `declareRoots`, `declareRoots_lookup`, `declareRoots_lookup_absent` | Consecutive root declarations through the real lexical `declare`; distinct names resolve to their own indexed roots, absent names retain prior lookup. Repeated names are not presumed distinct. |
| `bindParams_exact` | Boolean parameter types plus equal parameter/value lengths imply the actual binder's exact environment and appended heap. Input Booleans retain their order and value. An arbitrary existing heap/environment is preserved, even if malformed; this equality does not claim to repair it. |
| `allocDecls_exact` | Boolean declarations imply the actual allocator's exact environment and one new false-valued Boolean cell per declaration. Existing cells/bindings are preserved; no implicit well-typedness or separation premise. |
| `pinResultLocs_of_lookup` | Pointwise actual lookup at the declared indices yields the exact ordered pin list. This supporting theorem uses independently checkable lookups, not a pinning-success premise. |
| `initialEnv_argument`, `initialEnv_result` | Distinct combined parameter/result names resolve to indices `i` and `argumentCount+i`. These are facts about the canonical environment; the entry theorem below identifies it with the actual driver. |
| `initialState_argument` | Each in-bounds argument index in the canonical state loads the corresponding supplied Boolean. |
| `initialState_result` | Each declared result index loads false, **provided supplied argument count equals the function's argument count**. This premise is essential; otherwise the offset may select an argument cell. |
| `initialEnv_pins`, `initialResults_distinct` | Distinct signature names give the canonical actual pinning equation; the canonical consecutive result list is always duplicate-free. Canonical-list distinctness alone says nothing about a weakly admitted driver's actual pins. |
| `EnvRoots.locSup_le`, `BoolHeap.heapLocSup`, `booleanState_wf`, `booleanEntry_wf` | The all-binding typed-root and actual-Boolean-cell predicates supply address bounds, together with Boolean program syntax and unchanged context. Initial `MachineWf` is derived; its iterator component uses the existing `itersNormalized_true` fact, not a new typing assertion. |
| `setup_typed_exact` | For any scoped `TypedBooleanAdmission p name (bs.map bool).toArray`, arbitrary setup fuel and arbitrary choices, the real driver enters the selected typed function with the canonical heap/environment/pins, `MachineWf`, typed heap/environment, name coverage, typed pinned roots, unchanged nonheap context and exact argument arity. The entire choice stream is unchanged. |

The setup theorem's arguments are a list of actual Booleans converted to
the driver's value array. This represents all admitted Boolean inputs;
the original `initialArguments_bools` theorem decomposes arbitrary admitted
arrays. The no-global/no-package-initializer profile needs no lower bound on
setup fuel. Execution fuel remains a separate resource obligation. Nothing
here assumes a successful future run or generates an Iris resource.

The canonical layout uses natural-number heap indices and the current dense
heap allocator. Those are explicit current-machine representation facts,
to be transported through B7; there is no host-memory availability theorem
or additional platform-conformance claim. The Go/Lean frontend relation
remains tested, not proved, and names are ordinary GoCore binding keys.

## Evidence and remaining integration

The expanded interface gate passed with 41 required exports, 11,879 imported
project declarations and seven compiled poison rejections. It includes a new
unused private axiom injected into `BooleanInitialization`. Ordinary capped
CI passed, including the warning-free build and all 202 eval tests; full
3598-case executable and 394-case negative comparisons are explicitly cached
from `10fefeb3`. No existing runtime behavior changed in this increment.

The kernel regressions now include a two-argument/two-result setup family:
different input values distinguish argument order, and the two initially
false results must have separate pins at the correct offsets. The existing
weak-admission hidden-binding/readout controls remain. The independent reviewer
compiled additional adversarial probes; its sealed report records the exact
scope and verdict separately.

Still required for O1: connect these facts to the reviewed structural control
invariant and all-successor preservation/progress, expose the combined admitted
driver safety/readout result, validate the integrated public interface and
both customer gates, and independently review that combined chain. A generic
termination bound is not claimed. O2 recovery/customer reuse, B7/I1, C1 handoff
and the final closing packet remain mandatory under the charter.
