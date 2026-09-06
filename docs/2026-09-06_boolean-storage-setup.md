# Boolean storage and actual driver setup: bounded increment

[AGENT], 2026-09-06. This is an O1 building block under the approved
[charter](2026-09-05_typed-consumer-sprint-charter.md), not completion of O1.
The static admission increment is `c7a439f7`, integrated at `a392fab0`.
No interpreter or frontend behavior changes in this increment.

## Definitions and claims

All names below are in `GoLean.GoCore.BooleanRuntime`, unless qualified.
The storage lemmas are in `GoLean/GoCore/BooleanStore.lean`; the entry lemmas
are in `GoLean/GoCore/BooleanSetup.lean`. The semantic facade imports both,
together with the stronger `GoLean.GoCore.BooleanTyping` profile.

| Contract | Exact claim and premises | Status and limit |
|---|---|---|
| `BoolRoot s loc` | `loc` is a root address with an actual `.value .bool (.bool b)` cell in `s` | Structural definition; excludes a declared Boolean cell containing nil and excludes arbitrary paths |
| `BoolHeap s` | Every allocated heap cell contains an actual Boolean at Boolean type | Structural definition for the Boolean-only profile; unsuitable unchanged for O2's reference/interface values |
| `EnvRoots s env` | Every binding occurrence in every scope references a typed Boolean root | Includes hidden outer bindings and shadowed same-scope bindings; visible lookup alone is weaker |
| `NamesPresent names env` | Each listed name has a successful actual `LocalEnv.lookup` | Binding existence only, not a name-to-index or nonaliasing assertion |
| `BoolRoot.load`, `EnvRoots.lookup` | Typed roots can be loaded; any successful lookup in an `EnvRoots` environment yields a typed root | Generic, no run-success premise |
| `store_bool`, `BoolRoot.set`, `BoolHeap.set`, `EnvRoots.set` | The real root-cell store writes the Boolean value and preserves other typed root/environment facts | Existing in-bounds typed cell required; existing aliases preserved |
| `allocDecls_bool` | The actual local allocator succeeds at Boolean type and preserves typed storage and named binding coverage | Boolean parameter list plus structural store/environment premises; shadowing permitted at this helper level; this existential postcondition does not yet expose each initial zero value |
| `bindParams_bool` | The actual argument binder succeeds and preserves typed storage and names | Boolean parameter types, actual Boolean values and equal lengths; normalization success alone is insufficient |
| `allocDecls_shape`, `bindParams_shape` | Each successful helper adds exactly one cell per parameter and preserves all nonheap context fields | These supporting shape lemmas assume helper success; the Boolean lemmas and entry theorem derive that success separately |
| `pinResultLocs_bool` | The actual result-pin operation succeeds, retains the result-list length and produces typed roots | All result names present in a typed environment; distinctness is a separate stronger-admission fact |
| `loadMany_bool` | Actual driver readout succeeds with a Boolean list of matching length | Each supplied pinned root must remain valid; no terminal or reachability assumption is hidden here |
| `setup_boolean` | The real `runProgramSetupM` succeeds with the entry body, actual empty driver barrier, typed heap/environment, parameter/result name coverage and typed external result pins | A3a `BooleanAdmission`; arbitrary input choices and arbitrary fuel; globals and package initialization excluded by that profile |
| `setup_boolean` (resources/context) | Exact final heap size is argument count plus result count; all nonheap context fields and the complete choice stream are unchanged | No setup fuel lower bound is needed in this no-initializer profile; no execution-termination claim |
| `BooleanTyping.checkTypedBoolean_iff` | Stronger total checker iff the independent scoped judgment | Previously reviewed static theorem; A3a's accepted-unbound counterexample remains unchanged |

The theorem declarations are kernel-checked under the existing foundational
axiom policy; the gate evidence and independent implementation-review verdict
must be consulted before treating the increment as accepted. There are no new
assumptions about future execution, fixture identity, native generated names,
or successful evaluator runs. `SameContext` is an equality of all nonheap
state fields, awaiting B7's representation-enforced immutable context.

## Review-driven invariant correction

The statement review exhibited a visible `x` at root 0 hiding an outer `x`
at dangling root 999. A predicate checking only successful visible lookup
would accept it even though configuration address bounds fail. `EnvRoots`
therefore quantifies **every binding occurrence**, and derives lookup
coverage as a theorem. Tests retain both the outer-scope and same-scope
shadowed dangling cases. They also retain an address-bounded heap whose
declared Boolean cell actually contains nil, and check the real native
argument setup with both input values and an initially false result.

## Remaining O1 and downstream obligations

`setup_boolean` deliberately states typed storage, rather than claiming that
A3a types the current body. O1 still requires stronger admission to establish
the structural control invariant, preservation for every relational successor,
terminal-aware progress, and the reachable terminal driver's typed readout.
Exact generic parameter-value/name-location correspondence, distinct initial
roots and zero-valued result pins must be exposed for useful functional and
ownership reasoning; the current existential storage statement alone does not
supply all those facts. The small concrete setup test is a regression, not a
replacement for those generic theorems.

O2 must extend the store/value/control judgments for calls, captures, defer,
panic and recover, and prove the corresponding transitions. Iris ownership
resources stay in the customer; no heap invariant here creates Iris resources.
B7/I1, the second fixture and final integration review remain mandatory.

## Audit integration and validation

The semantic interface, A1 and A2 dependency audits now sweep every imported
`GoLean` and `Tests` module by origin (including private/generated/unused
declarations), in addition to their customer modules. The interface audit
requires the new public contracts and key regression theorems. Its compiled
negative controls include unused private axioms in both helper modules and a
trailing forbidden theorem in the runtime regression module.

Run the interface and CI gates through `scripts/capped`, with the approved
16 GiB cap and three Lean threads. Ordinary CI may reuse the fresh preflight
executable/negative records at `10fefeb3` only as **cached** comparison evidence:
this increment does not change runtime behavior. Final sprint validation still
requires the complete gates at the final runtime source. Validation results
and hashes are recorded in the
[evidence directory](evidence/2026-09-06_boolean-storage-setup/README.md).
Interface, ordinary CI, A1 and A2 gates passed; A2 includes fresh artifact
equality and all three differential cases. Independent implementation review
returned **PASS for this bounded helper increment**, with six fresh kernel
adversarial probes and no blocking finding. This does not discharge the
remaining O1 obligations listed above.
