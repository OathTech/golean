# Boolean runtime invariant evidence

This is the bounded runtime preservation/progress increment following the
static admission commit `c7a439f7` and reviewed storage/setup commit
`f251abcb`. It does not certify completed O1 setup-to-invariant integration,
O2 recovery typing, or the whole sprint. The parent lane owns those steps.

## Reproduce

From the repository root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped bash scripts/check-boolean-runtime
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci
sha256sum -c docs/evidence/2026-09-06_boolean-runtime-invariant/sources.sha256
```

The build uses actual committed `BooleanStore.lean` source after merging
`f251abcb`. Temporary helper oleans were used only during development;
`BooleanStore` and its runtime dependents were rebuilt from source before this
gate. `sources.sha256` pins all 44 local GoLean modules plus test, build and
gate inputs (53 files total). The checksum does not include itself or this
evidence prose.

## Focused runtime gate

`gate.log`: PASS, exit 0. It prints the hashes and freshly elaborates
`BooleanStore`, the six new runtime modules and both test/audit modules
(nine files). The `BooleanRuntimeTests` target builds 25 jobs.
The post-import audit requires 28 theorem exports and checks 10,506 constants
from **all imported local GoLean/Tests module origins**, including unused and
private declarations and the importing module. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

All three negative mutations compile successfully, then fail the independent
importing audit for the intended forbidden axiom:

- unused private axiom in `BooleanPreservation`;
- private axiom appended to `BooleanSafetyAudit`;
- trailing private `sorry` theorem in `Tests.BooleanInvariant`.

The expected error lines in `gate.log` are those negative controls, not a
failed positive gate.

`Tests.BooleanInvariant` has 12 kernel theorems. They include arbitrary-name
staged initialization, a structural initial invariant, preservation for every
supplied successor, refusal exclusion for every fuel/choice stream, and
rejection of foreign initialization environments, root initialization,
return-to-stop, wrong sort, dangling roots and hidden dangling bindings.
Two both-input kernel evaluations use actual `runConfig` and `loadMany` to
test outer-scope restoration and zero initialization. These are executable
kernel checks, not new Go-vs-Lean differential rows.

## Ordinary CI and differential provenance

The final ordinary CI run is recorded in `ci.log`: **PASS, exit 0**. It builds
the core, passes 202 evaluator tests and all mandatory gates including the
strengthened runtime gate with fresh source elaboration. It reports the two
existing reconciler findings as report-only, with zero HIGH findings.
This increment changes no interpreter, relational rule or native frontend.

The broad executable and compile-negative corpus records checked by ordinary
CI are explicitly **cached**, copied from the sealed
[storage/setup evidence](../2026-09-06_boolean-storage-setup/README.md):
3,598 executable cases (3,353 PASS and 245 known failures), 394 compile-negative
cases, originally freshly run at
`10fefeb3e6fbb3f7cb6630b8b559a9a7e7915e97` by the preflight lane. The copied
records were checked against that directory's `SHA256SUMS` before reuse.
This worktree does not claim a fresh full-corpus run at the new proof sources.
The earlier complete native fixture, initializer-shadowing challenge and
3/3 focused differential results remain recorded with the
[static typing increment](../2026-09-06_boolean-typing/README.md).

## Review and limits

The independent `typed_contract_review` lane issued **PASS for this bounded
runtime increment** on 2026-09-06 after reading the structural definitions,
all-successor proof, actual driver contracts, focused regressions, all-origin
audit and the strengthened final gate evidence. It found no circular safety
premise or quantifier defect. The reviewer inspected the recorded passing
executions rather than rerunning them independently, and required ordinary
CI to exit 0 before commit. Its source review explicitly
limited the context-union argument to homogeneous Boolean memory type safety;
it is not lexical identity or functional equivalence and must not be copied
unchanged into heterogeneous recovery typing.

The [design note](../../2026-09-06_boolean-runtime-invariant.md) records the
exact theorem inventory and the separate responsibilities for setup,
termination/fuel, memory allocation model, result values and Iris resources.
