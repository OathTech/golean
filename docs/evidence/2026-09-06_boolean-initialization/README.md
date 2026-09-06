# Exact Boolean initialization evidence

[AGENT], 2026-09-06. Source: uncommitted exact-initialization increment over
`8b0a6a22` on `typed-consumer-sprint`, bound by `sources.sha256`. This is a
proof/API increment; no existing interpreter/frontend behavior changed.
The [claim ledger](../../2026-09-06_boolean-initialization.md) states the
exact initialized values, bindings, identity, resource and setup guarantees.

All commands used `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3`, under
`scripts/capped`, at Lean 4.32.2 and Go go1.26.5:

- `scripts/capped lake build GoLean.GoCore.BooleanInitialization` passed.
- `scripts/capped bash scripts/check-interface` passed (`interface.log`):
  41 required exports, 11,879 imported project declarations, seven compiled
  poison controls rejected, including an unused Initialization-module axiom.
  The gate freshly elaborated all public new sources and tests.
- `scripts/capped scripts/ci` passed (`ci.log`): warning-free default build,
  interface/admission/static-typing gates, frontend and lowering tests/pins,
  all 202 interpreter eval tests and cached full/negative comparisons.

The 3598 executable / 394 negative comparisons reuse the completed preflight
records at `10fefeb3`, explicitly labeled stale in CI. Their original sealed
bytes are in `../2026-09-06_typed-preflight/`. They are not fresh conformance
evidence for this increment. The earlier A1/A2 gates covered the preceding
helper source; the complete admitted runtime integration must rerun both on
its final public source. No current A1/A2 rerun is claimed here.

Independent source review and eight fresh adversarial kernel probes returned
a bounded setup-only PASS. The separate reviewer report contains the exact
source provenance and limitations in the
[sealed independent review](../2026-09-06_boolean-initialization-review/README.md),
integrated at `815227ad`. This evidence does not establish the complete O1
chain, O2 or B7.

During iteration a malformed indentation in the new paired fixture prevented
elaboration; its corrected source passed the fresh gate. The earlier failed
log remains at `artifacts/boolean-runtime/initialization-interface.log`.
No gate or proof premise was weakened to correct that syntax error.
