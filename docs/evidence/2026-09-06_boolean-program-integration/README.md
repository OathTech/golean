# Public Boolean setup, driver and readout integration

[AGENT], root integrator, 2026-09-06. Source parent `761d4e28`, integration
branch `typed-consumer-sprint`. This proof/API increment adds
`BooleanProgram`, `BooleanPool` and seven actual-driver kernel consumers.
The [contract ledger](../../2026-09-06_boolean-program-contract.md) states
the exact domains, choice quantifiers, fuel and terminal/output policy.

The complete proof bodies were independently re-elaborated and challenged
in review `fadcb0c3` (integrated at `761d4e28`). The separate public-promotion
review `638af8dd` compares all 20 original theorem bodies and seven tests
with their promoted modules and inspects the source-origin audits and
compiled poisons. Both bounded reviews PASS. The promotion review inspected
the parent's gate evidence rather than claiming a duplicate independent
gate run; that limitation is preserved in its own record.

## Fresh checks on the promoted source

All commands completed with exit 0 using `GOLEAN_MEM_MAX=16G` and
`LEAN_NUM_THREADS=3`:

```text
scripts/capped lake build
scripts/capped bash scripts/check-interface
scripts/capped scripts/ci
scripts/capped bash scripts/check-admission
scripts/capped bash scripts/check-boolean-typing
scripts/capped bash spikes/gate-a1/check
scripts/capped bash spikes/iris-customer/check
```

The explicit build log records the public-module build; CI and each full
customer gate additionally run the ordinary default build. The interface
gate checks 65 required exports and 12,196 local declarations, rejecting all
twelve compiled private/unused/trailing poisons. CI's runtime gate freshly
elaborates all fourteen selected modules, checks 44 required exports and
12,135 local declarations, and rejects all six compiled poisons. The ordinary
CI also passes the standing source/pin/frontend checks and 202 evaluator
tests. The two existing reconciler findings remain report-only, with no HIGH
finding.

The full admission gate passes fresh native artifact correspondence and 1/1
differentials. The Boolean family passes whole-artifact correspondence and
3/3 differentials; seven new kernel consumers additionally cover both Boolean
argument values, actual result/zero initialization, and fuel/choice/output
boundaries. A1 checks 12 exports and 12,503 declarations with all three
compiled negatives. A2 checks 18 exports and 12,914 declarations with all
three compiled negatives, then passes fresh native artifact correspondence
and all three normal/recovered/uncaught differentials. These are retained
A1/A2 gates, not a claim that the new O2 reusable customer has been finished.

## Reused runtime evidence

The fresh full runtime gate for the preceding renderer integration is sealed
at `82e177c7` under `../2026-09-06_renderer-integration/`: 3,607 executable
cases, 3,363 PASS and 244 known FAIL, plus 394 negative cases. This increment
changes proof modules, public imports, test/audit selection and build targets;
it changes neither executable semantics nor native emission/lowering.
`runtime-reuse.json` records the exact changed members of that prior source
inventory and compares the actual interpreter binary. The rebuilt binary
differs; reuse is justified by unchanged executable source, not a claim of
binary identity. The full/negative
records used by ordinary CI retain their original dirty-source provenance
at parent `c7eeaf57`; they are not reattributed to a clean commit or relabeled
fresh. The slow-tier certificate remains explicitly cached.

`sources.sha256`, `provenance.json` and `SHA256SUMS` bind the actual source,
toolchain pins, commands, logs and focused differential tables. Proof source
was frozen during these checks; evidence/handoff bookkeeping followed their
completion. This closes the current O1 public-program increment. O2 runtime
and Iris reuse, observer/R-1 fixes, B7/I1, C1 handoff and the full closing
decision packet remain required; no stable pin or complete Gate A is claimed.
