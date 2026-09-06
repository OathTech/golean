# Recovery static lane handoff

**Follow-up checkpoint:** the original six-module snapshot below received
independent review at parent `1ae77483`: all structural admission checks passed;
RS-1 required distinguishing profile exclusion from malformed-body diagnostics.
The seven-module correction and its current validation are recorded separately
in `../2026-09-06_recovery-diagnostics/README.md`. The original logs/hashes below
remain historical. Runtime implementation is now owned by this agent in the
separate `typed-recovery-runtime` worktree; it is not part of this static gate.

**Final static checkpoint:** RS-1 follow-up independently passed at parent
`c2057e78`; the final full focused gate and ordinary CI both exited 0 with the
reviewed sources unchanged. The follow-up evidence includes the CI log and
reverified source hashes. The static increment is ready for authorized feature
integration; no main merge or push is authorized by these gates.

[AGENT] 2026-09-06. Worktree `typed-recovery`, branch `typed-recovery`.
Base O1/runtime source `8717b9748d6732d7aa5f27a4efc0dfb6e4896c06`; intervening
review-only commit `fadcb0c3`. The current static increment is not committed
until final ordinary CI and independent review pass. Main merge/push is not
authorized by this handoff.

Implemented: six independent static modules, full checker equivalence,
all-body/no-cycle consequences, 46 kernel challenges/admission families,
whole original A2 and second native artifacts, four compiled audit poisons,
five differential observations and explicit functional/order/directness pins.
The design and claim ledger are `docs/2026-09-06_recovery-static-design.md`
and `docs/2026-09-06_recovery-static-claims.md`.

Passing focused command:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/check-recovery-typing
```

The exact final gate logs source hashes, fresh elaboration, 40 required
theorems, 10,773 audited imported local constants and four rejected compiled
poisons. Both complete native artifacts match; all five differential cases
pass and their actual native Boolean observations distinguish input, defer
order and recovery directness. Final ordinary `scripts/ci` passed with exit 0:
all proof audits, 202 eval tests, 394 cached negative and 3,598 cached full
baseline cases with no regression; two existing report-only findings, zero
HIGH. The current static source/gate was unchanged during that run.

Failed attempts: optional symbolic whole-pool native fixture kernel reduction
hit the enforced cap (137); retained and abandoned as a test attempt, not a
runtime proof. Initial native fixture returned false on both inputs; self
review found the charter violation and corrected it before acceptance. Initial
wire/oracles, final result table and counterfactual controls are retained.

Next actions: incorporate the independent static review,
seal final source/evidence hashes, then commit for internal feature integration.
The parent must rebuild integrated source and connect the profile to generic
actual setup and a precise mixed-store/control invariant, prove all admitted
runtime transitions and terminal-aware readout, then instantiate reusable Iris
call/unwind rules for both customers. No successful execution premise may
replace those obligations. Observer repair must handle the admitted arbitrary
bytes and equal re-panic family. Static admission is not O2 completion.

There is no blocking user decision in this static increment. The separate
finite-DAG-to-table-size graph theorem is an explicit unclaimed auxiliary,
not an execution assumption. Broad CI records are explicitly cached at
`10fefeb3`; this lane changes no frontend/interpreter runtime source. Parent
final runtime integration must run its required fresh gates.
