# O2 independent static foundation evidence

[AGENT] 2026-09-06, `typed-recovery`, implementation based on reviewed O1 runtime
commit `8717b9748d6732d7aa5f27a4efc0dfb6e4896c06`. The intervening commit
`fadcb0c3` contains only the independent parent Boolean program bridge review.

This increment defines `GoLean.GoCore.RecoveryTyping.RecoveryAdmission` and its
total checker `checkRecovery`, with independently defined type/scope/call/control
judgments and proved checker equivalence. It preserves A3a and O1 unchanged.
It does **not** complete O2 setup, runtime preservation/progress/readout, observer
fidelity, or Iris ownership/customer obligations.

The dedicated full gate passed with exit 0:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/check-recovery-typing
```

`gate.log` records ten module source hashes, successful fresh elaboration of
all ten, 40 required theorem exports, and a post-import transitive audit of
10,773 declarations across every imported local module. The allowed axioms
are exactly `propext`, `Classical.choice`, and `Quot.sound`. Four independent
poisons compile and are then rejected: unused private axioms in a call helper,
the public admission module, and the audit module, plus a trailing private
`sorry` theorem in the challenges module. No actual source is poisoned.

There are 46 kernel test/family theorems: 37 focused challenges, three complete
A2 entry checks, and six second-fixture admission checks (three quantified over
either Boolean input). Generic arbitrary-byte and equal-payload re-panic
families admit invalid UTF-8/control bytes. Negative cases check mixed-sort
first-match shadowing, live-root capture refinement, signature prefixes and
arity, result targets, uncalled/unreachable bodies, declaration effects and
placement, duplicate binding keys, missing returns, and direct/deferred cycles.

The full gate also established that the complete A2 fixture is an exact copy
of the original existing definition, then freshly emitted and lowered both
native Go artifacts and compared **every field** with their proof fixtures.
`a2.json` and `native.json` retain those wire artifacts. This is executable
frontend correspondence evidence, not a compiler-correctness theorem.

`focused.tsv` and `focused.meta.tsv` record a fresh 5/5 Go-versus-Lean PASS
for the second fixture: both Boolean inputs of `Shared` through wrappers,
ordinary recovery in `Outside`, swapped defer order, and direct recovery
instead of indirect recovery. Two deferred handlers share the same
result root, recovered LIFO order affects that root's final value, an ordinary
Boolean helper is called, and indirect recovery executes before direct
recovery while a panic may still be active. The default strict harness also
checks its fixed choice streams; it found no choice consumption. The dedicated
gate also pins the actual native result JSON, separately from equality with
Lean, so input dependence and both controls must remain observable.

| Native observation | Initial draft | Final fixture |
| --- | --- | --- |
| `Shared(false)` | false | true |
| `Shared(true)` | false | false |
| `Outside()` | true | true |
| `Reversed(true)` | absent | true |
| `DirectRecoveryControl(true)` | absent | true |

Self-review caught the initial draft's failure to provide the charter's
input-dependent **result**, although its control paths differed. The initial
wire artifact and the two original native JSON results are retained as
`initial-*`. The final fixture begins with a false result, so normal return
and recovered return differ after the handlers execute. The reversed-order
control changes the recovered result, as does moving the helper's recovery
expression directly into the handler: that direct call consumes the panic
before the second recovery. This latter control is a valid Go source variant
that makes the forbidden semantic inlining observable; it does not mutate
the interpreter or mislabel indirect recovery as a static error.

One optional draft proof reduced the entire symbolic-choice pool execution
of the native fixture and reached the enforced memory cap (exit 137). It is
not counted as a pass. That large closed execution reduction was removed;
the final kernel tests are static admission tests, with actual execution
covered by the fresh differential records. The generic O2 runtime proof
obligation is unchanged and remains open. `optional-runtime-oom.log` retains
the failure classification.

Final ordinary CI passed with exit 0 (`ci.log`):

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/ci
```

The full current static source/gate was unchanged during that run. CI includes
the existing interface/admission/Boolean audits, the new recovery static
audit, frontend tests/pins, 202 successful evaluator tests, and cached baseline
comparisons without regression. The reconciler reported the same two
report-only findings and zero HIGH findings. Independent implementation review
is still pending at this draft checkpoint and must be recorded before commit.

The broad executable corpus is explicitly **cached** from the sealed fresh
preflight at source `10fefeb3`: 3,598 executable and 394 negative cases. Before
ordinary CI, the four `cached-*` records under the previously integrated
`2026-09-06_boolean-storage-setup` evidence were checksum-verified and copied
to this worktree's `artifacts/coverage`. This static lane changes neither the
interpreter nor the frontend. A successful cached baseline comparison is not
a claim that the entire corpus was freshly rerun here.

`references.tsv` pins the Go spec, refined-cerberus, RefinedC, BRiCk and archived
GoLean files read. Their concrete design lessons and all explicit profile
boundaries are described in `docs/2026-09-06_recovery-static-design.md`.

Remaining boundaries include the explicit string-literal boxing profile,
the first-match mixed-store runtime obligations, and finite-call certificates
bounded by table size. The checker is proved equivalent to that independent
bounded graph judgment and admission excludes all cycles; the separate
finite-DAG-to-table-size graph theorem is not claimed by this increment.
