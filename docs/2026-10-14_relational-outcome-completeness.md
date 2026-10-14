# C1 local outcome completeness — first constraint checkpoint

[USER] 2026-10-14: after audited residual RD5 E/F, begin C1 under
`relational-demo-brief/docs/2026-10-14_mirror-outcomes-brief.md`.
E/F is independently consumable at
`fc52512a6644c04996d327865919556107cf84ba`; its audited handoff is
`3feb58821686d000fd06204ff7dba45323e858ba`. C1 starts from that response,
not from the earlier A–D baseline. No merge, push, live repin or peer writes.

**Status: begun, not complete.** This checkpoint compiles candidate carriers
and exact correspondence obligations. It does not prove exhaustive local
outcome coverage, and no new outcome API is exported by `GoLean.Relational`.
The E/F implementation, facade and checked downstream acceptance are unchanged.

[AGENT] 2026-10-14: keep the initial constraint in
`experiments/2026-10-14-outcome-completeness/LocalOutcomeConstraint.lean`
until a concrete ordinary-operation failure relation and its correspondence
are proved. Its `OperationFailure` parameter is the signature that still needs
an implementation; introducing it assumes no proof and discharges no obligation.
The experiment uses namespace `GoLean.GoCore.Relational.C1`.

## Carriers and domains

- `Mode`: main or initialization. `Admitted` is True in main and absence of
  the actual `printOut?` guard in initialization, at each traversed source.
- `FailureCause`: exact ordinary refusal or fatal diagnostic. Panic payload
  chains, rendered text and rendering refusal stay in the existing `Boundary`.
- `OperationFailure`: a semantic relation over context, supplied state,
  consultation records and failure cause. Its signature contains no tape,
  evaluator or driver. Its implementation is still owed.
- `Finish`: normal/deadlock boundary at cost zero, rendering and ordinary
  operation failure at their actual cost, and initialization printing at zero.
  Ordinary failures cannot bypass zero-cost or initialization-print priority.
- `Prefix`: successful labelled transitions retaining each source mode guard.
- `Execution`: selected bounded execution, exact successful labels, endpoint,
  separate finishing consultations, outcome and actual cost. Exhaustion is at
  zero remaining fuel after exactly the budget's number of successful steps.
- `Outcome.stop?`: projects causes exactly. The correspondence projection
  returns store/tape only for normal completion. Error projections erase the
  semantic endpoint and consultation suffix, since those are not returned by
  the executable. No emitted label for a failed call is manufactured.
- `Avoids`: excludes a named bad outcome at every reachable mode-admitted
  prefix and every finishing alternative. Refusal and fatal exclusion remain
  distinct; one successful successor is never used as an all-choice premise.

All inputs retain arbitrary context, supplied store/control and budget. No
MachineWf, NoRefusal, fit condition or blanket successful-operation premise
is added. There is no global outcome-uniqueness claim across different choices.

## Exact named obligations

The experiment's `Correspondence` namespace contains these compiled `Prop`
definitions, not theorem declarations or assumed instances:

| Obligation | Required result |
| --- | --- |
| `OperationCoverage failure` | Every ordinary non-abort/non-zero-cost actual step refusal/fatal has a semantic failure witness whose consultations replay on that actual tape. |
| `OperationReplay failure` | Every semantic failure works on every tape replaying its consultation witness. |
| `OperationSelections failure` | Each failure's consultation witness can be realized with any suffix. |
| `Coverage failure mode` | Every actual local run has an `Execution`, the same executable successful prefix, finishing replay and exact result projection. |
| `Realization failure mode` | Every admitted relational execution at its budget is realized with an arbitrary finishing suffix and the same labels/result projection. |
| `RefusalExclusion failure mode` | `Avoids ... Outcome.isRefusal` excludes every actual executable refusal. |
| `FatalExclusion failure mode` | The separately stated fatal exclusion excludes actual fatal failure. |

The source gives the full quantifiers and projections. Main-mode coverage and
realization come first. Initialization-mode correspondence follows only after
the main checkpoint; its guard and cost are already explicit in the constraint.
A failed operation's replay suffix is a semantic witness, not a claimed
executable error return value.

## Checked results and concrete gap

Proved carrier laws: `Prefix.erase`, `Execution.prefix`,
`Execution.within_budget`, `Execution.exhaustion_length`, and
`Execution.finish_or_exhausted`. Boundary controls check normal completion at
zero fuel, initialization printing at zero fuel, and byte-exact agreement of
the initialization diagnostic with the existing guard.

`Correspondence.excludes_stop_of_coverage` proves the generic exclusion
transfer from an explicit coverage proof. Its refusal and fatal specializations
are separate proved lemmas. They do not supply the still-missing coverage proof.

`old_fault_coverage_gap` is a checked counterexample to treating the old
selected-fault API as exhaustive: for arbitrary context/store/environment/tail
and reason, evaluating `.unsupported reason` returns that unsupported refusal,
but there is no matching `LocalFault` witness. This does not refute the requested
C1 semantics; it identifies a concrete missing site in the old API. The existing
`ExecutionStatement.Finish.fatal` and `ClassRefusal` also retain stepFn equations,
so simply re-exporting their classification would not satisfy C1's boundary.

Compilation passes with no warnings. Twelve headline axiom prints and the
exhaustive current-module audit (162 declarations) use only `propext`,
`Classical.choice`, `Quot.sound`. Kernel replay of `LocalOutcomeConstraint`
passes. Its unchanged GoLean imports retain the E/F source/CI/replay evidence;
this experimental-only checkpoint does not change runtime or public exports.
Earlier elaboration attempts failed on a mode parameter and proof rewrites;
the audit rejected Lean's generated sorryAx in those failed attempts. The
successful final elaboration and replay, not those attempts, are the evidence.
This first constraint checkpoint has not had a separate C1 independent audit;
C1's final implementation still requires its commissioned fresh review.

Reproduce from this worktree (outputs are disposable):

```sh
mkdir -p .tmp/c1
LEAN_NUM_THREADS=2 capped lake env lean \
  -o .tmp/c1/LocalOutcomeConstraint.olean \
  experiments/2026-10-14-outcome-completeness/LocalOutcomeConstraint.lean
LEAN_PATH="$PWD/.tmp/c1" LEAN_NUM_THREADS=2 capped lake env leanchecker \
  --verbose LocalOutcomeConstraint
```

## Remaining implementation work

1. Implement ordinary-operation failure coverage, including malformed controls,
   fatal operations and choice-dependent refusals, using semantic operation
   premises and selection witnesses. Prove all three operation obligations.
2. Prove main `Coverage` and `Realization` without safety or well-formedness
   premises; instantiate the exclusion corollaries. Check the main checkpoint.
3. Complete initialization coverage and realization with the guard-before-fuel
   ordering; then expose the coherent public interface and a facade-only client.
4. Run the required CI, exhaustive/headline axiom checks, exact module replay,
   existing relational regressions and a fresh independent implementation audit;
   disposition findings before claiming C1 complete.

The later all-outcome program bridge (validation, setup, package initialization,
activation and readback), complete observers, locality and sequentialization
remain outside C1. This document records a checked start, not a blocker claim
or a completed mirror-completeness milestone.
