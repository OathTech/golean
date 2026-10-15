# Independent concurrency compatibility review

Fresh independent reviewer: `/root/independent_review`, 2026-10-15.
The reviewer received the original brief, source/setup locations and applicable
charter, with unrestricted review scope. The following review is recorded
verbatim; coordinator dispositions follow it.

## Review

Reviewed commit `ea1341cf20941c2c91d6811fab1099476e05d975` against baseline `fc52512a6644c04996d327865919556107cf84ba`, the supplied brief, and the applicable charter. All references below are relative to the reviewed worktree.

The two selected executions support the stated, limited compatibility result. I found no implementation defect in their positive acceptance proofs. The unresolved detector-ordering contract remains a substantive baseline finding; it prevents a broader detector-history or ownership-safety conclusion.

Findings:

1. **Medium — unresolved baseline ordering contract, already disclosed.** `GoLean/GoCore/Ops.lean:2698` derives the opaque location comparator used by `Race.shadowSet` (`Race.lean:303`). The missing contract is precisely exposed by `Concurrency/Obstruction.lean:10`; `Synchronization.lean:138` establishes the conditional loss of rejection when distinct roots compare equal. My independent audit reproduced the partial implementation finding. This is a proof/interface obstruction, not a demonstrated runtime comparator defect. The positive acceptance proofs remain valid because they handle every comparator result without assuming the contract. Keep this finding open for upstream disposition; do not promote these examples into general preservation of race history.

2. **Low — the rendezvous theorem’s comment overstates its conclusion.** `Concurrency/Synchronization.lean:100` says “two-way rendezvous ordering.” `TransferBoundary` in `Concurrency/Constraints.lean:35` asserts only the old sender clock is below the new receiver clock, and `transfer_boundary` proves that direction. Change the comment to sender-to-receiver ordering, or prove the reverse direction too. The stage record’s prose already describes the actual one-way conclusion correctly.

3. **Low — incorrect qualified declaration name in the handoff.** `docs/2026-10-14_relational-concurrency-compatibility.md:106` names `Concurrency.Obstruction.RootComparatorContract`. The actual declaration is `Concurrency.RootComparatorContract` (`Concurrency/Obstruction.lean:4`, `:10`). Correct the name so the reported blocker can be located and checked directly.

Supported claims:

- `variable_phase_pool` consumes the public variable-read phase with symbolic store, value, environment, continuation and scheduler parameters. Concrete applicability guards are discharged at the example sites.
- The disjoint-memory execution contains actual spawn, two memory-active goroutines, a permitted print boundary, and a disjoint write before the parent resumes. `preserved_read` uses the actual write/read support laws rather than thread framing.
- The 25- and 38-iteration prefixes use upstream `PoolPrefix`, actual `stepMulti`, and continuously threaded `raceUpdate`. Initialization at `execProg` and the real spawn justify the empty initial detector and thread identities. No detector reset or assumed detector success appears.
- Driver results retain output and scheduling records. The disjoint example also checks the fuel boundary at 24 iterations.
- The rendezvous proof checks an actual paired transition, detector fold, sender-to-receiver clock order and subsequent read of the changed value. Its negative probe is accurately described as counterfactual, not a schedulable step.
- The downstream discussion correctly distinguishes ordinary steps, spawn and paired control updates, and does not claim concurrent Iris adequacy or an NPDRF converse.

Remaining limits are accurately disclosed: whole-program/frontend setup admission, general path lifting, interior locality within one root, general detector-history preservation, reverse rendezvous ordering as an exposed theorem, other synchronization cases, and all-schedule safety.

Validation performed independently:

- Direct re-elaboration of `Concurrency/Example.lean` and `Concurrency/Synchronization.lean` with `LEAN_NUM_THREADS=2 capped lake env lean`: both exited successfully.
- `Concurrency/Audit.lean`: standard-axiom audit **PASS**, 20,349 declarations; implementation scan **FAIL**, 17 reported partial implementations without transparent total parents. Headline theorem dependencies were standard axioms only.
- Source inspection of the certificate generator, upstream pool/driver/race definitions, relational contracts and downstream sequential lifting/adapter; source escape-hatch search and `git diff --check`.
- No independent kernel replay was run, to avoid duplicating the coordinator’s replay. This review does not certify that pending result.
- No files, refs or shared state were edited.

## Coordinator dispositions

- F1 — **Open, raised with the user.** [AGENT] 2026-10-15: retain the
  compiled `Concurrency.RootComparatorContract` and conditional countermodel
  `Concurrency.Sync.equal_comparison_loses_rejection` as the precise blocker.
  No runtime/API repair is authorized in this experiment. The stage record
  and final handoff report the ordering obstruction and all 17 implementation
  scan findings as unresolved; no broader safety claim is made.
- F2 — **Fixed.** [AGENT] 2026-10-15: corrected the theorem comment to
  sender-to-receiver ordering, matching its checked proposition. The reverse
  direction remains outside the exposed result; no theorem was weakened.
- F3 — **Fixed.** [AGENT] 2026-10-15: corrected the stage record's declaration
  name to `Concurrency.RootComparatorContract`.

The only post-review Lean change is F2's documentation comment. The stage
record gives final build, axiom audit and coordinator kernel-replay results.
This review commissions neither merge approval nor a trust-finding waiver.

Reviewer follow-up, 2026-10-15, verbatim:

> Verified read-only:
>
> - **F2 fixed:** the comment now accurately says sender-to-receiver ordering; theorem unchanged.
> - **F3 fixed:** the stage record names `Concurrency.RootComparatorContract`.
> - The review transcription matches my original report.
> - Dispositions preserve F1 as unresolved and do not imply a waiver or broader safety result.
>
> No additional findings or builds. I have not independently certified the coordinator’s replay result.
