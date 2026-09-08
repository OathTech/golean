# Recovery static foundation claim ledger

> [AGENT] 2026-09-08: historical contract note selected from committed
> `typed-consumer-sprint` at `7edc298f`. The landed definitions and theorem
> statements on main take precedence; current compatibility and limits are
> recorded in `docs/2026-09-08_typed-test-gates-landing.md`. Validation
> counts below belong to the original sprint. Unlanded references are
> identified as paths at that source commit, not as files present on main.


[AGENT] 2026-09-06. Namespace: `GoLean.GoCore.RecoveryTyping`. This is the
static increment of O2, not the completed recovery runtime/customer contract.
The design and explicit exclusions are in
[the design note](2026-09-06_recovery-static-design.md).

All proved rows below are generic over their displayed source parameters.
**Choice quantifier:** not applicable; no judgment/checker below accepts,
selects, consumes or assumes an execution choice stream. **Resource premise:**
none concerning machine fuel, future evaluation or runtime success. The finite
call-tree judgment has an explicit structural natural-number bound, with
whole admission using the function-table size. **Terminal/output policy:**
these are static claims only; they make no terminal, output, refusal-freedom,
termination, renderer or Iris `NotStuck` promise.

| Claim and definitions | Theorem names | Source | Status |
| --- | --- | --- | --- |
| Independent type classes, first-match scoped binding, admitted nil syntax | `checkType_sound`, `checkType_complete`, `checkType_iff`, `checkHas_iff`, `checkNilType_iff`, `checkNilExpr_iff` | `GoLean/GoCore/RecoveryTypingCore.lean` | Proved |
| Declaration lookup and new-binding type | `lookup_declare`, `has_declare_self` | `GoLean/GoCore/RecoveryTypingCore.lean` | Proved; exact static lookup, not yet runtime-environment correspondence |
| Independent sorted expression and actual target judgments | `checkExpr_sound`, `checkExpr_complete`, `checkExpr_iff`, `checkExprAt_iff`, `checkTarget_iff`, `checkTargetAt_iff` | `GoLean/GoCore/RecoveryExpressions.lean` | Proved |
| Argument/result vectors and root-only captures | `checkArguments_iff`, `Arguments.length`, `checkTargets_iff`, `Targets.length`, `checkCaptures_iff` | `GoLean/GoCore/RecoveryCalls.lean` | Proved; liveness is a required refinement for subsequent runtime interpretation, not a consequence of Go pointer type alone |
| Direct-call signatures; literal closure prefix/signatures; deferred registration signatures with discarded results | `checkDirectCall_iff`, `checkClosureCall_iff`, `checkDeferredCall_iff` | `GoLean/GoCore/RecoveryCalls.lean` | Proved; actual frame/capture/defer transitions remain owed |
| Assignment sort and explicit string-boxed panic argument | `checkAssignment_iff`, `checkPanicArgument_iff` | `GoLean/GoCore/RecoveryStatements.lean` | Proved; no restriction on payload bytes or earlier recovery |
| Sequence effects and branch neutrality | `afterStmt_neutral`, `afterStmts_neutral` | `GoLean/GoCore/RecoveryStatements.lean` | Proved; sequence exports declarations, block restores context |
| Independent statement and statement-list judgment/checker correspondence | `checkStmt_sound`, `checkStmts_sound`, `checkStmt_complete`, `checkStmts_complete`, `checkStmt_iff`, `checkStmts_iff` | `GoLean/GoCore/RecoveryStatements.lean` | Proved; checks unreachable arms and declaration placement too |
| Redundant structural surface and declaration-placement diagnostics | `ExprTyped.in_profile`, `TargetTyped.in_profile`, `Statement.in_profile`, `Statement.placement` | `GoLean/GoCore/RecoveryDiagnostics.lean` | Proved consequences of independent judgments; `checkFunction_iff` and `checkRecovery_iff` preserve the unchanged admission predicate |
| Complete syntactic dependency extraction | `callIds_sound`, `callIdsList_sound`, `callIds_complete`, `callIds_iff` | `GoLean/GoCore/RecoveryGraph.lean` | Proved; direct, closure and defer edges all included |
| Independent bounded call-tree certificate and strict depth descent through paths | `checkCallDepth_iff`, `CallDepth.down`, `no_self_call`, `CallDepth.edge`, `CallDepth.path`, `CallDepth.no_cycle` | `GoLean/GoCore/RecoveryGraph.lean` | Proved; separate closed-finite-DAG-to-table-size theorem not claimed |
| Last-statement return/panic or both-branch termination policy | `checkReturns_sound`, `checkReturnsList_sound`, `checkReturns_complete`, `checkReturns_iff` | `GoLean/GoCore/RecoveryAdmission.lean` | Proved; this is a syntactic return policy, not a bounded-execution termination theorem |
| Typed signatures and bodies, all functions, complete named admission | `require_eq_ok`, `sequence_eq_ok`, `checkFunction_iff`, `checkFunctions_iff`, `checkRecovery_iff`, `checkRecovery_sound`, `checkRecovery_complete` | `GoLean/GoCore/RecoveryAdmission.lean` | Proved against independent judgments, not successful execution |
| Every admitted body's control typing and absence of cycles | `admitted_all_bodies`, `admitted_no_cycle` | `GoLean/GoCore/RecoveryAdmission.lean` | Proved; includes uncalled functions |
| Whole A2 and second-fixture admission, malformed controls, generic bytes and equal re-panic | 46 named theorem declarations in `Tests.RecoveryTyping`, `Tests.RecoveryA2Artifact`, `Tests.RecoveryTypingFixture` | `Tests/Recovery*.lean` | Kernel-proved static examples/families; not substituted for generic runtime/client rules |
| Complete fresh native artifact correspondence, five functional/directness/order observations | `scripts/check-recovery-typing`, `tools/check-recovery-typing-artifact.lean`, `tools/check-recovery-fixture-controls.py` | Dedicated gate and sealed `2026-09-06_recovery-static` evidence | Executably tested; not a compiler theorem or universal Go conformance proof |
| Actual mixed heap, first-match environments, live pointees, frame/capture/defer lists, panic chains and recovered continuations | Future recovery runtime invariant | Parent recovery runtime lane | Deferred and mandatory for O2 |
| Generic actual setup, all-successor preservation, terminal-aware progress/readout and fixed-stream driver/observer bridges | Future recovery runtime contracts | Parent recovery runtime lane | Deferred and mandatory for O2; admitted arbitrary bytes/equal re-panic must remain supported |
| Reusable call/unwind WP rules and both Iris customers | Future customer rules and functional proofs | Parent customer lane | Deferred and mandatory; shared semantic roots do not duplicate exclusive Iris resources |

The standalone proof checks no Go source lexical validity. Source-to-GoCore
scoping/identity correspondence is a frontend assumption with fresh artifact
tests, to be discharged by a separate compiler argument. Repeated `_` storage
keys are explicitly out of this profile, not asserted to be invalid Go.
String variables/general interface operations, nil pointer defaults as live
roots, recursive graphs and other exclusions are recorded in the design note.
The opt-in predicates leave existing A3a admission and O1 typing unchanged.

Independent review at parent `1ae77483` found no admission/scope/capture/cycle
defect, but required RS-1: distinguish an explicit surface exclusion from a
malformed body. The follow-up in
`docs/evidence/2026-09-06_recovery-diagnostics/` records the correction, paired
kernel failures, freshly typechecked outside-profile Go and the expanded
helper audit. The original evidence remains the pre-correction snapshot.
