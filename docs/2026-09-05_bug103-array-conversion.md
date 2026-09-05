# BUG-103: array value conversion

Status: implementation and validation complete; ready for independent review.
[AGENT], 2026-09-05.
Lane: `bug103-array-conversion`, based on main
`8db2d6dad165393f4d3cdffee63b8e7d624f39e6`. This is the independent semantics
fix lane authorized alongside the Iris consumer exercise. It does not edit
the customer package or change the core/customer boundary.

## Contract and implementation

The pinned Go specification (`deps/go/doc/go_spec.html`, commit
`c19862e5f8415b4f24b189d065ed739517c548ba`, go1.26.5),
spec#Conversions and spec#Type_identity, permits conversions between defined
array types whose underlying array types are identical: same length and same
element type. Array values copy their elements; pointers and slice descriptors
inside them retain their references. A zero-length conversion still evaluates
its operand.

`convertValueToTy` had no array-operand arm for a resolved array target. Legal
conversions reached GoCore and returned `unsupported`. The new arm calls
`normalizeValueForTy` on the target array type and operand. The existing
normalizer checks array length and normalizes elements using structural type
descent. There is no heap allocation, state mutation, or choice consumption in
this operation. The array representation is a persistent value; copying it
preserves the contained references, while later array/struct updates construct
new values.

The executable and relation already share the total `applyStrictOp` premise
in `Step.strictApply`. Both therefore acquire the same conversion behavior;
no new relation constructor or evaluator-only branch is needed.
`convertValueToTy_locSup` gains the array case by applying
`normalizeValueForTy_locSup`. The existing `Step.preserves_wf` and
interpreter/relational coherence theorem builds check the composed change.

This is not static admission. `GoValue.array` has no source type, and
normalization cannot establish the legality of a source/target conversion.
For example, integer normalization can narrow a malformed hand-built value,
and the normalizer's scalar fallbacks are not a complete value typing check.
The current native frontend delegates Go type checking to `go/types`; a
machine-level typed admission judgment remains an independent master-plan
obligation. Successful slice-to-array and slice-to-array-pointer conversions
remain the separately recorded FR-10 frontier; the existing short-slice panic
rules are unchanged.

## Regression evidence

The original `structs/decl-order-reversed/conversion-array-target` returns 104
in Go and failed at `lean-observation` with `unsupported` before this change.
Five added cases in the same family were run before the runtime edit: all
also reached Lean and failed at the same stage, for the array target named in
the refusal.

| Suffix in `structs/decl-order-reversed/` | Discriminator |
| --- | --- |
| `conversion-array-target` | defined-to-defined and defined-to-unnamed conversion, independent value copies |
| `conversion-unnamed-target` | unnamed array identity conversion, independent copy |
| `conversion-nested-copy` | recursive arrays of structs, independent nested field values |
| `conversion-shared-references` | pointer/slice referents remain shared; replacing fields only changes the copy |
| `conversion-empty-eval-once` | zero-length value, operand call evaluated once |
| `conversion-float-elements` | float32 element kind and copy behavior |

Four direct eval tests cover malformed-IR boundaries that valid Go cannot
exercise: narrow integer normalization as a positive control, wrong array
length, wrong nested array length, and mismatched float element kind.

The capped core build passed, including the StateWf and coherence modules.
The eval executable passed 202 checks. The focused differential ran 23 cases:
22 PASS and one unchanged FR-10 FAIL. All six BUG-103 rows passed; the BUG-020
pointer/slice/map/func controls and the short-slice panic controls matched the
baseline.

The full ordinary `scripts/ci --diff` run measured **3598 cases = 3353 PASS /
245 FAIL**. It exited 1 for exactly the expected baseline drift: the original
BUG-103 row changed FAIL→PASS and five new rows were PASS. Every other
existing result/stage matched; there were no removals or lane moves. The
negative corpus passed all 394 oracle-rejection cases. All other gate checks
passed, including the warning-free core build, 202 eval tests, frontend
unit tests, frontend pins, harness self-tests, and generated-vector checks.
One slow-tier case used its existing cached certification. No recertification,
negative frontend rejection result, or zero-refusal coverage claim is made.

The baseline was then updated only for those six entries, with the full-run
reason in its header. BUG-103 was closed and the ledger's current counts
updated: 3593 + 5 = 3598, 3347 + 1 + 5 = 3353, and 246 − 1 = 245. The
post-vintage red bucket decreases 66→65. The ordinary baseline comparison now
matches all 3598 recorded results, and `check-bugs.sh` passes. The final
`scripts/ci` reruns the standing checks and judges the same complete recorded
run against this corrected baseline and passes; no runtime or fixture code
changes followed the full differential measurement. The initial record
update used a heading spelling the reconciler did not recognize, so it read
a historical count instead and reported two C4 findings. Restoring the
established parseable count line removes both. The remaining C13 historical
Go-version citations and C5 FR-7 citation are pre-existing record findings,
outside this fix.

Evidence is in `docs/evidence/2026-09-05_bug103-array-conversion/`, including
the initial full gate's honest failing verdict, the full result/meta records,
and the subsequent gate verdict. The runs were on a dirty worktree at the
listed base; the evidence manifest binds them to the tested source bytes.

## Consumer-facing implications and handoff

This fix needs no customer API change. The shared total strict-operator
premise and the existing normalization bound theorem support the executable
extension without a second semantic definition. The separate typed-admission
obligation remains visible: neither `StateWf` nor successful normalization
proves that arbitrary machine inputs correspond to legal Go.

Independent adversarial review and explicit user merge permission are still
required. There is no merge or push in this lane. No wire/lowering change is
made, so the charter's special post-merge frontend slow-recertification rule
is not triggered.
