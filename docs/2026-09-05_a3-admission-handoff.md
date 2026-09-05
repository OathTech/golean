# A3 first admission slice handoff

[AGENT], 2026-09-05. Lane `gate-a3-admission`, base `700128f3`.
Prepared under the [USER]'s authorization to execute the reviewed next steps.

The initial capped core build, full dedicated admission gate and ordinary
CI passed. The [independent review](2026-09-05_a3-admission-review.md) is
PASS for this bounded slice, with no required fix outstanding. All evidence
here predates the rebased combined-tree checks described below.

## Scope and ownership

The opt-in `GoLean.GoCore.Admission.checkBoolean` API is implemented with
soundness/completeness for the exact `BooleanAdmission` conjunction:
`IndexStructure`, actual-driver entry/Boolean argument validity, and a
conservative whole-program Boolean syntax policy. It is not wired into the
frontend/driver and changes no executable language coverage. The API is not
full Go typing or refusal freedom. Methods/globals/initialization/calls are
excluded; method-set/display metadata is explicitly unchecked because no
admitted Boolean operation uses it. The native proof fixture retains all
emitted metadata.

The complete index scan is independent of the syntax policy and includes
references under pointer/slice/map/channel/function types and interface
method signatures that are intentionally absent from `Ty.deps`. It checks
all function bodies and signatures, including unreachable helpers. The
32 kernel regressions include a valid native artifact, malformed rejections,
and a program that is both admitted and proved to refuse on an unbound
variable. This explicit counterexample prevents overstating the boundary.

The design and exact statements are in
[the A3 note](2026-09-05_a3-admission-design.md). Source/evidence records are
in [the evidence directory](evidence/2026-09-05_a3-admission/README.md).

## Integration

This lane changes `GoLean/GoCore.lean` to import the checker; adds an
`AdmissionTests` library and an admission proof/audit step in `scripts/ci`.
The root coordinator owns `GoLean/Interface.lean` and the A1/A2 audit
selection changes, and will integrate these after rebasing onto the landed
BUG-103/interface train. Preserve both new test libraries and both CI
steps when resolving their append conflicts. No baseline re-pin is owed
for this admission-only change. The combined rebased tree still requires
its ordinary gates and A1/A2 consumer checks after those root-owned edits.

The next A3 task is lexical/scoped typing of this Boolean fragment, with
soundness for an independently stated judgment and explicit malformed
scope/name cases. Then extend the entry/value/call/capture/init boundary
toward the actual A2 recovery artifact. General typed runtime states,
preservation and refusal freedom remain separate obligations. The next
work should remove the accepted-unbound counterexample under a stronger
named predicate rather than quietly redefining this existing one.
