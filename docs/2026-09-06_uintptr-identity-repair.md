# BUG-107: preserve uintptr identity

[AGENT] root integrator, 2026-09-06. **Uncommitted repair in progress**, based
on `53ca910a`. This is a K3 fidelity repair, separated from B7 representation
correspondence and I1 refusal-stage movements. No completion or baseline
re-pin is claimed by this note.

While developing I1's positive declaration bridge, I found that
`NativeToIR.intKindOfName` lowered `uintptr` to `.uint64`. A fresh direct Go,
native emitter and shipped-model probe returned Go 8 versus Lean 15:
cross-type assertions in both directions and a `M(uintptr)` method falsely
matching `M(uint64)` all succeeded in the model. A separately built focused
corpus run then preserved five differential failures (assertions, parameter
and result signatures, aggregate identity, interface map keys) and a passing
unsigned wrapping control. Two additional direct/boxed uintptr readouts
failed at `go-observation` under the old explicit observer refusal.

Raw commands, wire bytes, original source hashes and all red records are in
`docs/evidence/2026-09-06_uintptr-identity/`. The focused red run built the
actual source at this worktree; its base build cache was copied from the
earlier I1 worktree, and Lake rebuilt the changed dependency graph. This is
executable evidence, not a manually substituted expected result.

The pinned `deps/go/doc/go_spec.html` at `go1.26.5` supplies the ruling:
spec#Numeric_types makes numeric types distinct except the explicit byte/rune
aliases and defines uintptr as an unsigned type capable of storing pointer
bits. spec#Type_identity, spec#Method_sets and spec#Type_assertions determine
the failed cases. Equal widths do not authorize equal type identities.

The repair adds a distinct `IntKind.uintptr`, using the unsigned width
`8 * Platform.wordBytes`. The existing pinned platform still has 64 bits.
This also corrects the platform field documentation: the integer width does
not itself define uintptr width. No new platform is advertised.

The lowerer preserves the new kind in ordinary and atomic values; atomic
classification explicitly includes it. Existing generic integer operations
provide normalization, conversion, comparison, allocation and arithmetic.
The relational atomic rules and interpreter share `atomicPlan` and the same
total premises; no evaluator-only rule or hidden choice is added. Their
generic soundness/completeness proofs must rebuild on the new constructor.

The Go observer and Lean observation decoder carry `uintptr` explicitly,
with the pinned unsigned range. They retain distinct uint64 observations.
The old unknown-kind test uses genuinely unknown `uint128`; added checks
reject negative/overflowing uintptr observations and establish its distinct
encoding. The eight native regression rows exercise actual lowering and
execution; existing uintptr atomic rows remain required compatibility tests.

Required next evidence: warning-free default build, fresh focused identity
and atomic runs, actual observer negative controls, compiled core coherence
and dependency audits, independent adversarial implementation review, and
the full differential gate. Lowering changes require the standing slow
certification train before final runtime integration. Any resulting stage
movement is recorded separately from B7's zero-drift claim. B7 must rebase
its reference and recapture observations after this independently accepted
repair, rather than asserting equivalence across a corrected wrong answer.
