> Historical prototype record, selected from `7ac3eb46bb3e2fe9c15b86b509569ef086327453`
> by [AGENT] 2026-09-08. Its validation describes that prototype only.
> Current scope, changes and fresh evidence: [I1 landing charter](2026-09-08_i1-declaration-landing-charter.md).
> Evidence paths below refer to the retained prototype branch; they are not
> copied into this landing. Production I1 integration remains outstanding.

# I1 positive declaration identities and decoder

[AGENT] root integrator, 2026-09-06. Implementation increment after serializer
`298e4da1` and independent reviews `7ae7fc0a`/`cf13789f`. This is **INCOMPLETE
I1 work**: neither production emission/lowering nor executable admission uses
this channel yet. No refusal marker or passing support case is removed here.

`GoLean/GoCore/Declaration.lean` represents positive closed declaration
identities independently of supported runtime values. It includes every
closed basic kind, keeping `uintptr` distinct from `uint`; it cannot encode
the runtime integer representation's unbounded/untyped placeholder. Named
types have a `TypeId` and ordered type arguments. Structural identities keep
array bounds, channel direction, signatures/variadicness, ordered fields,
package-sensitive member identifiers and raw tag bytes. A runtime interface
contains its complete unique method set in canonical package/name order.
There are no opaque/refusal constructors, optional bodies, support flags,
layout/default/comparability facts, or reflection permissions.

`equality_exact` proves soundness **and completeness** of the total transparent
structural comparisons over types, fields, methods and their lists. The
`LawfulBEq` instances follow from that theorem. This proves equality of the
representation; it is not a theorem identifying arbitrary unchecked raw
constructors with valid Go types. In particular, direct interface constructors
must satisfy the canonical method-set invariant. Metadata validity and the
translation between supported runtime `Ty` and declaration identities remain
obligations of the package/context integration.

`GoLean/NativeDeclaration.lean` consumes the separate serializer schema.
It checks exact keys, primitive shapes, byte bounds, closed basic tags,
channel directions, variadic slice shape, method signature shape and an
explicit nominal declaration/arity inventory. Duplicate nominal/method
identities refuse. Method order is normalized, preserving semantic identity
when the wire lists the same method set in another order. No unsupported
kind falls back to a positive declaration. The nominal inventory supplies no
layout or executable authority.

The adapter uses the same style of partial JSON descent as `NativeToIR`,
outside the total semantic core. It receives a parsed `Json`; it cannot
recover duplicate raw JSON keys that the enclosing parser discarded. Raw
duplicate-key rejection is an explicit outstanding package-envelope seam
before production connection. This decoder also does not replace Go's
source type checker (for example validating every manually constructed
map-key type or source identifier). The compiler-correctness arrow remains
tested, as required by the charter, rather than being implied by a schema
check. These limits do not authorize accepting an unproved executable demand.

The dedicated gate builds and freshly elaborates the core, adapter and
tests. A real `go/types` producer emits 24 identities and all 576 ordered
equality comparisons, including recursive nominal references, instantiated
generic signatures, complex types, uintptr/unsafe.Pointer, invalid tag bytes,
variadicness, channel directions and anonymous interfaces. The actual Lean
decoder and proved comparison agree with every pair. Seventeen malformed
inputs invoke that decoder, and an extra method-order permutation checks
canonicalization. The gate checks pair inventory/order rather than accepting
576 copies of one comparison. This is declaration correspondence evidence,
not Go program execution conformance.

The post-import audit checks all imported GoLean/test-local declarations
against the existing foundational axiom allowance. Four unused injected
axioms must first compile and then be rejected, including one after the
audit's own initial evaluation. Initial standalone gate `34109` passed,
checking 1,687 declarations and all four poisons. Ordinary CI includes the
same gate. Ordinary CI `31463` initially failed only because the comment
prose `admit executable demand` matched the standing escape-hatch scan.
Changing that one word to `authorize` preserves the code, claim and gate;
independent exact-delta review `d2ed3ecd` accepted it. Corrected ordinary
CI `3794` exited 0, including the warning-free default build, fresh dedicated
gate, frontend units/diagnostics and 202 eval cases. Its 3,607/394 corpus
records are explicitly cached from the earlier renderer source, with the
original metadata and source-reuse argument retained in the foundation
evidence. This is not fresh full executable or slow-wire certification.

Independent review `e9045844` is a bounded PASS: separate fresh elaboration
of the two new Lean modules, fifteen additional identity/schema challenges,
and kernel use of the exact equality theorem. Its stated package-envelope
and production-closure limits remain outstanding. Raw author logs, original
reviewed inputs, final source copies, comment-delta hashes and the fresh
24-type/576-pair Go JSON artifact are preserved under
`docs/evidence/2026-09-06_i1-positive-declarations/`. No source code changed
after the final passing CI; this completion paragraph is the later doc update.

Next: bind exact function/method declarations and nominal inventories into
the package envelope; prove the current method queries factor through these
facts; check entry/argument-specific all-choice executable closure; remove
the old executable markers while preserving indices and reserved runtime
error metadata. The 522 passing marker-bearing cases and 70 guarded-call
hits remain constraints. B7 equivalence, I1 stage changes and any fidelity
repair remain separately reviewed and measured. Wire/lowering integration
still requires full differential and slow certification at the final source.
