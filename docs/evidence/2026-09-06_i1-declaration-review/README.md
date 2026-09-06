# Independent I1 positive declaration serializer review

[AGENT] typed_preflight, 2026-09-06. **Bounded PASS** for the three frozen
inputs in `candidate-sources.sha256`, based on `8ea5a74b`. This accepts an
unwired serializer increment. It does not accept I1 completion, any package
admission/closure rule, a runtime descriptor algebra, or a conformance change.

The implementation obtains positive facts from `go/types` without inspecting
function bodies or consulting the executable type emitter. Basic kinds remain
basic (including complex and unsafe.Pointer); nominal identity is separate
from ordered generic arguments. Aliases unalias. Anonymous interfaces flatten
and canonically order the complete method set. Unexported field/method
identifiers retain defining package paths, while exported names omit package
identity. Struct fields retain order, embeddedness and raw tag bytes.
Signature parameters/results omit binding names and receiver identity, which
must be carried separately by the future method envelope.

The generic/local path uses the existing source inventory and naming helper:
unknown local ordinals fail before its diagnostic placeholder could escape.
Locals declared inside distinct active stencils keep distinct enclosing
instantiation identities. The helper can still report an existing stencil-key
rendering failure; callers must keep that refusal visible. This review does
not establish total serialization of every future declaration inventory.

Independent probes run on an exact owned copy of all frontend Go files;
`snapshot.json` records every copied source hash. No author file was edited.
The final `probe-2.log` passes three tests:

- 324 pairwise comparisons against `types.Identical`, including recursive
  nominal types, nested generic aliases, distinct generic origins, flattened
  anonymous interfaces versus named interfaces, embedded versus named fields,
  the named universe error type, and complex generic arguments.
- Receiver erasure, substitution into a nested complex slice, and refusal
  with no declaration for a missing substitution.
- Actual checked local declaration under int versus bool enclosing stencil
  arguments; the emitted identities remain distinct.

The author's four focused tests were inspected, including raw invalid-UTF8
tags versus U+FFFD, unexported identifiers in distinct packages, imported
generic origins, untyped/invalid basics, nested open types, negative array
length, and malformed channel direction. The serializer is downstream of
checked `go/types` data; this is not a claim that it validates every arbitrary
malformed object constructible with the Go API (for example an invalid map
key in a manually assembled map type). Future wire decoding needs its own
strict validation and identity/query-preservation obligations.

The ledger accurately says that no markers are removed, executable support
does not change, and emission/lowering/closure integration remains owed. A
positive signature alone grants no body, layout, allocation or dispatch
permission. No new descriptor or runtime support policy is chosen here.

The ordinary CI was running at review request time. This review neither
reruns nor claims its completion, nor reuses unit tests as the full runtime
or slow certification train required when wire/lowering is connected.
