> Historical prototype record, selected from `7ac3eb46bb3e2fe9c15b86b509569ef086327453`
> by [AGENT] 2026-09-08. Its validation describes that prototype only.
> Current scope, changes and fresh evidence: [I1 landing charter](2026-09-08_i1-declaration-landing-charter.md).
> Evidence paths below refer to the retained prototype branch; they are not
> copied into this landing. Production I1 integration remains outstanding.

# I1 positive declaration wire increment

[AGENT] root integrator, 2026-09-06. Work in progress, based on the
declaration-query prototype `8ea5a74b` and the independent I1 census/design.
This supplies a positive declaration serializer in the native frontend.
It is not yet connected to package emission or accepted by the executable
decoder. No marker is removed and no case's support boundary changes here.

The immediate problem is concrete: existing refused plain functions retain
only arity, while method signatures can represent `complex128` as an
invented named opaque type. The final separate declaration table needs exact
type/signature facts before those executable placeholders can be removed.
`emitDeclarationType` obtains these facts from `go/types` without consulting
a body or the executable type-support machinery.

The separate schema represents every closed Go basic type positively,
including complex types and `unsafe.Pointer`. A nominal type has a stable
declaration key and a separate ordered list of positive type arguments;
`iter.Seq[int]` requires no opaque TypeDef or guessed function layout.
Aliases are erased. Structural types retain pointer/slice/map/array shape,
array length, channel direction, function parameter/result types and
variadicness. Parameter binding names and method receivers are excluded
from function type identity; receiver metadata belongs to a method
declaration separately.

Anonymous struct identities retain ordered fields, exported/unexported
identifier identity, embeddedness and every byte of the tag. Tags use an
integer byte array: passing an invalid-UTF8 Go tag through a JSON string
would merge it with a different replacement-character tag. Anonymous
runtime interfaces retain their full, canonically ordered method set;
unexported member identities include the defining package path.

This channel describes closed runtime declaration types. Uninstantiated
type parameters, constraint-only interfaces, invalid/untyped basic kinds,
unknown array lengths and malformed channel directions produce named
frontend errors. A local type absent from the checked source inventory
also refuses; the existing name helper's diagnostic placeholder is never
emitted as a positive declaration identity. Existing stencil substitution
errors propagate. Rejected function/template metadata remains a frontend
envelope concern; this does not authorize rejecting a package merely
because it contains an unused template.

Focused tests compare declaration equality against `types.Identical` for
aliases and named types, generic arguments, parameter-name erasure,
variadicness, channel directions, array bounds, field tags and interface
method ordering. Additional probes distinguish same-spelling unexported
members from different packages, retain invalid tag bytes, preserve actual
imported `iter.Seq` identities and distinguish separate local declarations.
Invalid nested type requests must return an error and no declaration.
No test claims a complete Go type-identity theorem.

This is finite positive metadata, not a universal runtime descriptor
algebra: it supplies no default value, layout, comparability, dispatch body,
reflection operation or allocation permission. The next implementation
steps are a strict decoder into positive declaration facts, exact function/
method envelope emission, query-preservation integration, and checked
entry/argument-specific code closure. The 522 passing marker-bearing cases
and their 70 syntactic guarded-call hits remain mandatory constraints.
Portable-library guards, formatting guards and interface target precision
still need their respective checked transformations or separately justified
semantic completions. B7 representation equivalence remains separate.

Validation commands use the worktree-local Go cache and pinned toolchain:

```sh
GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off go test ./tools/nativefrontend -run '^TestDeclaration' -count=1 -v
GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off go test ./tools/nativefrontend -count=1
```

The four focused tests and full frontend suite pass. Independent review
`58cd8b69` passes 324 additional pairwise Go identity comparisons and
substitution/local-stencil controls. Review `08f7984f` accepts the exact
eight-message diagnostic inventory update. Initial ordinary CI `47743`
failed that missing inventory and absent local corpus records; the complete
diagnostic suite passed after correction and ordinary CI `1329` then exited
0. Its 3,607 executable/394 negative records are explicitly cached renderer
evidence, with original metadata and a checked source-difference inventory;
they are not fresh conformance runs for this unused helper. The source,
logs, review references and reuse argument are retained in
`docs/evidence/2026-09-06_i1-declaration-foundation/`.

Future connection to wire/lowering requires the charter's full differential
and slow certification train; unused helper tests do not discharge it.
