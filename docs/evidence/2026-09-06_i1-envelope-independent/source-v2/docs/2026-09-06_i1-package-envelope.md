# I1 package declaration envelope

[AGENT] string-members / I1 envelope lane, 2026-09-06. Base: reviewed strict
parser `7ac3eb46`. Root authorized this bounded production-envelope increment
under the typed-consumer sprint charter. This document describes work in
progress; executable admission and runtime marker removal remain later work.

The native emitter will add a `declarations` field to its existing program
wire. It will bind every final function and method entry to positive types
from `go/types`, including declarations whose bodies are refused. The existing
runtime interpreter remains unchanged. The existing runtime decoder only adds
the new root key to its known, deliberately unread metadata keys; the strict
package API is the sole consumer of these positive facts. No declaration supplies a
body, layout, default value, reflection permission or executable-demand proof.

## Exact scope and representation

The envelope has a version tag, package-unit paths, a nominal-origin/arity
inventory, ordered function and method bindings, and complete interface
requirement bindings. Function/method bindings contain the final table index
and stable identity. The decoder checks a bijection with the actual enclosing
wire arrays, including order, lengths, names, receiver names, parameter/result
arity and variadicness. Unknown roles or incomplete bindings refuse the new
channel. Runtime bodies are opaque inputs to this metadata decoder.

Source signatures exclude receivers and parameter binding names. A source
function has its exact source signature. A lifted closure additionally has an
explicit capture prefix and a separate lowered ABI signature: prepending
capture-pointer types must produce that ABI exactly. A synthetic helper has
its own signature and an explicit closed helper role, without pretending it
is a source function. Methods retain package-sensitive member identity,
source receiver, adapter receiver and exact signature; promotion does not
replace the declaring receiver with the adapter receiver.

The nominal inventory is complete for all nominal origins transitively
referenced by these positive facts, plus package-scope defined type origins
in the source units retained by the emitter (including their generic arity).
Aliases are transparent. Closed local types retain their existing scope and
enclosing-instantiation identity. Uninstantiated local templates and all
underlying layouts of referenced imported types are outside this inventory
claim. An opaque runtime spelling is never a source for a nominal declaration.
Complex and unsafe-pointer basics stay basic identities; they do not become
invented nominal types.

Interface requirement bindings cover every final interface TypeDef and its
complete `go/types` method set. They preserve member package, parameter and
result identities and variadicness. The decoder checks exact final indices
and identities together and rejects duplicate native type identities. The
older runtime requirement headers omit declaring packages. Their bare-name,
arity and variadicness multiset must match the projection of the complete
positive requirements, consuming each once. Distinct private members with the
same spelling retain their full package identities, including when their
header shapes coincide. This check does not reconstruct the missing runtime
package/type information. The empty-interface identity needs no
invented TypeDef. The old imported-carrier `exported` coverage convention is
not promoted into a claim of complete concrete unexported method coverage.

## Actual emitter construction inventory

The binding points are source declarations and initializers; quarantined plain
functions and methods; closed function and method stencils; lifted literals;
promotion wrappers and refused promotions; declared and call-site interface
anchors; imported stubs; sync methods and helpers; harvested atomic model
methods; package initialization; formatting lifts; deferred recover/close/sync
helpers; and the per-site Once helpers. Signatures are captured where the
actual `go/types` objects or explicitly constructed helper types exist.
No final-wire type-to-Go reconstruction is used.

Transient metadata travels with each function/method map until final array
assembly. This preserves correspondence across renaming, worklist drains,
promotion, sorting and quarantine rollback. It is removed from the executable
entry objects and moved into the envelope before JSON encoding. A shadow-model
harvest carries its already emitted declaration facts with its method entries.
Positive serialization uses isolated identity bookkeeping so collecting facts
does not register executable types or change the runtime worklists.

## Decoder and query boundary

The new Lean input takes the entire raw byte document through the reviewed
strict parser before selecting the envelope. Both duplicate keys and Unicode
loss therefore refuse before field projection. Every envelope object uses an
exact schema; nominal identities are unique and every named reference has the
declared arity. Function/closure/helper roles are checked separately.

Positive semantic records and total metadata queries contain no frontend role,
refusal reason or body. The adapter retains wire provenance separately. Any
factoring theorem about the current runtime query must state the actual
signature-correspondence premise; representation equality alone does not prove
that a hand-edited positive type equals a runtime type, especially an old
opaque marker. Actual-emitter correspondence tests and the existing prototype
projection are separate from that future runtime connection.

## Required evidence

The dedicated gate will invoke the actual emitter and real Lean byte-input
decoder on source-derived positive cases and structural mutations. Controls
must cover missing/duplicate/reordered bindings, changed IDs, nominal omissions
and arity changes, closure capture/source/ABI confusion, unknown helper roles,
method receivers and variadicness, incomplete interface requirements, raw
duplicate keys and malformed bytes. Refused bodies with complex/imported
generic signature facts must remain visible metadata, and source/ABI examples
must differ where captures exist. Go `types.Identical` supplies independent
signature equality observations for selected queries.

Fresh build, declaration audit with compiling unused-axiom controls, focused
source-derived correspondence, and ordinary CI are required. The frontend wire
change also requires full differential and slow certification at the final
integration source. The 522 passing marker-bearing census rows and 70 guarded
syntactic call hits remain preservation constraints; a blanket closure refusal
is not part of this increment. No baseline drift is self-waived.

## Bounded implementation checkpoint

The construction-point producer, `GoCore.DeclarationContext` and
`NativeDeclarationPackage.decodeBytes` are implemented. The positive context
proves exact signature comparison and exact selected-method matching without
reading any body. It is not yet a factoring theorem for the current runtime's
receiver selection or its supported-type representation. The one NativeToIR
change permits the known `declarations` root key without reading its value.
Malformed metadata cannot create authority through that ignored key; callers
of the positive channel must use its strict byte API. The adapter validates
binding header shapes, while bodies, non-interface layouts and global values
remain outside its validation scope.

Six actual loader/emitter fixtures exercise all three function roles, six
method roles and ten helper roles, including 223 imported method entries.
Fresh Go supplies 16 ordered source-signature comparisons, five source-origin
arities, two selected-method/receiver observations and two complete private
requirement sets from separately rechecked three-package source. The latter
cover both differing and identical bare header shapes. The package gate checks
54 malformed whole documents and six schema-valid false metadata documents.
The latter deliberately decode successfully, then fail the fresh Go checks:
wrong unused-origin arity, source signature, receiver, member package and
interface signature, plus a private requirement's declaring package. Reordered
native private headers must also preserve both fresh Go observations. This
keeps source correspondence distinct from schema
validity rather than claiming a JSON parser proves Go typing.

A separate fresh comparison against the exact `7ac3eb46` frontend covered all
80 distinct wire representatives of the historical 522 passing marker-bearing
cases, plus the five fixtures. Every candidate document strict-decoded; removing
only its new root field restored the base output byte-for-byte in all 85 cases.
This is frontend preservation evidence, not a re-certification of the 522 Go
executions or their 70 guarded-call paths. Full CI, final pin disposition,
independent implementation review and integration certification remain owed.

Independent v1 review found and reproduced an interface-index bijection gap
under duplicate native type IDs and rejection of valid same-spelling private
requirements from different packages. The repaired decoder checks exact
index/identity pairs and unique native type IDs, and consumes projected header
multisets while retaining full positive MemberIds. Original v1 source and
accepted/rejected inputs remain preserved. The first full CI ended with
ENOSPC during audit copies and log writing, before differential execution;
that failed run is not full conformance evidence.

The private source probe also exposed the pre-existing emitter collision for
a *defined* `Mix` embedding `p.m` and `q.m`: both old dispatch entries receive
the ID `main.Mix.m`. The new envelope visibly refuses that duplicate FuncId.
The positive fixture uses transparent interface aliases and their anonymous
signature types, which have complete TypeDefs without that colliding dispatch
table. Repairing private-method runtime identity remains later work; this
increment does not rename, collapse or silently drop those entries. The exact
named-source refusal and source files are retained as a bounded limitation.
