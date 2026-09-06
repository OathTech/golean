# I1 declaration-query prototype

[AGENT], root integrator, 2026-09-06. Owned worktree `typed-i1-declarations`,
based on the integration branch at `f3913e06`. This experiment implements
the first metadata-query obligation in
[`docs/2026-09-06_i1-admission-design.md`](../../docs/2026-09-06_i1-admission-design.md).
It is outside the default build and is not an implemented I1 boundary.

`Prototype.lean` defines a positive function declaration containing stable
identity, parameter/result declarations, variadicness and wrapper metadata,
with no executable body, refusal reason or support bit. The projection from
the current `Func` is an experiment for declarations whose full signature
already exists; it does not repair or legitimize arity-only quarantined
functions whose parameter types currently contain invented refusal markers.

Generic kernel theorems establish:

- projection commutes with actual first-match function lookup, even for
  malformed tables with duplicate IDs;
- the actual `concreteMethodSignature?` factors through the projected
  declaration table, preserving receiver removal, ordered parameter/results,
  variadicness and missing-declaration behavior;
- the actual `satisfiesMethodSig` has the same answer with that independent
  signature table;
- changing a function body leaves its projected declaration unchanged.

Four kernel probes retain a variadic first duplicate, absent lookup, body
independence and an exact signature for a declaration with no code. These
are metadata facts. They do not authorize executing a missing body and do
not prove call/dispatch support closure. Receiver selection still invokes
the existing `concreteMethodForDynamic?`; inspection confirms that operation
reads the method table and receiver types, with its state parameter passed
to the receiver helper currently unused. The final live API should take
those context facts directly instead of constructing dummy machine states.

No executable source, wire schema, type table or rejection stage changed.
`Ty.unsupported`, the other three executable refusal markers and
`TypeDef.opaqueDecl` remain in the current machine. In particular, this
prototype's use of existing `Ty` is not the final identity representation
for signature-only basic/imported types: current wire examples encode
`complex128` as a fabricated named opaque declaration and `iter.Seq[int]`
as an imported-instantiation marker. I1 must replace those with exact positive
identity facts at emission/lowering, not parse their names in GoCore or
invent layouts/comparability.

Next establish the declaration wire/envelope and identity translation,
preserving the reserved prefix and indices, then separate actual executable
definitions and prove support/closure before removing bodies or guarded
call sites. The independent census's 522 passing marker-bearing cases and
70 syntactic closure hits remain constraints; this projection does not
resolve them. Guarded formatting paths, portable bytealg dead branches and
interface target precision retain their distinct obligations. B7 migration
and this I1 work remain separate changes.

Validation uses the unchanged pinned toolchain and resource caps:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake build
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean spikes/i1-declarations/Prototype.lean
```

The fresh prototype elaboration also audits every local/imported GoLean
declaration against the existing foundational axiom allowance. Early proof
attempts in `artifacts/i1-declarations/prototype-*.log` are retained: copying
the fold lambda generated a different opaque matcher and did not establish
the desired equation. The final proof instead derives the projection using
a general fold-commutation lemma instantiated with the actual operation,
avoiding any assumption of equality between separately generated matchers.
Independent review and final live-interface audit coverage remain owed.
