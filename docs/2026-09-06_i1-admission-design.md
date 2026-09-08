> Historical prototype record, selected from `7ac3eb46bb3e2fe9c15b86b509569ef086327453`
> by [AGENT] 2026-09-08. Its validation describes that prototype only.
> Current scope, changes and fresh evidence: [I1 landing charter](2026-09-08_i1-declaration-landing-charter.md).
> Evidence paths below refer to the retained prototype branch; they are not
> copied into this landing. Production I1 integration remains outstanding.

# I1: declarations, executable bodies, and admission

[AGENT], `typed-preflight`, 2026-09-06. Bounded design assessment of the
sealed `10fefeb3` corpus and current lowering/call machinery. No core edits,
new semantic policy, or acceptance waiver. Evidence:
[independent census and representative artifacts](evidence/2026-09-06_i1-admission-design/).

**I1 is credible as a staged declaration/admission refactor. Blanket marker
rejection is not credible.** Signature separation is necessary but not
sufficient: some passing entry points contain syntactic paths to guarded
refusals. Clean executable code needs a checked support/closure argument
before those declarations or branches can be removed.

## Verified measurements

An independent scan exactly reproduces the parent's 696 records, including
every wire hash, marker path, name, kind and reason: **522 recorded PASS
cases and 174 FAIL cases** contain markers. The PASS cases use 80 distinct
wire byte strings. Their marker categories are:

| Declaration categories | PASS cases |
| --- | ---: |
| Functions only | 281 |
| Methods only | 185 |
| Functions and methods | 40 |
| Functions, methods and types | 13 |
| Methods and types | 3 |

Every marker in this census is at a declaration boundary:
`$.funcs[i]`, `$.methods[i]`, or `$.types[i].def`. There are no nested wire
expression/statement/assignee/type markers in these 696 records. That does
not make the resulting GoCore clean: `NativeToIR.decodeFunc` synthesizes
`Ty.unsupported` parameters and `Stmt.unsupported`; `decodeMethod` retains
real signatures over unsupported bodies; `decodeTypeDef` makes
`TypeDef.opaqueDecl`.

`atomics/counter/add` records unused `And`/`Or` and `WaitGroup.Go` method
declarations. Removing their signatures changes Go method-set answers.
`methods/signature-basic-unlowerable/iface-uncalled` actually queries an
interface requiring `OverflowComplex(complex128) bool`, then calls the
healthy `Kind` method. Imported `iter.Seq`/`Seq2` signature identities are
another concrete family. Sixteen passing rows contain type-definition
markers; they cannot all be rejected or replaced by invented empty structs.

A second exploratory scan closes the manifest entry and `$pkginit` over
wire `func` references, expanding interface anchors to every concrete
method of the same name, as the existing `checkInitQuarantine` does. It
finds quarantined targets in **70 of the 522 PASS rows**, with no missing
referenced IDs. This is a syntactic overapproximation, not a proof of
dynamic reachability:

| Target family | PASS rows with a syntactic path |
| --- | ---: |
| `goleanShimUnsupported` | 46 |
| `internal/bytealg.Cutover` | 24 |
| `internal/bytealg.IndexString` | 23 |
| `internal/bytealg.Index` | 1 |
| `main.fancyLog.Infof` | 1 |

These counts overlap. `interfaces/quarantined-dispatch-teeth/installed`
selects `quietLog`; same-name expansion spuriously includes `fancyLog`.
The portable `bytealg` substitution records `MaxLen=0`, making calls to
its assembly placeholders dead. Formatting shims contain genuine guards:
ASCII-only quoting, supported verbs, dynamic argument kinds and counts.
Those guards require proofs or more complete lowering; declaration pruning
alone cannot remove them soundly.

## Proposed separation

Use three interfaces, with illustrative names rather than a mandated API:

1. **Declaration facts in fixed context.** `FuncSig` and `MethodDecl` carry
   exact receiver/parameter/result identities, variadicness, method-set
   coverage, dispatch identity and wrapper/recover metadata independently
   of code. Type identity/display facts survive even when no value layout
   is supported. `satisfiesMethodSig` reads these facts directly; it must
   stop finding a dummy `Func` merely to recover its signature.
2. **Executable definitions.** A code table contains only fully lowered
   real bodies. Interface invocation is an explicit dispatch operation or
   declaration role; it does not need a fabricated body calling
   `$interface-method-unreachable`. Concrete dispatch selects a supported
   body under the admitted call-target invariant. Preserve receiver
   adjustment, nil checks, arity, variadicness, wrapper transparency and
   the `nilValueMethodText` choice site.
3. **Frontend package and admission result.** Keep refused declarations,
   source locations and reasons outside GoCore in the decoded package
   envelope. Admission takes explicit roots, valid entry arguments and a
   support contract, and returns clean code plus checked closure evidence
   or a named boundary refusal. Do not add `unsupportedBody`, a disguised
   external-call trap, or an optional body whose absence is used as the
   old runtime refusal mechanism.

An identity-only declaration is positive semantic information, not a
reason-bearing dummy executable type. Keep complete identity/signature
facts separate from facts needed for allocation, normalization, field
access, comparison or conversion. A signature may mention a real Go basic
type such as `complex128` without implementing complex values. It must
still be identified as the correct Go type, not as a fabricated named
type. Imported nominal identities must remain distinct by package and
instantiation; absent layout information must never imply an empty layout,
comparability, or an empty method set.

For I1, preserve the existing finite facts needed by satisfaction and
dispatch, with checked translations between signature identities and
supported value types. Retain the reserved runtime-error identity as an
explicit built-in context fact, its inaccessible payload role and the
reserved-prefix invariant. Do not compact type/global indices or delete
initialization effects as a side effect of removing declarations.

## Required closure and preservation obligations

The code table may omit a body only after establishing that the admitted
execution cannot enter it. A function value's identity and signature must
remain available even when the value is never called. Distinguish
declaration/type demand, function-value demand and executable call demand.
Rejecting every taken function value is an unjustified overapproximation.

Closure must cover direct calls, indirect closures and captured values,
method values, interface dispatch, promoted wrappers, deferred calls,
goroutine entry, package initialization and global references. It must
hold for every admitted argument/state and modeled choice, not just the
captured oracle streams. Unknown targets are obligations or explicit
boundary failures, never permission to drop a declaration. Missing method
metadata cannot become a false satisfaction answer.

For reachable guard syntax, produce a checked transformation or an explicit
support proof that makes its branch unreachable before emitting clean
code. A proof must justify removal of the call site as well as its target:
a dangling `FuncId` would merely change unsupported into stuck. The first
bounded implementations should address:

- **Dispatch precision:** prove the installed logger's possible receiver
  types; retain the quarantined method's signature and keep the uninstalled
  control refused before execution.
- **Portable-library dead branches:** establish the substituted `MaxLen`
  invariant, including initialization and possible writes/aliases, then
  validate branch elimination. The substitution-table prose alone is not
  a reachability certificate.
- **Formatting support:** state and check the format/argument/string
  restrictions, propagate them across calls and loops, and justify removing
  unreachable guard branches. For an unproved path, improve the analysis
  or implement the real missing semantics separately; do not discard the
  path or turn its refusal into a recoverable Go panic.

The admission contract is entry/argument-specific; do not silently claim
that one accepted request makes every entry and argument of a package
supported. Recheck when roots/arguments change. A sampling run is not a
proof of this universal closure. The 522 PASS statuses constrain the
implementation, but neither establish refusal-freedom nor license a weaker
admission guarantee.

Prove metadata-query preservation separately from execution preservation.
Then prove that admitted clean execution agrees with the before model on
steps/drivers, choices, terminal outcomes and output. Add actual GoLean
negative controls for a reached refused function, changed indirect target,
missing/forged signature, variadic mismatch, malformed type identity,
unsupported structural demand and violated guard premise. Preserve sibling
successes and the full method-set answers in paired positives. Re-run the
full corpus, separately listing intended earlier refusal stages; no PASS
may become a refusal merely to simplify admission.

## Scope and decision status

Separating existing signature facts from bodies, preserving stable IDs,
introducing checked entry closure and validating dead-code lowering are
ordinary K3 implementation/design choices within approved I1. The census
does **not** force a decision about universal `reflect.Type` descriptors,
layout/addressability of arbitrary types, recursive descriptor construction
or the implementation of reflection. That broader Gate A/F11 decision
remains open independently; I1 should not choose it accidentally.

A genuine descriptor gate arises if a proposed I1 representation must
answer a currently unresolved structural/runtime query for an admitted
type, or changes the reserved runtime-error meaning. Show that concrete
query and competing meanings before invoking charter §7. Marker presence
alone establishes neither that gate nor impossibility. The observed guard
and call-target obligations are substantial engineering work; their
difficulty is not authorization for a waiver.

This refines the earlier B7 design note's shorthand that all nonreserved
unsupported declarations fail at the boundary: their **unsupported
executable demand** must fail, while legitimate declaration facts survive.
B7 remains a separate representation correspondence over the actual before
model. Do not mix I1's validated admission/refusal-stage changes or a
formatting-fidelity expansion into B7 equivalence.
