# A3 first admission slice: indices, entry, and Boolean syntax

[AGENT], 2026-09-05, worktree `gate-a3-admission`, base `700128f3`.
The [USER] authorized executing the reviewed next-step sequence. This is
its first bounded A3 implementation, not completion of typed admission.

`checkBoolean` is an opt-in API for a customer that chooses this profile.
Neither `NativeToIR` nor `runProgramSetupM` invokes it automatically. Existing
runtime coverage is unchanged; ordinary GoLean inputs do not thereby gain
any admission guarantee. There is no generic `Accepted` alias.

## Contract written before implementation

The checker returns a named admission error or unit. Its theorem states
that success is equivalent to the conjunction of three separately named
predicates. None is defined using an interpreter run.

1. **IndexStructure**: the exact two reserved leading type entries;
   `TypeEnv.WellFounded`; unique type and function keys; every `Ty.defined`
   occurrence in the entire type table and program syntax is below the
   table size. The occurrence traversal includes pointer/slice/map/channel
   and function types and interface method signatures, which intentionally
   contribute fewer edges to `Ty.deps`. This is index structure, not all
   name/reference validity, wire validity, or Go typing.
2. **Entry**: the actual `findFunctionIn?` lookup used by the driver finds
   the named function; its argument count equals the supplied value count;
   its parameters are Boolean and the supplied values are Boolean. No
   coercion, normalization, or successful execution substitutes for this
   value/type check.
3. **BooleanSyntax**: all functions, including unreachable ones, have
   Boolean parameters/results and use only Boolean literals, variable
   expressions, negation, conjunction/disjunction, variable assignment,
   Boolean local initialization/declarations, blocks/sequences, conditionals,
   and return. Calls (including closures/defer), globals, methods,
   variadic/wrapper functions, and a `$pkginit`
   function are rejected. Thus checking the entry body cannot accidentally
   leave initialization or a reachable helper outside the support policy.

The Boolean syntax predicate is a deliberately conservative syntactic
policy. It does not check lexical variable binding, duplicate local names,
or definite return. A malformed use of an unbound Boolean variable is an
explicit accepted counterexample to any interpretation as `ProgramWellTyped`
or refusal freedom. A separate small value/type judgment characterizes
the admitted Boolean argument values; it is not a runtime-state invariant.

Reserved table entries include the machine's opaque runtime-error entry;
unused additional type definitions may likewise be opaque. The fragment
does not execute operations at those types. Index bounds do not assert
that `Ty.interface` names, method-set keys, field identifiers or display
metadata correspond to declarations. Display metadata is diagnostic only;
method declarations are excluded by the policy. No stronger validity claim
is made for the resulting GoCore artifact, much less for native wire input.

**Implementation refinement from fresh native evidence, [AGENT]:** even this
Boolean source emits a full empty method-set record for reserved `struct{}`.
The final policy leaves method-set/display records explicitly unchecked:
none of the admitted Boolean operations uses this metadata. A proposal to
whitelist just that emitted record was rejected during coordination because
the admission boundary should not encode frontend layout assumptions.
An arbitrary method-set key is an explicit accepted limitation witness.
The artifact is compared whole, without deleting native metadata to pass.

## Intended checks and integration

Prove checker soundness/completeness for these exact predicates, and use
kernel-checked positive and negative witnesses. Include hidden out-of-range
indices in pointer/function/interface metadata, missing reserved entries,
dependency cycles, duplicate keys, missing entry, wrong arity/value kind,
and unsupported initialization/helper bodies. Prefer one actual native-
lowered Boolean fixture and retain its source/artifact provenance.

Run the capped core build, the ordinary CI gate, focused admission proofs,
and an external post-import axiom audit. There are no interpreter/frontend
changes or corpus baseline changes. Cached corpus evidence, if used by CI,
will be described as cached with its originating metadata. The independent
consumer gate remains outside the default dependency graph.

The root coordinator is promoting semantic bridges and an experimental
facade independently. This lane owns `GoLean/GoCore/Admission*.lean`, its
checks/evidence, and a dated handoff, without editing that facade or the
sealed A2 `HANDOFF.md`. Next extensions should be driven by the A2 artifact:
lexical/scoped typing, function/capture/call admission, explicit supported
initialization, then the separate preservation/refusal-freedom obligations.

## Delivered interface and evidence

`GoLean.GoCore.AdmissionIndices` traverses every current `Ty`, `Expr`,
`Assignee`, `SelectClauseHead`, `Stmt` and type-definition constructor with
no catch-all. `programIndices` adds all function signatures/bodies,
global annotations and method receivers. The traversal reports only index
occurrences; it is not a type checker.

`GoLean.GoCore.AdmissionPolicy` defines independent inductive `BoolExpr`,
`BoolStmt`/`BoolStmts`, and `InitialValueHasType` judgments. The executable
Boolean expression/statement checks are proved sound and complete for
those judgments. Future syntax is rejected by the policy unless explicitly
added; the index traversal must be updated to compile for new constructors.

`GoLean.GoCore.Admission` supplies the named error type, index/entry checks,
`checkBoolean_iff`, both implication theorems, and projections for index
bounds, all function bodies and absence of the package initializer. The
reserved-prefix clause also has a theorem identifying the exact leading
list with `TypeEnv.reserved`; it does not rely on opaque derived equality.

The core aggregate imports the checker. `scripts/ci` runs the separate
semantics-only proof gate, `scripts/check-admission --lean-only`; it builds
the test library, freshly elaborates all six complete admission/test/audit
modules, then runs an external post-import dependency sweep and three
compiled poison controls. The full `scripts/check-admission` additionally
builds the executable, freshly emits/lowers the native fixture, compares
the whole artifact and runs its one-case Go-vs-Lean manifest. It never adds
Iris or changes the default corpus baseline.

The delivered regression module contains 32 kernel-checked theorems. In
particular, `native_admission` witnesses the actual native-lowered function,
while `unbound_accepted` and `unbound_refuses` prove the deliberate limit:
one and the same admitted malformed artifact returns a named stuck refusal
from the executable driver. This is a guard against treating admission as
refusal freedom in future documentation or proofs.

See [validation evidence](evidence/2026-09-05_a3-admission/README.md) and the
[dated lane handoff](2026-09-05_a3-admission-handoff.md) for commands, cached
versus fresh scope, review, and integration obligations. This implementation
does not close Gate A3's larger typed-state/preservation work or all Gate A.
