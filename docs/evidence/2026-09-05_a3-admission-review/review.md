# Independent adversarial review: first A3 admission slice

[AGENT] `bug103_integration`, 2026-09-05, independently reviewing the
`a3_admission` implementation. Verdict: **PASS for the explicitly bounded
slice; no blocking or unresolved introduced defect found.** This is not
approval of complete Go typing, refusal freedom, or closure of all Gate A3.

The reviewed branch is `gate-a3-admission`, based on `700128f3`, with the
uncommitted implementation identified by `source-bindings.json` (123 exact
files, including untracked A3 source). Aggregate:
`aa9ffd2a22f079e16aa4f208a030b16942c3f09ca52bd67d6836665ab194331d`.
The review precedes integration with the newly landed BUG-103/interface
branches. Their combined tree needs its own integration gates.

## Contract and architecture

- `checkBoolean_iff`, soundness and completeness characterize exactly
  `IndexStructure ∧ Entry ∧ BooleanSyntax`. None uses an interpreter run,
  normalization success, or source/frontend string-layout policy as its
  definition. The small `InitialValueHasType` judgment genuinely checks
  Boolean argument payloads; it is not misrepresented as a typed store.
- The reserved prefix is checked structurally and related to the exact
  reserved entries by `reservedPrefix_exact`. Type dependency ordering and
  all referenced index bounds are separate checks. Unique semantic keys
  are checked without interpreting their grammar.
- I inspected every current Ty/Expr/Stmt constructor and the surrounding
  Param, FieldDef, MethodSig, MethodInfo, GlobalDef and Program structures.
  The index traversal covers all current `Ty.defined` positions, including
  indirections that `Ty.deps` deliberately omits, optional annotations,
  nested select heads/defaults, result signatures and metadata receivers.
  No constructor catch-all silently drops future expression/statement cases.
  TypeId/FuncId-name validity is explicitly outside this exact property.
- Entry uses the driver's actual `findFunctionIn?`, arity and Boolean
  parameters/values. The syntax policy checks every function, including
  unreachable helpers, and excludes the actual driver-recognized init ID,
  globals, method declarations, calls/defer/go, variadic and wrapper forms.
- `methodSets` and `typeDisplays` remain explicitly unchecked. Their keys
  are not constrained to the frontend's emitted `struct{}` spelling. The
  fixture retains that native record intact; Boolean operations do not
  inspect it. A draft error message overstated 'method metadata' checking;
  it now accurately says 'method declarations'. No required fix remains.
- The core imports no Iris/frontend component. The semantics-owned proof
  and audit check is included in ordinary CI; the additional native
  artifact/differential check remains an explicit full admission gate.

## Independent verification

`review_gate.py` invokes the final, unchanged preflight/elaboration/audit/
artifact functions from `tools/admission-check.py`. It redirects only the
scratch allocator and differential artifact directory into the review's
unique scratch; it does not weaken the checks. Final run exited **0**:

- All six core/test/audit sources freshly elaborated from source.
- **32 test theorem declarations**, including real native positive
  admission, malformed-index/type/entry/policy negatives, and explicit
  accepted limitation witnesses.
- Post-import audit: **14 required theorem exports, 375 constants**,
  transitive dependencies restricted to the classical trio.
- Three independent copied-cache mutations compiled successfully and then
  failed for their named forbidden dependency: trailing private audit axiom,
  private core Admission axiom, and trailing private test proof using
  `sorry`. An import/compilation failure cannot count as poison detection.
- Fresh Go emission and NativeToIR lowering matched the complete proof
  artifact. Native wire SHA256:
  `b72ed5518a3b3928455da2f0839c30b29c15f01d85a8922ba6d785225df259af`.
- Fresh native differential: **1/1 PASS**, `admission/constant`, go1.26.5,
  including the harness's observation-invariance streams. This is one
  scoped witness, not a full corpus run or a compiler-correctness theorem.

`Probes.lean` supplies **16 additional compiled boundary probes**, all PASS:
intertwined map/function/pointer type references; interface results;
unreachable function result types; method receivers and globals; select
send/receive-map-target/default paths; optional type-assert/length/nil
annotations; unsupported dead helpers; init exclusion; malformed initial
values; and intentional acceptance of unobserved metadata/unbound variables.
It also accepts a generated **3,000-function** input and rejects an
unsupported helper appended after those functions. This demonstrates
executable practicality on that input, not an asymptotic/resource guarantee;
the sub-millisecond printed timing is not a precise performance claim.

An accepted unbound-variable program really returns a named stuck refusal,
both in the author's kernel theorem and my independent executable probe.
That counterexample is a positive assurance feature: consumers cannot
mistake this syntax/index boundary for `ProgramWellTyped` or progress.

All Lean calls were capped at 16G with three threads. Fresh elaboration used
no `-o`; poisoned imports used independent copied compiled package trees.
The differential's standard incremental core build was coordinated with
the owner. The initial reviewer probe harness lacked a Decidable instance
for Except equality; its preserved failure log is a harness error, fixed
with explicit result-constructor comparison, not a project finding.

## Usefulness and remaining obligations

This is a credible first admission slice: the reusable all-syntax index
scanner closes a real distinction from resolution dependency order, entry
values have an exact typed boundary, and policy soundness is tied to an
independent inductive syntax judgment and actual native artifact.

The next useful increment is scoped variable/result typing and a driver
setup theorem for this small fragment, followed by the A2-required captures,
calls, initialization and recover support. Merely adding accepted syntax
constructors would not close the consumer's missing admission guarantee.
The current whole-program Boolean policy intentionally rejects the A2
recovery program. Definite return, lexical/name validity, full Go typing,
typed-state preservation and refusal freedom remain owed and are clearly
stated as such in the design.

The reviewer did not rerun the 3,593-case corpus or the ordinary CI suite;
the owner ran CI with explicitly cached corpus/negative provenance. No
clean network bootstrap, full upstream rebuild, or later combined-tree
claim is made. Curated evidence here excludes binary/cached mutation trees;
it retains the exact mutation sources, compilation/rejection logs, native
wire, source binding, probe source and raw fresh result/meta/oracle records.
