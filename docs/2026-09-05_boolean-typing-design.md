# O1 static foundation: scoped Boolean GoCore admission

**Status:** bounded static increment implemented, independently reviewed,
and validated on 2026-09-06 in the `typed-boolean` lane. This note makes no
setup, preservation, progress, readout, or full O1 completion claim.
[Sealed validation](evidence/2026-09-06_boolean-typing/README.md) records the
tested source tree and distinguishes fresh from cached evidence. The approved authority is the
[typed-consumer sprint charter](2026-09-05_typed-consumer-sprint-charter.md).

## Judgment and executable boundary

`GoLean.GoCore.BooleanTyping.TypedBooleanAdmission` is the conjunction of
the unchanged A3a `BooleanAdmission` and `ProgramTyped`. Every function in
the program is checked, including functions unreachable from the selected
entry. The selected entry still uses A3a's actual function lookup, Boolean
argument-value check, and arity check. No checker invokes the interpreter.

`ExprTyped`, `Statement`, `StmtsTyped`, `Returns`, and `ReturnsList` are
inductive judgments independent of their executable Boolean checkers.
`FunctionTyped` and `ProgramTyped` assemble those judgments with explicit
signature conditions. The theorems `checkExpr_iff`, `checkStmt_iff`,
`checkStmts_iff`, `checkReturns_iff`, and `checkTypedBoolean_iff` prove
soundness and completeness for exactly these definitions.

The checker is opt-in. Acceptance does not yet imply a successful driver
setup or execution, and no existing A3a theorem is relabeled. The old
unbound-read program still passes A3a and fails the new checker.

## Scope is defined by GoCore constructors

The context is a list of scopes, each a list of Boolean binding keys.
`Bound` searches all scopes; `Fresh` checks only the innermost scope.
`declare` mirrors `LocalEnv.declare`. All declared Boolean cells are
available immediately after zero initialization; there is no
definite-assignment condition. A use before declaration is rejected because
the binding is absent, not because its value has not been assigned.

| Constructor or boundary | Judgment and scope effect |
|---|---|
| Boolean variable/literal, `not`, `and`, `or` | Variables must be bound. Both operands are checked even when short circuiting may skip one at runtime. |
| Assignment to a variable | Target and every variable read in the RHS must be bound. Assignment changes no bindings. |
| `initialization p` | Boolean type and a fresh innermost key; permitted only as a statement-list element. The tail sees the new binding. |
| `seqn ss` | Checks and exports `afterStmts Γ ss`. It does **not** push or discard a scope. |
| `block ps ss` | Distinct Boolean preallocated declarations introduce a new scope; the body may add locals; exit restores the outer context. |
| `ifThenElse` | Boolean condition, both arms checked, and neither arm exports new bindings into the surrounding list. Nested blocks may declare and shadow. |
| `returnStmt` | Reads the function's pinned result cells at runtime; no assignment-before-return requirement. Static return obligations are checked separately. |
| Function signature | All parameters/results are Boolean and their combined GoCore binding keys are distinct. |
| Function body | Checked in the parameter/result context; result-bearing bodies must end in a structurally terminating statement. Resultless bodies may fall through. |

The sequence rule follows `Machine.seqCont`, which splices a nested list
into a same-environment governing sequence. In particular, a declaration
inside a nested `seqn` is visible to the following outer-list statement,
and redeclaring its key there is rejected. This was caught during the
independent design review before implementation. `stmts_append_iff` and
`afterStmts_append` expose the exact facts needed by the splicing proof.

`Statement inSequence Γ s` carries a placement flag. Initialization has
only a `true` constructor. `StmtTyped` abbreviates `Statement false`, used
at function entry and for direct branch arms. This reflects the machine's
requirement that initialization run immediately under a `.seq` continuation
whose saved environment equals the current environment. The runtime
invariant must establish that equality; the static flag alone does not.

Bare declarations as direct branch arms and branch sequences that export
bindings are explicitly outside this profile, even when a hand-built
configuration happens to execute them. Native Go branch blocks fit the
profile. This structural restriction prevents path-dependent binding joins;
it is not a statement that all such GoCore terms are runtime errors.

`Stmt.initialization` has no initializer expression: it allocates the zero
value. A subsequent assignment reads the then-current context. Preserving
Go source initializer scope, including `x := x` under legal shadowing, is
the frontend's translation obligation. The typing judgment does not infer
source declaration boundaries or recognize frontend temporary names.

Similarly, a GoCore `block` always introduces the scope its constructor
and machine rule specify, even when it appears directly as a function
body. Go source parameters/results share the function-body lexical scope;
`go/types` and the frontend must preserve that rule. The checker is a
GoCore scoped-typing boundary, not a Go source parser/type checker. It does
not attempt to reconstruct omitted source scopes.

Repeated blank or unnamed parameter keys deserve explicit treatment:
the current emitter can retain repeated `_` or empty keys, while result
keys are separately generated. The distinct-key profile refuses those
artifacts. Such a refusal is **out of profile**, not evidence that the
original Go source is invalid. No special meaning for `_`, empty strings,
or generated-name spelling has been added to GoCore. All required positive
witnesses use distinct semantic storage keys.

## Return policy and specification argument

The pinned source is `deps/go/doc/go_spec.html` at `go1.26.5`, commit
`c19862e5f8415b4f24b189d065ed739517c548ba`; see
[spec-sources.md](spec-sources.md). Relevant anchors:

- `spec#Declarations_and_scope`: lexical scope, same-block duplicate
  declarations, blank identifiers, and declaration initializer scope.
- `spec#Terminating_statements`: return, a block ending in a terminating
  statement, and an if whose two arms terminate.
- `spec#Return_statements`: named results and their initial zero values;
  the optional compiler restriction on returning while result names are
  shadowed is not a new GoCore runtime rule.
- `spec#The_zero_value`: Boolean locals and result cells start at false.

`ReturnsList` requires the last statement to terminate. It does not accept
an earlier return followed by a nonterminating tail, use constant-condition
evaluation to ignore an arm, or assume that every function must assign its
named results. Because the Boolean profile excludes loops, panic, and goto,
the accepted terminating constructors are exactly return, sequence, block,
and a two-arm terminating branch. Explicit return expressions already
lower to assignments to result cells followed by `returnStmt`; assignment
typing checks their Boolean values.

## Diagnostics and tests

The diagnostic order is A3a boundary, signature keys, placement policy,
scoped body, then return policy, applied in function-table order. This
separates unsupported types/syntax and declaration placement from missing
bindings and duplicate locals. The signature diagnostic specifically names
the distinct-key profile restriction. Missing-return refusal is the
declared result-bearing function policy. Diagnostics name the affected
function; they currently group unbound reads/writes and same-scope local
duplicates within the scoped-body category.

`Tests/BooleanTyping.lean` includes generic function families plus kernel
regressions for unbound reads/writes, use before declaration, local and
signature duplicates, escaped locals, legal shadowing, nested sequence
visibility, zero values, unsupported declaration placement and branch
effects, both-arm returns, invalid fallthrough, argument/result type
boundaries, and malformed unreachable functions.

`Tests/boolean-typing-fixture/main.go` is independently written native Go.
The entire lowered artifact, including metadata, is checked against
`Tests/BooleanTypingFixture.lean`. It contains an argument-dependent
function, legal shadowing, a two-arm result function, and zero-valued
locals/results. The shadow witness initializes outer `x` to true, evaluates
inner `x := !x`, and combines the inner and outer values afterward. Correct
initializer scope yields false; erroneously reading a freshly zeroed inner
cell yields true. The freshly checked lowering hoists the initializer value
before introducing the inner binding, and the checker treats its temporary
as an ordinary Boolean binding. The normal gate differentially runs the three no-argument
entries. The argument-dependent entry has kernel admission witnesses for
both Boolean inputs; the existing differential CLI takes integer entry
arguments, so these are not described as Boolean-argument differential runs.

Reproduce with `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash
scripts/check-boolean-typing`. `--lean-only` builds the typing library/tests
and freshly elaborates their sources; CI invokes that mode. A post-import
module-origin audit checks all declarations in the complete imported local
closure, including private or unused declarations, with only the classical
trio permitted. Three mutation controls compile an unused private assumption
in the core module, one in the audit module, and a trailing unproved test
theorem; each must then be rejected by the importing audit. The complete
gate additionally checks fresh native emission/lowering and the focused
differential manifest. Runtime contracts and auditing their expanded closure
are separate sprint work and remain required before O1 completion.

## Handoff to runtime proofs

The intended semantic bridge is a coverage relation from `Bound Γ x` to an
actual local-environment lookup yielding a valid Boolean root cell, plus
heap and pinned-result invariants. It need not equate the ordering of
static scope lists with the runtime allocator's prepending order.

Relevant exported APIs are `initialContext`, `bound_initialContext`,
`bound_declare`, `bound_push`, `afterStmt`, `afterStmts`, `stmts_cons_iff`,
`initialization_iff`, `stmts_initialization_iff`, `stmts_append_iff`, and
`Statement.inSequence`. Scope effects for sequence execution must flow into
continuation typing; block exit must restore the saved outer environment.
Initialization requires the genuine same-environment sequence premise.
No theorem in this slice supplies those runtime obligations by assumption.
