# Recovery profile: independent static contract

[AGENT] 2026-09-06. Static implementation for independent review, implementing
the minimum in charter §3.2. This is a separate admission predicate; neither
O1 nor A3a changes. Static acceptance alone does not complete O2 runtime
preservation, terminal observation, or the Iris customer.

## Constructor and contract matrix

| Constructor / boundary | Candidate judgment |
| --- | --- |
| Variable | The **first actual lexical match** in a stack of scopes has the required type class. No union-context weakening from homogeneous O1. |
| Boolean expressions | Literals, not, short-circuit and/or; Boolean equality/inequality may also be checked directly at Boolean type. |
| Root reference | `ref x` requires a Boolean variable; reading a pointer-to-Boolean parameter preserves a live Boolean-root-reference refinement. No pointer arithmetic or non-root paths. |
| Root load/write | `deref e bool` and assignee `addr e` require that refined root-reference expression. |
| String expression | An arbitrary `GoString` literal. No character, UTF-8, newline, or control-byte restriction. Strings are transient payload inputs in this profile. |
| Interface payload | `toInterface target string e`, where target is the machine's empty interface and `e` is a string expression. Value class is nil or a boxed string. |
| `recoverCall` | Always a well-typed payload expression. Whether it returns nil and which suspended marker it updates remain dynamic semantic questions. |
| Nil | Untyped nil and nil annotated at an admitted empty-interface type; never a live root reference. |
| Nil comparison | `eqCmp`/`neqCmp` at an admitted empty-interface type, comparing a payload expression with nil in either orientation. General interface operations are excluded. |
| Assignment | Target and RHS value classes agree. Named targets resolve the first matching binding; address targets write Boolean roots. |
| Initialization / block declarations | Boolean and empty-interface cells default to false/nil. Root-reference locals/results are excluded because their Go zero value is nil, which cannot establish the live-root refinement. Initialization retains O1's actual statement-list placement and threaded declaration effects. |
| Function parameters | Boolean, empty-interface payload, or refined non-null Boolean-root-reference. A pointer parameter obtains its refinement from every checked call argument, not from Go pointer type alone. |
| Function results | Boolean or empty-interface payload; declaration keys are distinct from each other and parameters. Resultful bodies meet the declared return/terminating policy. |
| Direct call | Actual `FuncId` lookup, complete argument vector checked against parameters, result-target vector checked against results with exact arity. |
| Known closure | Only a literal `funcVal fid captures`; every capture is a Boolean-root-reference expression and matches the corresponding prefix of the actual callee signature. No inference from names such as `$lit`/`$cap`. |
| Closure call | The known closure's captures followed by explicit arguments match the entire signature. Ordinary result targets have exact result arity. |
| Defer | The same complete invocation check, including the capture prefix. Results may be discarded, matching deferred entry's deliberately empty result frame. Registration remains attached to an enclosing function frame at runtime. |
| Panic | Explicit string boxing as above, including repeated equal strings after recovery. There is no restriction on preceding recover/defer operations or re-panic control flow. |
| Return / control | Returns, nested sequences, blocks and branches; resultless fallthrough allowed. Resultful bodies end in return, explicit panic, or structurally terminating branches/lists. No loops or arbitrary control transfer. |
| Whole program | Existing index/reserved-prefix checks; no globals, package initializer, methods, variadics or wrappers. Check **all** bodies, signatures, captures, calls and deferred registrations, including uncalled functions and unreachable branches. |
| Entry | Existing Boolean external argument boundary, with selected entry signature checked; internal payload/root parameters are supplied only by checked calls. |
| Dependency graph | Direct call, known closure call and defer edges all contribute. Reject recursion using a total structural call-depth check bounded by the number of functions, independent of table order. This is a call-graph certificate, not execution fuel. |

Ordinary GoCore calls with zero targets and nonzero callee results are rejected
for arity; the actual ordinary frame otherwise refuses on exit. This differs
from defers, which deliberately discard results. The native frontend already
creates result targets for ordinary result-bearing calls. No new discard
convention will be invented in semantic typing.

The first candidate uses string literals as transient string expressions;
it does not introduce string variables, general interface equality, `panic(nil)`
or arbitrary recovered-payload rethrow. Re-panic with explicit string boxing
is supported without any flow restriction, including the equal-payload and
invalid-byte challenges. The current reviewer repair lane covers valid-UTF8
control-byte transport only; invalid UTF-8 and R-1 membership remain separate
parent-coordinated obligations. This
restriction is explicit for review against the approved minimum, rather than
an attempt to hide a renderer refusal.

The independent reviewer accepted this candidate minimum surface on
2026-09-06, including the explicit string-literal boxing restriction. That
is an early design assessment, not implementation acceptance.

## Independent judgments and executable checker

The independent review's RS-1 correction adds a redundant diagnostic layer:
total surface and declaration-placement checks run before scoped body typing.
`Statement.in_profile` and `Statement.placement` derive them from the unchanged
statement judgment, and `checkRecovery_iff` still targets the same independent
admission predicate. Valid Go `panic(true)` is now explicitly outside the
string-payload profile; an unbound assignment fails scoped typing instead.
These diagnostics classify this GoCore profile, not general source validity.

Use `Context := List (List (String × Ty))` with first-match lookup. A separate
inductive `TypeClass` classifies Boolean, live Boolean-root-reference,
empty-interface payload and transient string expression types. It delegates
empty-interface recognition to the existing semantic helper; it must not
reimplement native-name heuristics.

Independent inductive judgments cover expressions, assignable targets,
matching argument/parameter lists, matching result/target lists, known
closure capture prefixes, statements and effect-threaded statement lists.
The checker computes expression/target classes and recursively checks those
judgments. Every successful-check predicate has soundness and completeness
against its judgment; no judgment runs the interpreter or names an artifact.

Calls do not recursively type callee bodies during expression/statement
checking. Each call consults a signature, and whole-program admission checks
every function body separately. A distinct independent bounded call-tree
judgment/checker supplies the nonrecursive call-graph restriction, including
defer edges. This avoids tying completeness to a frontend function-table
ordering or to a user-chosen execution budget.

## Runtime and customer obligations retained

The mixed store must connect each actual first-resolved binding to the right
cell type and value class. Root-reference parameters are stored pointers to
live Boolean cells; payload cells hold nil or boxed strings. The required
runtime invariant additionally types saved argument/capture/result vectors,
ordinary versus deferred frames, external driver pins, deferred call lists,
panic chains and the continuation rebuilt by `recoverResult`.

Two handlers capturing one root share a semantic alias fact. Static typing
does not hand each handler independent exclusive Iris ownership of that root.
Recover outside the effective direct handler is admitted valid Go, and its
nil behavior must be tested independently. Uncaught panic is a semantic
terminal; renderer success and the existing Iris `NotStuck` policy remain
separate proof obligations.

## Required witnesses

The complete existing A2 artifact is an input, not a whitelist. Its normal,
recovered and uncaught entries must all be admitted. A new native fixture
will add Boolean input, an ordinary helper call, two handlers sharing a
result root whose LIFO order affects the result, normal/recovered paths and
recovery outside the effective direct-handler context. Additional kernel
families and negatives challenge wrong captures, aliasing, mixed-sort
shadowing, result targets, deferred registration, missing callees, recursive
edges and malformed uncalled functions. Arbitrary byte payloads and explicit
re-panic controls remain admitted even while terminal observer work is pending.

## Implemented API and boundaries

The modules `RecoveryTypingCore`, `RecoveryExpressions`, `RecoveryCalls`,
`RecoveryStatements`, `RecoveryGraph` and `RecoveryAdmission` separate lexical
contexts, sorted expressions/targets, call vectors, effect-threaded statements,
the dependency graph and whole-program admission. The namespace is
`GoLean.GoCore.RecoveryTyping`; the named predicate is `RecoveryAdmission` and
the total public checker is `checkRecovery`. Its `checkRecovery_iff`,
`checkRecovery_sound` and `checkRecovery_complete` relate the executable result
to independently defined propositions. All component Boolean checkers have
their own equivalence theorems too.

`Statement fs inSequence Γ s` and `Statements fs Γ ss` check actual statement
placement. A sequence exports its declarations; a block discards them.
Branches require zero exported declarations from each arm, with
`afterStmt_neutral` proving that this leaves the outer static context intact.
This count is a structural alternative to comparing contexts containing `Ty`
(which intentionally lacks an unrestricted `DecidableEq` instance).

`Calls` includes both branch arms and every nested direct-call, literal closure
call and deferred-call edge. `CallDepth` is an independent inductive finite
call-tree certificate; its total checker uses the function-table size as a
structural upper bound. `CallDepth.no_cycle` rules out arbitrary nonempty
cyclic paths, and `admitted_no_cycle` exports that consequence for every body.
The equivalence theorem is with this explicit bounded judgment; this increment
does not additionally prove the standalone graph-theoretic theorem that every
closed finite acyclic table admits a certificate at that bound. Table reversal
is exercised by a generic payload family, and the checker uses no table-order
or execution-budget premise.

`admitted_all_bodies` makes uncalled/unreachable checking visible in the API.
Call/capture checks deliberately do not assert exclusive ownership, semantic
equivalence to Go source, renderer success, or dynamic directness of recovery.
No checked runtime success is used to define typing. Source identifier and
function-body scoping correspondence remains a frontend obligation, as for O1;
duplicate storage keys, including repeated `_`, are diagnosed as outside this
GoCore profile rather than falsely called invalid Go source.

The second native fixture's `Shared` function accepts either Boolean input
and returns its negation: normal completion returns true and recovered
completion returns false. An initial draft had different control paths but
the same result on both inputs; self-review corrected this before acceptance
to satisfy the charter's explicit input-dependent result requirement.
Its later handler calls `indirectRecover` **before** its direct recovery, while
an active panic may still exist. If that indirect call incorrectly recovers,
the later direct call observes nil and the final Boolean result changes. Both
handlers capture the same result root; the first-registered handler calls a
Boolean helper to negate that root afterward, making recovered LIFO order
observable. `Outside` is a separate valid ordinary recovery call. Boolean
wrapper entries exist only because the current differential harness accepts
integer external arguments; kernel admission checks the actual `Shared` entry
uniformly over both Boolean inputs. Fresh whole-artifact checks compare every
field of both native artifacts, including the existing A2 artifact's uncalled
bodies and metadata.

Two valid native controls make these distinctions executable: `Reversed`
swaps the handler registration order, and `DirectRecoveryControl` replaces
the indirect helper call with a direct recovery expression in the handler.
On input true, each returns true while `Shared` returns false. These controls
are included in the same whole-program admission judgment. The dedicated
gate runs all five differential entries and separately pins their actual
native JSON results; passing Go-versus-Lean equality alone would not detect
an accidentally constant-result fixture.

The static gate rebuilds and freshly elaborates all ten new core/test/audit
modules, records source hashes, and audits every declaration in every imported
local module. Compiled private poisons in an intermediate call helper, the
public admission module and the audit itself, plus a trailing private `sorry`
in the challenges module, must all be rejected after a separate import.
Ordinary CI runs this static gate; the full dedicated gate also emits both
native fixtures and runs the second fixture's focused differential cases.

## Pinned design references and concrete lessons

These local sources informed the design; they are not imported proof
dependencies or substitutes for current GoCore runtime proofs. Source pins and
file hashes are retained in the static evidence's `references.tsv`.

| Source inspected | Concrete lesson used |
| --- | --- |
| Go repository `c19862e5f8415b4f24b189d065ed739517c548ba`, `doc/go_spec.html`, declarations/scope, terminating statements, defer and handling panics | Deferred callees/arguments are evaluated and saved at registration, execution is in reverse order, returned values are discarded, named results may be changed, and recovery directness is dynamic. Resultful return checking follows Go's terminating-statement forms. |
| refined-cerberus `c2ebeb7915da06461aa2bed8f898a7ca59c883b2`, `cerberus-heaplang/CerberusHeapLang/Rules.lean` | Prove atomic engine steps against actual liveness/type/bounds facts. Continuation-discarding control does not justify an unconditional sequencing/context law. A recovery rule must describe the continuation actually rebuilt by `recoverResult`. |
| RefinedC `25f706d417df2b18b23c5cbadde46468c1b1262c`, `theories/typing/programs.v` | Keep function signatures and call input/output vectors separate from logical pre/postconditions. Shared semantic aliases do not manufacture duplicated exclusive Iris ownership. |
| BRiCk `eee838e797ee636dd1f3de451ef7b2751018f313`, `rocq-skylabs-brick/theories/lang/cpp/logic/call.v` | Make arity and ordered argument setup explicit, and separate callee execution from caller result/lifetime handling. Here captures form the actual parameter prefix and deferred result handling is distinct. |
| Archived GoLean `wp-design` at `c3dc3986edbb3f1e2f0b33c7419ba16a041b6080`, `proofs/GoLeanProofs/SurfaceExit.lean` | Reuse the architectural separation of functional WP, frame-closed adequacy and explicit readout/choice bridges. Do not reuse its old `.exec ... .stop` setup as a fact about the current driver, whose entry is an empty function barrier. |
