# Boolean runtime contract: proposed statements and invariant obligations

[AGENT], 2026-09-05. **Candidate design under independent statement review**,
not a report that O1 is complete. This refines the approved
[sprint charter](2026-09-05_typed-consumer-sprint-charter.md) without reducing
its profiles or outcomes. Concrete proved helper declarations currently live
in `GoLean/GoCore/BooleanStore.lean`; all larger statements below are targets.

## Scope and existing judgments

The static lane supplies `BooleanTyping.Context := List (List String)`,
`ExprTyped Γ e`, `Statement inSequence Γ s`, and `StmtsTyped Γ ss`, with
`afterStmt`/`afterStmts` recording introduced storage bindings. `seqn`
threads declarations into the following statements; `.block` owns a fresh
scope and restores its outer scope on exit. An initialization can only be a
sequence member. Both branch arms must preserve their incoming scope; native
Go branch blocks meet this restriction. This is a GoCore judgment, not a
proof of equivalence with the Go source type checker.

`TypedBooleanAdmission` strengthens the existing A3a judgment with these
checks and function-result return obligations. A3a stays unchanged. Repeated
storage keys (including repeated native `_` parameter keys) are an explicit
profile restriction, not a claim that all such Go source programs are invalid.
No identifier spelling has special runtime typing meaning.

## Store and environment predicates

`BooleanRuntime.BoolRoot s l` means there exist `a : Nat` and `b : Bool`
such that `l = Loc.base ⟨a⟩` and the actual heap at `a` is
`HeapCell.value Ty.bool (GoValue.bool b)`. `BoolHeap s` says this of every
allocated cell. `EnvRoots s env` says every successful actual lookup yields
such a root. `NamesPresent ids env` states the existence of lookup locations
for those names. These inspect storage, not evaluator success.

The static/runtime link `EnvCovers Γ env s` must combine actual bindings for
every statically bound name with typed roots. The source typing context and
runtime environment need not list bindings in the same order: `declare`
prepends names, whereas source parameter lists retain declaration order.
Bounds for all saved scopes, including hidden bindings, must additionally
be sufficient to derive `ConfigWf`; lookup coverage alone does not imply
that hidden locations are in range.

Allocation lemmas must establish fresh initialized roots, preserved old
roots, heap typing, bound names, exact allocation count, and unchanged
immutable context. Stores must retain the declared type and preserve all
other typed roots. Readout must prove `loadMany` succeeds and returns exactly
as many Boolean values as the pinned result locations. A successful call to
`normalizeValueForTy` is not an input-typing assumption: its Boolean fallback
currently accepts arbitrary values, so actual Boolean arguments are required.

## Entry/setup target

For arbitrary program `p`, entry `name`, Boolean arguments `args`, fuel and
choices, derive from typed admission that `runProgramSetupM` succeeds with:

- the function returned by the driver's actual lookup;
- its actual body and initialized parameter/result environment;
- an all-Boolean heap, valid environments and pinned Boolean result roots;
- the original program context, empty globals, and no package initializer;
- exactly `args.size + f.results.size` allocated cells;
- the original choice stream (this setup uses no choices).

The initial configuration is exactly
`.exec f.body env (.frame [] [] [] [] .stop)`. This driver's barrier has
**no results in its continuation**; its real result locations are returned
separately by setup. Carry those locations as an external invariant parameter
through every step. Ordinary result-returning call frames later in O2 have
a different invariant.

No setup-success premise may escape. `StateWf` of the seeded state and the
reserved-prefix Boolean guard must be derived from admission. There is no
initialization fuel requirement for this no-globals/no-initializer profile;
subject execution has its own explicit fuel/termination obligation.

## Runtime invariant target

`Inv p resultLocs s c` is a structural typing judgment over the real state
and control. It includes unchanged context, `BoolHeap s`, all pinned roots,
actual environment coverage, and enough bounds to derive `MachineWf s c`.
Its control cases cover at least:

| Actual control family | Required static/runtime obligation |
|---|---|
| Statement sequence cursor | Current context and actual environment cover the remaining list; declaration effects are threaded through the static list judgment. |
| Executing a sequence member | The executing head and its saved tail are typed jointly. Future declared names need not exist before the head allocates them. |
| Initialization | Immediate continuation is exactly `.seq rest env k` with the same actual `env`; the tail is typed under the declared context. |
| Nested `seqn` | Account for both `seqCont` branches. Equal saved/current environments splice `ss ++ rest`, retaining declarations. A different environment wraps a distinct sequence. |
| Block | Default initialization of block declarations, pushed scope, and restoration through the saved continuation. |
| Boolean expression and strict `not` | Incoming/outgoing value sort is Boolean; pending operands and saved environment are typed. |
| Short-circuit and branch frames | Boolean condition/value, correctly typed pending expression or branches, and appropriate continuation. |
| Assignment target evaluation | A generated `.ref` expression returns a Boolean root **address**, even though admitted source expressions are Boolean. |
| Assignment delivery | The actual `tgtOpK`, `rhsK`, and `storeK` singleton spines carry matching Boolean-root targets and Boolean values; target/value arity is exact. |
| Return signal | Only sequence frames and the correct entry barrier can receive this signal; expression glue and `.stop` cannot. |
| Normal completion | `.next .stop`, with the external result roots still typed and available for readout. |

Transient expression sorts therefore include Boolean values and addresses of
Boolean roots. The admission syntax need not admit arbitrary user-written
address expressions to type runtime-generated assignment targets.

The invariant must not be defined as “reachable and safe,” a successful
bounded run, or existence of a future trace. No constructor may simply assume
the safety conclusion or closure under every future step. Reachability can
be a theorem about the structural invariant once initialization and one-step
preservation are proved.

## Main proof obligations (schematic names, not existing exports)

1. `setup_typed`: typed admission implies the actual setup equality and the
   initial invariant above, universally in setup fuel/choices.
2. `inv_step`: `Inv p rs s c → Step c s c' s' → Inv p rs s' c'`. This covers
   **all** relational successors, not one chosen oracle run.
3. `inv_machineWf`: derive the existing `MachineWf` from the new invariant.
4. `inv_progress`: `Inv p rs s c → c = .next .stop ∨ ∃ c' s', Step c s c' s'`.
   O1 has no panic-producing operation; this formula is specific to O1.
5. `run_no_refusal`: derive the hypotheses of the existing
   `execStmtLoop_ok_or_fuelOut` theorem from the invariant. Its reachable
   progress hypothesis must not become a new admission assumption. Use
   `step_complete_any_wf` to connect relational progress to executable
   success for every choice stream, and `stepFn_sound` plus preservation
   to account for the actual chosen successor.
6. `run_typed_readout`: a successful bounded run from the admitted setup has
   a successful `loadMany` at the declared Boolean result arity. Keep the
   choice-sensitive trace bridge and final output contract explicit.

No generic termination theorem is required. A consumer proving its result
may discharge a separate bounded termination witness, but must use shared
WP rules for the functional argument rather than replace them with a trace.

## O2 extension and newly exposed obligations

Extend heap/value/control typing to the charter's calls, captured Boolean
roots, explicit string/interface payloads, defer registration and unwind.
Distinguish the driver barrier, ordinary frames that transfer results, and
deferred frames that discard results. Recovery updates a continuation marker,
not just a value: preservation must retain the modified panic-chain state.

O2 progress must classify both normal completion and legitimate Go abort,
and its observation theorem must establish that the actual abort renderer
produces that terminal observation. `abort? ≠ none` alone is insufficient.
The existing Iris adapter's `NotStuck` policy remains scoped to the normal/
recovered customers.

The independent reviewer has produced kernel and Go probes exposing Unicode,
newline and invalid-UTF8 payload refusals and equal-payload recovered/repanic
boxing ambiguity. These are **not discharged** by the new type checker.
UTF8/newline rendering repairs should be evaluated under the existing
first-panic-line policy, preserving suffix placement. Raw invalid bytes and
boxing identity may need critical representation/policy decisions. Do not
add an ASCII-only or no-repanic restriction to the approved minimum profile
to conceal them. Record the precise scope and alternatives in the sprint
decision ledger, freeze only work depending on an unresolved decision, and
continue O1 and independent B7 preparation.
