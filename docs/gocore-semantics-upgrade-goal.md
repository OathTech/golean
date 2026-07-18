# GoCore Semantics Upgrade Goal

This document is the authoritative operating guide for the GoCore semantics
upgrade. An agent should be able to read this file with no conversation context
and know what to do, what not to do, how to validate progress, and when to stop
for user input.

The job is to replace ad hoc executable scaffolding with a principled GoCore
semantics that remains differentially testable against real Go and is shaped for
future Goose/Perennial-style verification.

## Start Here If You Have No Other Context

Your task is to clean and upgrade GoCore semantics. GoCore is the semantic
center. Gobra is only a temporary frontend and source of typed export data.

The most important rule:

**Never make GoCore semantics depend on Gobra verification artifacts, Gobra
proof evidence, Gobra name mangling, frontend recovery heuristics, or spec-only
constructs such as `old`.**

Every implementation step must improve one of these:

- semantic cleanliness: GoCore contains fewer frontend/proof artifacts;
- semantic precision: GoCore models Go behavior more faithfully;
- proof readiness: the syntax, state, and rules are easier to relate to a future
  relational semantics and typed heap ownership model;
- conformance accounting: differential coverage results more accurately
  distinguish frontend gaps, unsupported semantics, panics, stuck states, and
  true mismatches.

Passing tests by embedding junk is failure. Exposing a red case because the old
pass depended on junk is acceptable progress when the regression is documented.

## Resume, Branch, And Worktree Discipline

Implementation work for this goal should live on a dedicated semantics-upgrade
branch. A typical branch name is:

```sh
gocore-semantics-upgrade
```

This is not an instruction to create a fresh branch every time an agent resumes.
At the start of any session, first determine whether the task is already in
progress.

Always check:

```sh
git status --short
git branch --show-current
git log --oneline -5
```

Persistent handoffs for this goal live in
`docs/gocore-semantics-upgrade-handoff.md`. Then inspect that handoff, relevant
docs, recent commits, and the current diff to identify the current phase.

Treat a branch as an existing semantics-upgrade branch only if its name, latest
commits, persistent handoff, or current diff explicitly references this goal. If
the active branch is already the semantics-upgrade branch, or satisfies this
evidence test, continue there. Do not create a new branch just because this
document mentions the recommended branch name.

If on `main`, `master`, or another ambiguous branch with semantics-upgrade
changes or an ambiguous dirty state, stop and ask before creating, switching,
committing, or continuing.

If the working tree contains changes you did not make, do not revert them. Work
with them if they are relevant. Ignore them if they are unrelated. If they make
the next step ambiguous, stop and ask the user whether to branch, stash, commit,
or continue on top.

If no dedicated semantics branch exists yet, and code changes for this goal are
about to begin, stop and ask the user whether to create or switch to one.
Documentation-only edits may be made without a new branch when explicitly
requested.

If the task is half complete, prefer resuming the existing branch and phase over
restarting Phase 0. Re-run only the baseline checks needed to understand current
state or validate the next slice.

Do not use destructive git commands such as `git reset --hard` or
`git checkout -- <file>` unless the user explicitly requests them.

## Canonical References

Read these before starting implementation:

- `AGENTS.md`: project operating context.
- `docs/semantics-cleanup-plan.md`: cleanup inventory and phase order.
- `docs/semantics.md`: current GoCore semantic design.
- `docs/iris-lean-review.md`: Iris-Lean compatibility notes.
- `docs/slice-model.md`: slice descriptor model.
- `docs/differential-testing.md`: Go-vs-Lean validation loop.
- `docs/coverage-ledger.md`: supported and missing behavior accounting.

Use these dependency sources as design references, not as code to copy blindly:

- `deps/perennial/new/golang/defn/prelang.v`: structural Go type universe.
- `deps/perennial/new/golang/defn/postlang.v`: semantic functions and tables.
- `deps/perennial/new/golang/defn/interface.v`: interface semantics.
- `deps/perennial/new/golang/defn/slice.v`: slice/index/append shape.
- `deps/perennial/new/golang/theory/mem.v`: typed load/store/alloc proof shape.
- `deps/perennial/new/golang/theory/array.v`: per-index array ownership.
- `deps/goose/types.go`: generated field and method metadata.
- `deps/goose/proofgen/tmpl/types.tmpl`: generated typed points-to predicates.

The Goose/Perennial lesson is architectural:

- clean frontend translation;
- explicit semantic type/function/method tables;
- typed allocation/load/store/field/index primitives;
- interface behavior from type sets and method sets;
- proof automation layered above the semantic core.

Do not port GooseLang or Rocq syntax into GoCore.

## Semantic Authority

There are two intended semantic views:

- executable interpreter: used for differential testing on deterministic
  terminating supported programs;
- future relational semantics: the proof-facing authority and eventual
  Iris-Lean or Lean-native VCG bridge.

The executable interpreter is not allowed to hide semantic choices inside
opaque recursion. Every new feature should have an obvious future relational rule
shape. If a feature cannot be described cleanly as a rule over GoCore syntax,
values, locations, state, and outcomes, stop and redesign before implementing.

Panics are Go program behavior. `unsupported` means a known Go feature is not
modeled yet. `stuck` means malformed GoCore, violated invariants, or a model
gap. Do not treat `unsupported`, `stuck`, or internal errors as successful
conformance.

## In Scope

This goal may change:

- `GoLean/GoCore/Syntax.lean`
- `GoLean/GoCore/Value.lean`
- `GoLean/GoCore/State.lean`
- `GoLean/GoCore/Ops.lean`
- `GoLean/GoCore/Eval.lean`
- `GoLean/GobraJson.lean`, only as wire decoding for clean exported data
- `GoLean/GobraToIR.lean`, only as adapter/lowering into clean GoCore
- `GoLean/CLI.lean`, only for reporting, validation, or schema plumbing needed
  by the semantics upgrade
- `scripts/*`, only for focused validation/reporting support
- `docs/*`, when documenting semantic policy, regressions, or handoff state
- `Corpus/coverage/*`, only to add or classify focused cases needed to guard
  the upgraded semantics

The main semantic work is:

1. Remove runtime spec constructs from GoCore.
2. Introduce stable semantic identities and symbol tables.
3. Replace string-based type/interface/method identity with semantic IDs.
4. Remove executable Gobra proof wrappers.
5. Add typed local/heap invariants and make stores depend on declared type.
6. Rebuild interface conversion, assertion, dispatch, and equality from Go
   method-set/type-set semantics.
7. Keep slice descriptors over backing storage and document executable append
   policy versus future relational nondeterminism.
8. Add the first minimal relational semantics skeleton once the cleaned core is
   stable enough.

## Out Of Scope

Do not spend this goal on:

- building a native Go frontend;
- making Gobra a trusted semantic authority;
- importing Gobra verification semantics into GoCore;
- adding Iris-Lean as a project dependency;
- porting GooseLang or Perennial directly;
- broad concurrency semantics;
- channels, goroutines, select, data races, or happens-before rules;
- `defer`, `panic/recover`, type switches, reflection, unsafe, cgo, or standard
  library models unless a tiny change is strictly required by a cleanup step;
- new large corpus buildout unrelated to guarding the semantics cleanup;
- optimizing performance before the semantic shape is clean.

If an out-of-scope feature blocks a focused differential case, classify the case
as unsupported or frontend-blocked. Do not implement the feature opportunistically.

The `panic` and `recover` builtins, `defer` interaction, and full panic
unwinding are out of scope. Semantic panic outcomes required by modeled
operations remain in scope. Examples include nil dereference, failed single-value
type assertions, slice bounds panics, and incomparable interface equality.

## Forbidden Behaviors

Never do any of the following:

- keep `old(e)` as executable current-state identity;
- lower Gobra `MethodSubtypeProof` or other proof members into callable GoCore
  functions;
- use Gobra-generated proxy names as semantic type, function, or method identity;
- infer type definitions by adjacency or other brittle Gobra export layout
  assumptions;
- execute arbitrary Gobra return postprocessing as Go semantics;
- accept bodyless declarations as executable placeholders except for explicit
  modeled externs or builtins;
- add GoCore syntax solely to mirror Gobra wire artifacts;
- weaken, delete, skip, or fork valid coverage cases to keep results green;
- mark `unsupported`, `stuck`, frontend failure, or Lean internal error as a
  conformance pass;
- silently approximate Go behavior when Go requires a panic, compile error, or
  implementation-defined/nondeterministic policy;
- hide regressions by changing ordinary Go source;
- mix unrelated refactors into a semantics cleanup slice.

If a current passing case depends on forbidden behavior, it may regress. Record
the regression and the intended clean fix.

## Design Requirements

### Stable Identity

GoCore must distinguish semantic identity from display names.

Introduce or preserve a path toward:

- `TypeId`
- `FuncId`
- `MethodId`
- field identity scoped by the declaring type
- debug/source names as metadata only

Core equality, dynamic interface tags, struct checks, function lookup, method
lookup, and type assertions must eventually use semantic IDs. Strings may remain
for human-readable diagnostics and transitional lowering metadata, but not as
the semantic authority.

### Type Universe And Tables

The clean core should have explicit semantic tables for:

- defined type declarations;
- aliases and underlying types;
- struct fields;
- function signatures and bodies;
- method declarations;
- method sets;
- interface type sets;
- field references;
- index references.

This is the Lean GoCore analogue of Perennial's `GoSemanticsFunctions`. The
tables may start small and executable, but they must be frontend independent.

### Typed State

The runtime state must move toward:

- lexical local scopes;
- local bindings that record declared type;
- heap allocations that record declared type or enough metadata to enforce it;
- store normalization based on declared type, not previous value shape alone;
- well-formedness predicates for locals, heap, type tables, and interface boxes.

The interpreter may check invariants dynamically at first. The proof-facing
relation should later assume or carry a well-formedness predicate explicitly.

### Interface Semantics

Interfaces must follow Go semantics:

- nil interface is distinct from an interface containing a typed nil value;
- non-nil interface contains a dynamic semantic type and a value;
- concrete type assertion compares dynamic type identity;
- interface type assertion checks membership in the target interface type set;
- comma-ok assertions return the target zero value and `false` on failure;
- single-result assertions panic on failure;
- equality of interface values checks dynamic type identity, comparability, and
  dynamic value equality, with Go panics for incomparable dynamic values;
- method dispatch uses method-set lookup and dynamic receiver value;
- method sets account for pointer/value receiver rules and embedded methods.

Do not derive interface implementation from Gobra proof wrappers.

### Differential Testing

Every semantic change should be guarded by focused Go-vs-Lean differential
tests when the frontend can express the feature.

Use focused slices during iteration:

```sh
scripts/coverage run <case-id>
scripts/coverage run --prefix <area>/
scripts/coverage run --tag <tag>
scripts/coverage run --last-failed
scripts/diff-one <case-id>
```

Use `scripts/gobra-smoke` only as a frontend/Lean smoke check. It is not a
Go-vs-Lean semantic equivalence oracle.

## Implementation Phases

Work in small, reviewable slices. Do not begin the next phase if the current
phase has unclassified regressions.

### Phase 0: Baseline, Resume, And Branch Check

Required actions:

- determine whether this is a fresh start or a resume of in-progress work;
- identify the active branch and whether it is already the semantics-upgrade
  branch;
- read `docs/gocore-semantics-upgrade-handoff.md`, if it exists, or infer the
  current phase from commits, status, and docs;
- record `git status --short`;
- record the baseline commit, date, exact commands, case IDs, and results used
  as this upgrade's comparison point;
- if starting fresh, run or inspect the current focused passing slices for core
  pointer, struct, array, slice, map, and interface cases;
- if resuming, run only the focused baseline needed for the next slice unless the
  previous handoff says the baseline is stale;
- identify which current green cases depend on known junk;
- write down expected principled regressions before making them happen.

Suggested validation:

```sh
lake exe golean
scripts/coverage run --prefix pointers/
scripts/coverage run --prefix structs/
scripts/coverage run --prefix arrays/
scripts/coverage run --prefix slices/
scripts/coverage run --prefix maps/
scripts/coverage run --prefix interfaces/
git diff --check
```

If full prefix runs are too expensive, use narrower tags or exact cases and say
so in the handoff.

Later regressions are measured against the recorded Phase 0 baseline, not
against whatever happens to be green when an agent resumes.

### Phase 1: Remove Runtime Spec Constructs

Required outcome:

- runtime GoCore has no executable `old`;
- Gobra `Old` in runtime positions fails closed or is erased only from
  verification-only fields before GoCore lowering;
- tests or checks prevent `old` from silently entering executable GoCore.

Allowed regression:

- a case that passed only because `old(e)` evaluated as `e` may become
  frontend/lowering unsupported.

Stop before improvising if:

- Gobra export does not distinguish runtime code from spec-only code clearly
  enough to reject `old` safely.

### Phase 2: Stable Semantic Identities

Required outcome:

- introduce semantic IDs or an equivalent explicit identity layer;
- move source/Gobra/display names into metadata;
- all touched type, function, method, struct, and interface identity checks use
  semantic IDs or the new identity layer as authority;
- any remaining raw-string identity sites are enumerated, marked transitional,
  and shown not to affect runtime equality, lookup, dispatch, or interface tags;
- lowering builds an explicit symbol map.

Allowed regression:

- name-collision or malformed-export cases that previously passed by accident
  may fail closed.

Stop before improvising if:

- there is a serious design fork between a compact ID table and structural
  identity that affects all later phases;
- existing serialized artifacts or CLI output require a user-visible schema
  choice.

### Phase 3: Gobra Adapter Cleanup

Required outcome:

- Gobra proof members do not produce executable GoCore functions;
- `MethodSubtypeProof` is decoded only as wire data or ignored/validated as
  metadata;
- bodyless methods/functions fail closed unless explicitly modeled;
- type-definition recovery is explicit or fails closed;
- return postprocessing lowers only recognized Go reconstruction patterns.

Allowed regression:

- interface cases that passed only through proof-wrapper dispatch may fail until
  Phase 5 restores clean method-set dispatch.

Stop before improvising if:

- clean lowering requires additional Gobra JSON export fields not currently
  available. Prefer changing the Gobra JSON export over adding GoCore junk, but
  ask before making broad frontend changes.

### Phase 4: Typed Locals, Heap, And Well-Formedness

Required outcome:

- locals have explicit lexical scoping;
- local declarations and assignment are distinguished;
- heap cells are associated with declared type or equivalent allocation
  metadata;
- stores are normalized and checked against declared type;
- well-formedness predicates or dynamic boundary checks are documented and used;
- path-like `Loc.field` and `Loc.index` remain the memory-addressing model.

Allowed regression:

- shadowing cases that previously reused locals incorrectly may change result
  and should be fixed to match Go;
- malformed GoCore fixtures may become `stuck`.

Stop before improvising if:

- preserving current behavior requires violating lexical scoping or declared heap
  typing;
- a large state representation rewrite is needed and cannot be made in a
  reviewable slice.

### Phase 5: Clean Interface Semantics

Required outcome:

- interface boxes contain stable dynamic type identity and value;
- typed nil behavior is represented correctly;
- interface-to-interface and concrete assertions use type-set rules;
- single-result assertions panic and comma-ok assertions return zero/false;
- method dispatch uses method sets and dynamic receiver values;
- non-nil interface equality implements Go comparability and panic behavior;
- current interface differential cases are restored through clean semantics or
  documented as intentional regressions.

Allowed regression:

- cases relying on Gobra wrapper functions may remain red until method-set
  metadata is available.

Stop before improvising if:

- method-set computation cannot be represented from current exported metadata;
- embedded method promotion or pointer receiver behavior needs a design decision;
- a proposed shortcut would make interface implementation depend on Gobra proof
  evidence.

### Phase 6: Minimal Relational Semantics Skeleton

Required outcome:

- add a small proof-facing relation over existing clean GoCore syntax, values,
  locations, state, and outcomes;
- cover scalar expressions, typed heap load/store, locals, structs, arrays,
  direct calls, simple sequencing, and simple control flow;
- define panics as behavior and `stuck` as malformed state or unsupported model;
- state the intended interpreter/relation correspondence theorem shape, even if
  only a tiny theorem or executable check is completed initially.

Do not block cleanup on full proofs. The skeleton exists to force rule shape and
prevent the interpreter from becoming the only semantic definition.

Stop before improvising if:

- adding the relation would require bringing Iris-Lean into the build;
- the clean core is still changing too quickly to state stable rules.

## Required Validation Gates

Before every pause, handoff, or commit:

```sh
lake exe golean
git diff --check
```

Before claiming a semantic slice is done, also run focused differential tests
for the touched area:

```sh
scripts/coverage run --prefix <area>/
```

or, for narrow changes:

```sh
scripts/diff-one <case-id> [<case-id> ...]
```

For interface work, include focused interface cases such as:

```sh
scripts/coverage run --prefix interfaces/
```

If a command is too slow or blocked by sandbox/tooling, run the narrowest useful
replacement and report exactly what was and was not validated.

For every coverage or diff command, record the exact command, case count, pass
count, mismatch count, unsupported count, stuck count, frontend/export failure
count, Lean/internal error count, and any newly red case IDs. A zero exit code is
not enough for handoff-quality validation.

Do not claim Go semantic equivalence from:

- `scripts/gobra-smoke`;
- successful Gobra export alone;
- successful Lean build alone;
- a run that accepts `unsupported`, `stuck`, or frontend failure as success.

## Regression Accounting

Every regression caused by cleanup must be recorded in the handoff or a tracking
document with:

- case id or focused slice;
- previous stage/result if known;
- new stage/result;
- forbidden behavior or invalid assumption removed;
- intended clean fix;
- whether user input is needed.

Allowed regression reasons:

- removed runtime `old`;
- removed Gobra proof-wrapper execution;
- replaced Gobra name identity with semantic IDs;
- rejected heuristic type recovery;
- enforced lexical scoping;
- enforced heap typing;
- exposed missing method-set/type-set metadata;
- exposed a real unsupported Go feature.

Not allowed regression reasons:

- changed ordinary Go source to appease Gobra;
- changed the oracle to accept non-equivalence;
- skipped tests;
- converted semantic mismatch into unreported success;
- broadened `unsupported` to avoid implementing a required in-scope behavior.

## When To Stop And Ask For User Input

Stop immediately and ask the user before proceeding if any of these occur:

- code changes are about to begin, no active semantics-upgrade branch is
  identifiable, and the current branch/worktree state makes the branch decision
  ambiguous;
- a clean implementation requires broad Gobra frontend/export changes rather
  than small JSON metadata additions;
- a phase requires choosing between two incompatible principled semantic designs;
- preserving differential coverage conflicts with the no-junk rule;
- a needed Go behavior is implementation-defined, nondeterministic, or
  version-specific and the current harness cannot express it cleanly;
- the only apparent way to make progress is to add Gobra artifacts to GoCore;
- a destructive git operation seems necessary;
- a full validation gate cannot run and no focused substitute gives useful
  confidence;
- a change would require adding Iris-Lean or another substantial dependency;
- deleting, weakening, skipping, or rewriting valid corpus cases seems tempting.

When asking, present:

- the exact blocker;
- the options;
- the recommended option;
- the expected impact on coverage and future proof readiness.

## When To Pause For User Decision

Pause and request a user decision when one of these is true:

- Phase 1 through Phase 3 are complete, and further cleanup requires Gobra JSON
  export fields that are not available yet;
- stable IDs and adapter cleanup are complete, but interface method-set metadata
  cannot be obtained without a frontend/export decision;
- typed heap/local invariants are complete enough to expose that the next step
  is a relational-semantics design choice rather than implementation;
- the remaining red cases are all classified as frontend/export blocked or
  unsupported features outside this goal;
- the next meaningful work is adding Iris-Lean, a native frontend, concurrency,
  or another out-of-scope subsystem.

This is not final completion. Do not report the semantics upgrade complete under
this section. Report the state as blocked or deferred, list unmet final
completion criteria, and request the specific user decision needed to continue.

Do not pause for user decision merely because the work is large, tests are red,
or the current implementation is partial. Pause only when the next decision is
genuinely architectural or crosses the explicit scope boundary.

## Final Completion Criteria

The semantics upgrade is complete enough to resume ordinary feature expansion
when all of these are true:

- runtime GoCore contains no executable `old`;
- Gobra proof members do not produce executable GoCore functions;
- semantic identity for types, functions, methods, and interface dynamic tags is
  not raw Gobra/source strings;
- Gobra lowering either produces clean GoCore or fails closed;
- lexical local scoping is explicit;
- heap cells are typed or checked through an explicit invariant;
- store/load/default/zero behavior is type-directed;
- structs, arrays, slices, maps, and interfaces have documented well-formedness
  requirements;
- interface assertions, conversions, dispatch, typed nils, and equality follow
  Go semantics for the in-scope subset;
- unsupported gaps at final completion are outside this goal, blocked by a
  recorded frontend/export decision, or explicitly deferred by the user;
- each remaining unsupported gap names the missing semantic rule or missing
  exported datum;
- in-scope behavior is not left red merely because it is difficult;
- baseline pointer/struct/array/slice/map coverage is preserved or has
  documented principled regressions;
- baseline interface coverage is restored through clean method-set semantics or
  has documented principled regressions that the user explicitly accepts;
- a minimal relational semantics skeleton exists or the user has explicitly
  deferred it after reviewing the cleaned core;
- validation commands and focused differential slices have been run and reported;
- no known passing case depends on forbidden behavior.

Completion does not require full Goose/Perennial parity, Iris integration, a
native frontend, or full Go coverage. It requires a clean semantic foundation
that future work can build on without carrying Gobra or proof-artifact debt.

## Iteration Procedure

Use this loop for each implementation slice:

1. Pick the smallest coherent phase item.
2. Search current code and docs for the relevant constructs.
3. Identify current tests or add focused differential cases if needed.
4. Make the semantic change in GoCore or the lowering boundary.
5. Reject frontend artifacts at the boundary. Do not quarantine them inside
   executable GoCore.
6. Run `lake exe golean`.
7. Run focused `scripts/coverage run ...` or `scripts/diff-one ...`.
8. Run `git diff --check`.
9. Record regressions and classify them.
10. Stop if the next step crosses a phase boundary with unresolved regressions.

If a slice cannot be summarized in a few paragraphs, it is too large. Validate,
write a handoff, and split the work.

## Persistent Handoff

Persistent handoffs for this goal belong in:

```text
docs/gocore-semantics-upgrade-handoff.md
```

If that file does not exist, create it before the first nontrivial pause in the
semantics-upgrade branch. Chat-only handoffs are not sufficient for resume. Each
handoff must append to or explicitly supersede the previous handoff and identify
the next incomplete phase item.

## Handoff Summary Format

When pausing, report:

```text
Branch:
- <branch name>

Baseline:
- commit/date: <baseline commit and date>
- commands/cases: <exact baseline commands or case IDs>
- result summary: <pass/fail/stage counts>

Changed:
- <files or areas changed>

Phase:
- <phase number and name>

Validation:
- lake exe golean: <result>
- scripts/coverage run ... or scripts/diff-one ...:
  <exact command, case count, pass count, mismatch count, unsupported count,
  stuck count, frontend/export failure count, Lean/internal error count, newly
  red case IDs, or not run with reason>
- git diff --check: <result>

Regressions:
- <case id/stage/reason/intended clean fix, or none>

Known blockers:
- <blocker or none>

Next recommended step:
- <one concrete step>

Commit status:
- <uncommitted | committed <hash>>
```

Do not leave future agents to infer whether red results are expected, whether a
dirty tree is intentional, or whether validation was broad or focused.

## Current Near-Term Target

Follow the cleanup path already identified. If resuming in the middle, continue
at the earliest incomplete item with unclassified regressions resolved:

1. Confirm or resume the active semantics-upgrade branch.
2. Record or refresh the focused baseline needed for the next slice.
3. Remove runtime `old`.
4. Add stable semantic IDs and symbol maps.
5. Stop Gobra proof members from becoming executable functions.
6. Add typed locals/heap invariants.
7. Rebuild interface behavior over method sets and type sets.
8. Add the first relational semantics skeleton.

Do not expand into broader Go coverage until these foundations are in place or
the user explicitly redirects the goal.
