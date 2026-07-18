# GoCore Semantics Cleanup Plan

This plan is the hard gate before expanding GoCore further toward proof
generation. The goal is a principled Go semantics, not a Gobra-compatible
interpreter. Differential coverage remains important, but passing coverage by
embedding Gobra artifacts into GoCore is not acceptable.

## Goal

Define a clean GoCore semantics that can support:

- executable Go-vs-Lean differential testing;
- a future relational small-step or big-step semantics;
- Goose/Perennial-style heap and field ownership predicates;
- eventually Iris-Lean weakest-precondition rules or a Lean-native VCG.

The executable interpreter is a test implementation of the semantics for
supported deterministic terminating programs. It is not the semantic authority.

## Non-Negotiable Boundary

GoCore may contain only Go semantic constructs.

Forbidden in clean GoCore:

- Gobra proof artifacts;
- Gobra verification annotations, predicates, permissions, invariants, and
  postconditions;
- Gobra name-mangling assumptions as semantic identity;
- frontend recovery heuristics as semantic facts;
- runtime meanings for spec-only constructs such as `old`;
- synthetic executable functions whose only purpose is to encode Gobra proof
  evidence.

These may exist in Gobra wire decoding or adapter code only when quarantined and
fail-closed. They must not become GoCore runtime semantics.

## What Is Sound Directionally

Preserve these parts. They are compatible with the long-term plan:

- heap-backed locals;
- path-like locations: `Loc.base`, `Loc.field`, `Loc.index`;
- struct, array, and slice values with addressable field/index operations;
- slice descriptors over backing storage;
- byte-backed strings;
- typed integer values, with the executable 64-bit `int`/`uint` policy treated
  as an executable parameter to later generalize;
- structured `panic`, `unsupported`, `stuck`, and `internal` errors;
- type-directed equality for currently supported non-interface values;
- state-threaded expression evaluation;
- two-phase assignment and call-result sequencing;
- same-source differential coverage.

These should be tightened with invariants, not discarded.

## Junk Inventory

### Must Remove Or Quarantine

1. `old` in runtime GoCore.
   `old(e)` is not Go. It must not execute as current-state identity. Runtime
   lowering should erase or reject it. A future proof/spec layer may introduce
   a separate pre-state expression form with explicit semantics.

2. `MethodSubtypeProof` executable wrappers.
   Gobra subtype proof members must not lower into callable GoCore functions.
   Interface dispatch must come from Go method-set semantics and stable method
   metadata, not proof evidence.

3. Raw string type identity in core semantics.
   Dynamic interface type tags and struct names are currently strings. This is
   tolerable for scaffolding, but the clean core needs stable `TypeId`,
   `FuncId`, and `MethodId` identities. Source or Gobra names may remain debug
   metadata.

4. Gobra type-definition recovery by adjacency.
   Reconstructing defined types from nearby `program.types` entries is adapter
   logic. It must not be relied on as semantic truth. The Gobra fork should
   export explicit type declarations, or lowering should fail closed.

5. Broad return postprocessing execution.
   Gobra return postprocessing may only lower if it matches an explicitly
   recognized Go reconstruction pattern. Arbitrary postprocessing statements
   must not execute as Go semantics.

6. Bodyless declarations as executable placeholders.
   Bodyless Gobra functions or methods should be adapter errors or metadata,
   except for explicitly modeled extern/builtin declarations.

### Needs Principled Invariants

These are not junk, but they need a clean formal account:

- lexical scoping and shadowing;
- heap cell typing and heap well-formedness;
- map representation, no-duplicate-key invariants, and key comparability;
- interface values, typed nils, method sets, and comparability panics;
- fuel-based execution versus divergence;
- deterministic executable append growth versus nondeterministic relational
  append growth;
- architecture-dependent integer widths.

## Clean-Core Contract

Introduce an explicit distinction between:

- `Wire`: frontend-specific decoded artifacts;
- `Lowering`: adapter code that either produces clean GoCore or fails closed;
- `GoCore`: frontend-independent syntax, values, state, and semantics;
- `Proof`: later spec/proof constructs that may mention pre-state facts,
  ownership, and verification conditions.

Clean GoCore programs must satisfy a well-formedness predicate:

- no frontend-only constructs;
- no spec-only constructs;
- all type, field, function, and method references resolve through stable IDs;
- heap locations are well-typed;
- locals are scoped and resolve to live locations;
- method metadata corresponds to Go method sets;
- interface boxes have valid dynamic type/value pairs;
- map cells satisfy key uniqueness and comparability invariants.

The executable interpreter should either require this predicate or check enough
of it at boundaries to fail closed.

## Work Plan

### Phase 0: Baseline And Classification

Before changing semantics, record a coverage baseline:

- run focused passing slices for currently supported core features;
- record known Gobra/frontend failures separately from GoCore failures;
- mark the cases whose current pass depends on semantic junk.

Do not delete cases. If cleanup causes a case to fail, keep it red and classify
the reason. A principled regression is acceptable when the previous pass relied
on forbidden semantics.

### Phase 1: Remove Runtime Spec Constructs

- Remove `old` from executable GoCore semantics.
- Make Gobra `Old` lowering fail closed or erase only when it appears in a
  verified-to-be-non-runtime assertion/spec field.
- Add a lowering test that prevents `Old` from entering runtime GoCore.

Coverage policy:

- runtime Go cases should not need `old`;
- any current pass relying on runtime `old` should regress until reconstructed
  through a clean mechanism.

### Phase 2: Stable Identities

Introduce semantic identifiers:

- `TypeId`;
- `FuncId`;
- `MethodId`;
- possibly `FieldId` or field references scoped by `TypeId`.

Move source names, Gobra names, and pretty names into metadata. Core equality,
interface dynamic tags, dispatch, and struct checks should use IDs.

Coverage policy:

- existing differential cases should continue to pass after lowering maps Gobra
  names to stable IDs;
- if a Gobra name collision was hidden by current heuristics, fail closed.

### Phase 3: Typed Environments And Heap Invariants

Make the state model proof-ready:

- represent lexical local scopes explicitly;
- restore block scopes at block exit;
- distinguish binding a fresh local from assigning an existing one;
- add heap typing or allocation metadata;
- define heap/local well-formedness predicates;
- make store normalization depend on declared type, not only old stored value.

Coverage policy:

- shadowing and block-scope differential cases should be added or promoted;
- existing pointer/struct/slice aliasing cases should remain passing unless
  they depended on invalid local reuse.

### Phase 4: Clean Interface Semantics

Replace the current interface scaffolding with Go semantics:

- interface boxes contain a stable dynamic `TypeId` and value;
- typed nils are represented explicitly enough to distinguish nil interface
  from typed nil dynamic values;
- method sets are computed or represented as Go method-set metadata;
- interface-to-interface assertions check method-set satisfaction;
- concrete type assertions compare stable dynamic type identity;
- interface equality implements Go comparability and panic behavior;
- interface method dispatch uses method-set lookup, not Gobra proof wrappers.

Remove `MethodSubtypeProof` wrapper lowering. If Gobra exports useful
information, convert it into adapter metadata only after validating it against
clean method-set rules.

Coverage policy:

- keep the current interface differential cases;
- accept temporary regressions for cases that only passed because of Gobra proof
  wrappers;
- restore them through clean method-set dispatch;
- prioritize typed nil and interface equality cases once the representation is
  principled.

### Phase 5: Gobra Adapter Cleanup

Harden `GobraToIR` so it is plainly an adapter:

- Gobra proof members never become executable GoCore functions;
- type definitions must be explicit or lowering fails closed;
- return postprocessing is accepted only for recognized Go patterns;
- bodyless members are metadata, extern declarations, or errors;
- unsupported wire nodes produce adapter failures, not inert GoCore nodes hidden
  in dead code;
- all Gobra name stripping is replaced by an explicit symbol map.

Coverage policy:

- frontend/export failures remain red and separate from semantic failures;
- no hand-maintained Gobra-friendly source variants;
- if Gobra cannot export clean enough data for a feature, prefer improving the
  Gobra JSON export or waiting for a native frontend over polluting GoCore.

### Phase 6: Relational Semantics Skeleton

Add the first proof-facing relation before concurrency or more interface work:

- start with scalar expressions, heap locals, struct fields, arrays, direct
  calls, assignment sequencing, and simple control flow;
- reuse GoCore syntax, values, locations, errors, and outcomes;
- define panics as program behavior;
- define `stuck` as malformed GoCore or unsupported model state;
- state correspondence theorems between the executable interpreter and the
  relation for small deterministic terminating programs.

This relation can be partial at first. The point is to force new features to
have an obvious rule shape before the interpreter grows further.

Coverage policy:

- no need to prove the whole corpus immediately;
- add tiny relation/interpreter correspondence tests or theorems for each
  cleaned core feature;
- differential tests remain the practical conformance gate.

## Regression Policy

Regressions are allowed only when they remove forbidden semantics or expose an
invalid adapter assumption.

Allowed regressions:

- a case changes from pass to `frontend-export`/`json-check` because Gobra no
  longer supplies clean semantic data;
- a case changes from pass to `unsupported` because the old pass depended on
  `old`, proof wrappers, or type-recovery heuristics;
- an interface case regresses while replacing proof-wrapper dispatch with real
  method-set dispatch.

Not allowed:

- deleting cases;
- changing canonical Go source to appease Gobra;
- accepting Lean `unsupported`, `stuck`, or `error` as conformance success;
- adding GoCore constructs solely to mirror Gobra artifacts;
- silently approximating Go behavior to keep a case green.

Every regression should be recorded with:

- case id;
- previous stage/result;
- new stage/result;
- semantic reason;
- intended clean fix.

## Acceptance Criteria

The cleanup is complete enough to resume feature expansion when:

- runtime GoCore has no executable `old`;
- Gobra proof members do not produce executable functions;
- dynamic type and method dispatch use stable semantic IDs;
- block scoping is explicit;
- heap well-formedness is specified and enforced or checked at key boundaries;
- Gobra type recovery is explicit or fail-closed;
- current core pointer/struct/array/slice coverage is preserved or has
  documented principled regressions;
- current interface passes are restored through clean method-set semantics or
  tracked as intentional regressions;
- a minimal relational semantics skeleton exists for the cleaned deterministic
  subset.

## Recommended Immediate Order

1. Remove runtime `old`.
2. Introduce stable IDs and symbol tables.
3. Replace `MethodSubtypeProof` wrappers with clean method metadata or fail
   closed.
4. Add lexical scopes and heap typing invariants.
5. Rebuild interface assertions/dispatch over stable method sets.
6. Add the first relational semantics skeleton.

Do not expand into concurrency, defer/panic/recover, type switches, or broader
interface equality until these cleanup steps are underway.
