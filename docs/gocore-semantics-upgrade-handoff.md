# GoCore Semantics Upgrade Handoff

This file is the persistent handoff log for the semantics upgrade defined in
`docs/gocore-semantics-upgrade-goal.md`. Newest entry first. Each entry either
appends to or explicitly supersedes the previous one.

## 2026-07-17: Phase 4 slice 1 — explicit lexical scoping for locals

Branch:
- `gocore-semantics-upgrade`

Changed:
- `GoLean/GoCore/State.lean`: `LocalEnv` is now a scope stack
  (`List Scope`, innermost first). Lookup walks inner to outer.
  `LocalEnv.declare` always binds fresh in the innermost scope;
  `pushScope`/`popScope` manage block extent. `ExecState.bindLocal`
  (which silently reused an existing location on redeclaration) is
  replaced by `ExecState.declareLocal`, which always allocates a fresh
  location — shadowing now gets its own cell.
- `GoLean/GoCore/Eval.lean`: `.block` pushes a scope on entry and pops it
  on every exit path (normal, returned, broke, continued). Declaration
  sites (params, results, decls, initialization) use `declareLocal`;
  assignment still resolves through `lookupLoc` and cannot create
  bindings.

Why no behavior change is expected on the current corpus: Gobra
alpha-renames local ids, so GoCore never previously saw two bindings with
the same name — lexical scoping was effectively outsourced to frontend
renaming, which is exactly the kind of frontend-recovery reliance this
upgrade removes. A future native frontend can now emit source names
directly and shadowing is handled by GoCore itself.

Remaining Phase 4 items (next slices):
- heap cells recording declared type or allocation metadata; stores
  checked against it (slice 4b);
- documented well-formedness checks for locals/heap/type tables (4c).

Validation:
- `lake build` (library and tests): pass.
- `lake exe gobra-eval-tests`: 46 ok. `lake exe gobra-json-tests`: pass.
- `scripts/coverage run <136 cached-export case ids>`: 136 cases, 123 pass,
  13 fail; failing set identical to the post-Phase-3 set (which shares its
  case ids with the Phase 0 baseline).
- `git diff --check`: clean.

Regressions:
- none.

Commit status:
- committed (this entry accompanies the slice commit).

## 2026-07-17: Phase 3 slice 1 — MethodSubtypeProof decoded as wire metadata

Branch:
- `gocore-semantics-upgrade`

Changed:
- `GoLean/GobraJson.lean`: added `MethodSubtypeProofMember` (strict decode
  of source, sub/super proxies, superT, receiver, args, results, optional
  body) and the `AutoImplProofAnnotation` source annotation; both added to
  `knownTagNames`. Documented as wire data only.
- `GoLean/GobraToIR.lean`: `buildSymbolMap` and `lowerProgram` explicitly
  skip proof members — they never become executable functions, symbol map
  entries, or dispatch metadata.

Result: `methods/interface-dispatch` progressed from a json-check decode
rejection to a classified semantics gap: Lean now reports
`unsupported: default value for unknown defined type
methodDispatchInterface`. The adjacency-based type recovery reconstructs
only struct definitions, so defined interface types have no `TypeEnv`
entry (their zero value is a nil interface). Extending adjacency recovery
would deepen junk item 4; the clean fix is explicit type-declaration
export from the Gobra fork, which is a frontend decision (see pause note
below).

Observed while probing: interface type export names use a second mangling
pattern (`Y$fd0d1673_4b5075e4_`) that `stripGobraTypeSuffix` does not
canonicalize. Consistent within a program, so dispatch is unaffected, but
Phase 5 interface work should canonicalize it when interface type
identity becomes load-bearing.

Phase:
- Phase 3 partially complete: proof members are wire-only (the core Phase 3
  requirement) and bodyless members already fail closed at execution.
  Remaining Phase 3 items — explicit or fail-closed type recovery, and
  restricting return postprocessing to recognized reconstruction patterns —
  are blocked on or entangled with the frontend export decision.

Validation:
- `lake build`, unit suites, and the 136-case slice: recorded in the
  accompanying commit message; the expected delta is
  `methods/interface-dispatch` moving stage from json-check to
  lean-observation while remaining red.

Pause note (per "When To Pause For User Decision"):
- Phases 1 and 2 are complete; the core of Phase 3 is complete. Further
  interface progress needs Gobra JSON export enrichment (explicit type
  declarations, and later method-set metadata), a change in the Scala fork.
  Given the etcd-raft north star already commits to a native Go frontend,
  the user should decide: enrich the Gobra fork, start the native frontend
  early, or proceed with Phase 4 (typed locals/heap, frontend-independent)
  while deferring the frontend decision.

Commit status:
- committed (this entry accompanies the slice commit).

## 2026-07-17: Phase 2 slice 3 — receiver-scoped method canonical keys

Branch:
- `gocore-semantics-upgrade`

Changed:
- `GoLean/GobraToIR.lean`: method entries in the symbol map now get
  canonical keys `<receiver type canonical name>.<method name>` (via
  `receiverTypeKey?` over defined, pointer-to-defined, and interface
  receiver types), replacing the transitional Gobra `uniqueName` keys. Go
  forbids declaring the same method name on both receiver forms of a type,
  so the key is unique across value and pointer receivers. Methods with
  receiver shapes outside those three fail closed at map construction.

With this slice, Phase 2's required outcomes are met:
- semantic identities exist (`FuncId`, `TypeId`) and are the authority for
  function lookup, calls, dispatch metadata, struct/field identity, type
  environment keys, and interface dynamic-tag derivation;
- Gobra-mangled names are interpreted only inside the symbol map and
  `typeIdOfGobraName`, both fail-closed on collision;
- lowering builds an explicit symbol map;
- remaining raw-string sites, enumerated as transitional: interface dynamic
  tags are derived strings (`id.key`, `*id.key`, primitive kind names) and
  the `empty_interface` sentinel — both scheduled for the Phase 5 interface
  rebuild; `MethodInfo.name` holds the method source name pending real
  method-set semantics; local variable names remain strings by design
  (lexical scoping is Phase 4).

Phase:
- Phase 2 complete pending validation below. Next: Phase 3, Gobra adapter
  cleanup — decode `MethodSubtypeProof` as ignorable wire metadata instead
  of a json-check rejection (this blocks `methods/interface-dispatch` at
  decode today), and tighten bodyless/type-recovery fail-closed behavior.

Validation:
- `lake build` (library and test executables): pass.
- `lake exe gobra-eval-tests`: 46 ok. `lake exe gobra-json-tests`: pass.
- `scripts/coverage run <136 cached-export case ids>`: 136 cases, 123 pass,
  13 fail; failing case-id set identical to the Phase 0 baseline.
- `git diff --check`: clean.

Regressions:
- none.

Commit status:
- committed (this entry accompanies the slice commit).

## 2026-07-17: Phase 2 slice 2 — TypeId for defined and interface types

Branch:
- `gocore-semantics-upgrade`

Changed:
- `GoLean/GoCore/Value.lean`: added `TypeId` (newtype over the canonical
  source-level type name); `Loc.field` and `GoValue.struct` carry `TypeId`.
- `GoLean/GoCore/Syntax.lean`: `Ty.defined`/`Ty.interface` carry `TypeId`;
  `Expr.fieldGet`/`Expr.fieldAddr` carry `TypeId`; `Program.typeDefs` keyed
  by `TypeId`.
- `GoLean/GoCore/State.lean`: `TypeEnv` keyed by `TypeId`.
- `GoLean/GoCore/Ops.lean`, `GoLean/GoCore/Eval.lean`: identity comparisons
  now compare `TypeId`s; diagnostics print `.key`.
- `GoLean/GobraToIR.lean`: added `stripGobraTypeSuffix` and
  `typeIdOfGobraName` as the only `TypeId` construction point from Gobra
  names; `lowerProgram` fails closed when two distinct declared Gobra type
  names collide on one canonical name (`checkTypeIdCollisions`).
- `GoLean/CLI.lean`: struct and field-address observations print the
  canonical `.key`, so observed type names are source-level (matching the
  Go oracle's `typ.Name()`), not Gobra-mangled.
- `Tests/GobraEval.lean`: fixtures updated mechanically.

Design note: `TypeId` construction from Gobra names uses a deterministic
strip validated for collisions at program level, rather than a threaded
lookup map, because `lowerTy` is called from pure expression-lowering
context. When Phase 3 makes type declarations explicit wire data, the
constructor can switch to a declaration-backed map without touching GoCore.
Interface dynamic tags remain derived strings (`id.key`, `*id.key`,
primitive names) pending the Phase 5 interface rebuild; they now carry
canonical names instead of mangled ones.

Phase:
- Phase 2 in progress (slice 2 of ~3). Next: slice 2c, method canonical
  keys from receiver `TypeId` plus method name, replacing the transitional
  Gobra `uniqueName` keys.

Validation:
- `lake build` (library and test executables): pass.
- `lake exe gobra-eval-tests`: 46 ok. `lake exe gobra-json-tests`: pass.
- `scripts/coverage run <136 cached-export case ids>`: 136 cases, 123 pass,
  13 fail; failing case-id set identical to the Phase 0 baseline. Interface
  diagnostics now show canonical names (`*nilCompareA`,
  `assertInterfaceReader`) instead of Gobra-mangled ones.
- `git diff --check`: clean.

Regressions:
- none.

Commit status:
- committed (this entry accompanies the slice commit).

## 2026-07-17: Phase 2 slice 1 — FuncId and the lowering symbol map

Branch:
- `gocore-semantics-upgrade`

Changed:
- `GoLean/GoCore/Syntax.lean`: added `FuncId` (newtype over a canonical key,
  documented as symbol-map-only construction); `Func.name` became
  `Func.id : FuncId`; `Stmt.call` takes `FuncId`; `findFunctionIn?` looks up
  by `FuncId`; `MethodInfo.uniqueName` became `MethodInfo.funcId : FuncId`.
- `GoLean/GoCore/Eval.lean`: call execution, dynamic dispatch, and messages
  use `FuncId`; `findFunction?`/`runNamedFunction` remain string-keyed as the
  documented user-facing lookup by canonical function name.
- `GoLean/GoCore/Ops.lean`: `methodInfoByUnique?` became
  `methodInfoByFuncId?`.
- `GoLean/GobraToIR.lean`: added `SymbolMap` and `buildSymbolMap`, built in
  one pass over program members before lowering, failing closed on duplicate
  export names and canonical-name collisions. `stripGobraFunctionSuffix` is
  now interpreted only inside `buildSymbolMap`. Call lowering resolves
  callees through the map; calls to undeclared functions/methods lower to
  `.unsupported` instead of guessing via suffix stripping. Member lowering
  and `lowerMethodInfo` resolve their own IDs through the map.
- `GoLean/GobraEval.lean`: `runFunctionMember` builds a singleton symbol map.
- `Tests/GobraEval.lean`: `GoCore.Func` fixtures use `id := ⟨...⟩`; `.call`
  fixtures wrap callee keys.

Transitional raw-string identity sites (enumerated per the phase gate):
- method canonical keys are still the Gobra `uniqueName` (until `TypeId`
  lands and methods can be keyed by receiver type and method name);
- `Ty.defined`/`Ty.interface` names, `GoValue.struct`/`GoValue.interface`
  tags, and `dynamicTypeName?` pointer-tag strings (`*name`) are untouched
  in this slice — they are slice 2b.

Phase:
- Phase 2 in progress (slice 1 of ~3). Next: slice 2b, `TypeId` for defined
  and interface types.

Validation:
- `lake build` (including test executables): pass.
- `lake exe gobra-eval-tests`: 46 ok, 0 fail.
- `lake exe gobra-json-tests`: pass.
- `scripts/coverage run <136 cached-export case ids>`: 136 cases, 123 pass,
  13 fail (3 differential, 5 lean-observation, 4 json-check,
  1 artifact-check); failing case-id set identical to the Phase 0 baseline.
- `git diff --check`: clean.

Regressions:
- none.

Known blockers:
- none.

Next recommended step:
- Slice 2b: `TypeId` for `Ty.defined`/`Ty.interface`, `TypeEnv`, struct and
  interface value tags, with mangling stripped to source display names via
  the symbol map, so interface dynamic tags and struct observations match
  the Go oracle's source-level names.

Commit status:
- committed (this entry accompanies the slice commit).

## 2026-07-17: Phase 1 complete — runtime `old` removed

Branch:
- `gocore-semantics-upgrade`

Changed:
- `GoLean/GoCore/Syntax.lean`: removed `Expr.old`.
- `GoLean/GoCore/Eval.lean`: removed the `old`-as-identity evaluation case.
- `GoLean/GobraToIR.lean`: runtime `Old` now lowers to
  `.unsupported "old expression in runtime code"`; `lowerExprTy?` returns
  `none` for `Old`; `lowerAddressOfExpr` no longer looks through `Old` (falls
  into the fail-closed catch-all). Spec-field erasure (assertions, pres/posts,
  postprocessing asserts) is unchanged; `Old` remains decodable wire data.
- `Tests/GobraEval.lean`: added `runtime old expression fails closed`, a wire
  document whose body assigns `old(x + y)`; expects error status
  `unsupported`.

Phase:
- Phase 1 complete. Next: Phase 2, stable semantic identities (design note
  below).

Validation:
- `lake build`: pass (38 jobs).
- `lake exe gobra-eval-tests`: pass, including the new fail-closed test.
- `lake exe gobra-json-tests`: pass.
- `scripts/coverage run <136 cached-export case ids>` (same slice as Phase 0
  baseline): 136 cases, 123 pass, 13 fail. Failing stages: 3 differential,
  5 lean-observation, 4 json-check, 1 artifact-check. The failing case-id set
  is identical to the Phase 0 baseline; zero new red cases.
- `git diff --check`: clean.

Regressions:
- none. No active case depended on runtime `old`.

Known blockers:
- none.

Next recommended step:
- Phase 2 slice 1: add the identity newtypes and the lowering symbol map
  (collect pass over Gobra members/types, strip mangling once, fail closed on
  collision), then thread `TypeId`/`FuncId` through GoCore in follow-up
  slices.

Commit status:
- committed (this entry accompanies the Phase 1 commit).

## Phase 2 design note (recorded 2026-07-17)

Chosen identity layer: newtype identities (`TypeId`, `FuncId`, `MethodId`)
wrapping canonical source-level names, produced only by an explicit symbol map
that lowering builds in a first pass over Gobra members and types. The map
strips Gobra `_<hash>_T` / `_<hash>_F` mangling once, at the boundary, and
fails closed on collisions. GoCore equality, dispatch, interface dynamic tags,
and lookup consume the newtypes; raw Gobra names never cross the boundary.
This is the "equivalent explicit identity layer" the goal doc allows; the
compact numeric ID table remains a contained, mechanical follow-up because
every identity creation point goes through the symbol map. Transitional
raw-string sites (to enumerate as they are touched): pointer dynamic tags
derived as `*name` strings in `Ops.dynamicTypeName?`, and the
`empty_interface` sentinel interface name.

Evidence this matters: Gobra-mangled names currently leak into interface
dynamic tags (`*nilCompareA_4b5075e4_T` in baseline failures) and would leak
into struct observations if any active case observed a whole struct value
(the Go oracle prints source names such as `copiedStruct`).

## Phase 6 design note (recorded 2026-07-17)

The relational semantics skeleton should be small-step, not big-step.
Concurrency is an explicit eventual goal via Iris-Lean, and Iris-Lean's
`Iris.ProgramLogic.Language`/`PrimStep` interface requires a primitive step
relation of shape `Expr × State → Obs → Expr × State × List Expr → Prop`,
where the `List Expr` component is forked threads; goroutine spawn maps onto
it directly. A big-step relation would have to be rebuilt for that interface.
The deterministic executable interpreter remains the differential test
implementation; the small-step relation is the proof-facing authority. See
`docs/iris-lean-review.md` for the interface details and the Lean toolchain
version gap that gates direct Iris-Lean dependency integration.

## 2026-07-17: Phase 0 baseline recorded

Branch:
- `gocore-semantics-upgrade`, created from `phase-2-gocore-memory` at
  `b51d9ba` after committing the previously uncommitted interface subset
  (`e0a51ce`) and the planning docs (`b51d9ba`).

Baseline:
- commit/date: `e0a51ce` (interface subset included), 2026-07-17.
- commands/cases:
  - `lake build`: pass.
  - `lake exe golean`: pass (usage output, exit 0).
  - `scripts/coverage-negative`: 309 cases, 309 pass, 0 fail.
  - `scripts/coverage run <136 cached-export case ids>`: the 136 executable
    cases with warm Gobra exports under `artifacts/coverage/work/`. This is
    the comparison point for later regression accounting. Results in
    `artifacts/coverage/latest.tsv` at baseline time.
- result summary: 136 cases, 123 pass, 13 fail, 0 unsupported-accepted.
  Failing stages: 3 differential, 5 lean-observation, 4 json-check,
  1 artifact-check.
- The remaining ~536 executable corpus cases have no cached Gobra export and
  were validated Go-side only during the core coverage spike
  (`GOLEAN_FRONTEND=none`); they are frontend-blocked, not semantic failures.

Baseline failure classification:
- `arrays/array-bounds`, `ints/divide-by-zero`, `ints/negative-shift`
  (differential): Lean panic messages missing Go's `runtime error: ...`
  prefix/detail. Message-alignment fixes, not model gaps.
- `methods/interface-dispatch` (json-check): Gobra export contains a
  `MethodSubtypeProof` member the strict decoder rejects. This is cleanup
  target item 2 (proof members must not become executable; decode as wire
  data or ignore as metadata).
- `range/range-map-sum`, `range/range-nil-map` (json-check): map-range
  expression nodes not decoded; frontend/decode gap.
- `maps/nil-read-key-types` (json-check): malformed/unsupported member tag in
  export; frontend gap.
- `comparisons/short-circuit/array-skips-interface-panic`,
  `comparisons/short-circuit/array-reaches-interface-panic`,
  `comparisons/short-circuit/nested-array-struct-skips-panic`
  (lean-observation): interface conversion for slice dynamic types is
  unsupported in the new interface subset.
- `comparisons/short-circuit/nested-array-struct-reaches-panic`
  (artifact-check): stale unsuccessful artifact record for the same case
  family.
- `interfaces/type-assert-interface` (lean-observation): default value for
  Gobra-mangled defined type name `assertInterfaceReader_4b5075e4_T`;
  depends on raw Gobra name identity (cleanup target item 3).
- `interfaces/typed-nil-pointer-compare` (lean-observation): interface
  equality between typed-nil interface boxes unsupported (cleanup Phase 5
  territory).

Known green-on-junk dependencies (expected principled regressions later):
- Interface dispatch and type assertions key on raw Gobra-mangled names
  (`*nilCompareA_4b5075e4_T` style) and `MethodInfo.uniqueName` strings.
  Phase 2/5 replace these; some interface cases may go red transiently.
- `Expr.old` currently evaluates as current-state identity in
  `GoLean/GoCore/Eval.lean`. Any case relying on runtime `old` will regress
  in Phase 1 and should be reclassified as frontend/lowering unsupported.
- Type-definition recovery by adjacency in `GobraToIR.lowerTypeDefsFromTypes`
  remains a heuristic (cleanup target item 4).

Changed:
- none yet on this branch (handoff file only).

Phase:
- Phase 0 complete. Next: Phase 1, remove runtime `old`.

Validation:
- `lake exe golean`: pass.
- coverage: see baseline above (full 136-case cached-export run).
- `git diff --check`: clean.

Regressions:
- none yet.

Known blockers:
- none for Phase 1.

Next recommended step:
- Phase 1: remove `Expr.old` from GoCore syntax and evaluation; make Gobra
  `Old` in runtime positions fail closed at lowering; rerun the 136-case
  baseline slice and record deltas.

Commit status:
- uncommitted (this file), to be committed as the Phase 0 record.
