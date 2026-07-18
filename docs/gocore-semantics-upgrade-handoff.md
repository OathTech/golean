# GoCore Semantics Upgrade Handoff

This file is the persistent handoff log for the semantics upgrade defined in
`docs/gocore-semantics-upgrade-goal.md`. Newest entry first. Each entry either
appends to or explicitly supersedes the previous one.

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
