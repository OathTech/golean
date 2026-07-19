# TODO

See `docs/roadmap.md` for the phased project roadmap. This file tracks tactical
backlog items.

## Current Priority Sequence (post-2026-07 design review)

The end state is a complete trust chain: real Go → executable model
(differentially validated against `go run`) → the **relational semantics**
(the proof authority) → machine-checked proofs (Iris-Lean). The two-reviewer
design review found the executable/testing half sound but the proof half
blocked at the foundation (the interpreter and the shared `Ops` substrate are
`partial def`, so the relation's own premises are opaque and its correspondence
theorems are unprovable-as-written). **Feature breadth is paused for this
foundation work.** Reviews synthesized in the design docs; both reviewers
(proof-chain, engineering) idle/available.

Done:

- [x] Turn reviewer-found Go divergences into differential tests, then fix
  (`control-flow/for-continue-post-plain`, `multi-assign/blank-discard-nonint`).
- [x] Drop Gobra entirely; native is the only frontend, real Go is the oracle.
- [x] Honesty fixes (correspondence "blocked", not "deferred"; sufficiency not
  yet "quorum covered").

In order:

1. **Totality of the substrate + interpreter** (the top priority; also an Iris
   prerequisite — Iris WP rules are proved by inverting the relation's premises,
   which is impossible while those premises call opaque partials):
   - [x] Convert the structurally-recursive `Ops` ops (`loadLoc`, `storeLoc`,
     `coerceStoredValue`) to plain `def`.
   - [x] Decide and implement the type-directed-recursion strategy: **fuel**
     (decremented only at `.defined` type-env resolution, so it bounds
     type-nesting depth not value size). See
     `docs/2026-07-18_totality-fuel-decision.md`. Applied to
     `valueEq`/`normalizeValueForTy`/`defaultValue`/`convertValueToTy`/
     `resolveDefinedAliases`/`goTypeNameForMessage` via constant-fuel wrappers
     over fuel'd workers (call sites unchanged); array/struct child recursion
     refactored from for-loops to structural list helpers. **`Ops.lean` is now
     fully total — zero `partial def`.** Library builds, 40 unit tests green,
     quorum 37/39.
   - [ ] De-partial the interpreter (`Eval.lean`, ~30-function mutual block) via
     structural/well-founded recursion on `fuel`. `execStmt`/`execStmts` already
     carry fuel; the `evalExpr` expression recursion, the call/loop recursion,
     and the many `for`-loop helpers need the same fuel-and-structural treatment
     used for `Ops`. This is the larger remaining half.
   - [ ] Prove one real interpreter↔relation correspondence lemma on the
     scalar/control subset to validate the whole approach end-to-end.
2. **Relation catch-up + merge invariant** (`Rel.lean` must become an actual
   authority):
   - Grow `Rel.lean` to cover the current interpreter subset — slices, maps,
     `mapRange`, conversions, multi-assign — with nondeterminism expressed as
     the relation permitting **all** valid behaviors (map order = any
     permutation; append cap = any `≥ newLen`). The oracle stays interpreter-
     side for deterministic testing; the relation is genuinely nondeterministic
     (this is an Iris soundness requirement, not just testing hygiene).
   - Adopt the merge invariant: no interpreter feature merges without its
     relational rule (total premises; nondeterminism permitted where Go has it).
3. **Guardrails** (keep the differential anchor honest):
   - Strengthen the oracle-invariance check — exhaustive permutations for small
     maps + seeded-random streams (seed recorded), and make it
     frontend-independent.
   - Add golden-wire emitter unit tests (`tools/nativefrontend/*_test.go`) for
     the intricate desugarings: ANF hoisting/ordering, short-circuit no-hoist,
     compound-assign, variadic spread, keyed struct/slice/map literals.
   - Add a multi-file exec corpus case (cross-file calls/types) so the native
     multi-package advantage is a tested guardrail.
4. **Iris `Language` spike** (validate the proof endgame on a slice): once the
   scalar/control relation is total, instantiate Iris-Lean's `Language`
   typeclass for that subset and prove one WP rule (e.g. `wp_load`). This
   flushes out the structural mixin lemmas, the continuation-machine-vs-
   evaluation-context design question, and the toolchain version gap
   (iris-lean v4.31 vs project v4.29 — see `docs/iris-lean-review.md`) before
   building out more relation.

Deferred until the foundation is set (then resume under the merge invariant):

- Native interface dispatch (closes quorum 39/39; `AckedIndexer` is the last 2
  quorum cases). Cheap and broadly useful, but a feature — paused.
- Remaining native feature breadth toward the raft ladder: switch, closures/
  func values, defer, string/rune range, and the rest.
- `slices.Sort` extern + the input-fuzzing harness for the quorum sufficiency
  Layer 3 (the `slices.Sort`-faithful `CommittedIndex` variant).

## Goose/Perennial Design Mapping

- Produce a systematic design mapping of GoCore against new Goose/Perennial
  (reference checkouts under `../deps/goose` and `../deps/perennial/new`),
  area by area, so their lessons are adopted or explicitly rejected rather
  than rediscovered. Record the mapping and each adopt/reject decision in a
  dedicated doc (suggested: `docs/goose-perennial-mapping.md`).
- Areas to map, with their Perennial/Goose anchors: memory model and typed
  points-to (`theory/mem.v`, per-index array ownership in `theory/array.v`)
  versus GoCore `Loc.field`/`Loc.index` and the heap-cell typing work;
  semantic type universe and tables (`defn/prelang.v`, `defn/postlang.v`,
  `GoSemanticsFunctions`) versus GoCore `TypeId`/`FuncId` tables; interface
  semantics from type sets and method sets (`defn/interface.v`) versus the
  planned Phase 5 rebuild; slice descriptors and nondeterministic append
  capacity (`defn/slice.v`) versus `docs/slice-model.md`; strings as byte
  sequences (`go_string`); channels and concurrency primitives (new Goose
  channel model) ahead of the Iris-Lean concurrency phase; proof-generation
  templates (`proofgen/tmpl/types.tmpl`) ahead of Phase 5/6 proof output.
- The mapping should state, per area, what Goose/Perennial does, what GoCore
  does today, whether the delta is intentional (and why) or a gap with a
  planned fix, and which upcoming phase consumes the lesson. Keep it a
  design-review artifact, not ported code: the architecture lesson (clean
  frontend translation, explicit semantic tables, typed primitives, proof
  automation layered above the core) is the thing to preserve.

## Differential Execution

- Keep Gobra-specific handling in `GobraToIR`; semantic work belongs in GoCore unless it is purely frontend lowering.
- Current iteration priority after the core coverage spike: use
  `scripts/coverage run ...`/`scripts/diff-one ...` as the conformance loop and
  fix cases that reach a Go-vs-Lean differential mismatch before chasing cases
  blocked in Gobra export or JSON decoding.
- Track frontend-blocked corpus rows separately from GoCore semantics work.
  Recent focused probes show `delete`, `clear`, `range int`, richer method
  expressions/auto-addressing, floats, complex numbers, and `min`/`max` are
  often blocked before Lean by the current Gobra path; do not count those as
  GoCore semantic failures until a frontend can produce GoCore for them.
- Promote cases from `Corpus/challenges/semantic-edges/` into the active
  Gobra/Lean differential suite one feature at a time. Keep the challenge
  corpus runnable by `scripts/semantic-edges-challenge-smoke`, but do not treat
  it as a supported-semantics claim until cases land in
  `Corpus/coverage/manifest.tsv`.
- Keep `Corpus/coverage` comprehensive. Do not remove cases because the
  frontend or semantics fails; let `scripts/coverage` report the failing stage.
- Do not maintain Gobra variants of coverage inputs. The canonical Go source is
  the input to both `go run` and the frontend/Lean path.
- Expand `Corpus/coverage/negative/compile` with static Go errors. Runtime Go
  errors that execute and panic belong in the differential manifest with
  `expected_status=panic`.
- Replace stringly typed evaluator failures with structured `GoError` values and
  stable observations. CLI classification must not depend on matching error
  message prefixes.
- Treat `unsupported` and `stuck` as failures by default. A differential case may
  expect them only with an explicit manifest reason.
- Use a structured observation parser/comparator for Go and Lean output instead
  of raw JSON string comparison.
- Add timeouts/fuel for Gobra export, Go execution, Lean execution, and Lean
  builds used by the harness.
- Prevent stale or cross-test artifacts by tying generated Gobra JSON to source
  hashes and using per-run temporary artifact directories with atomic publish.
- Keep `scripts/diff-coverage` same-source: Go execution and frontend/Lean
  execution must consume the same canonical Go file.
- Preserve the executable corpus contract: every row in
  `Corpus/coverage/manifest.tsv` names a subject function in the canonical
  `main.go`. Successful cases print JSON from `main`; expected panic cases let
  Go panic and are normalized by the top-level runner.
- Investigate the current Gobra export blockers surfaced by the same-source
  corpus: local addressability for `&x`/array slicing from arrays, pointer
  receiver method lookup, string pointer assignment, and variadic nil-slice
  comparison.

## Hardening Phase

- Extend type-directed equality for interfaces, function values, and exact
  dynamic comparability panics once those value forms exist.
- Add a small relational GoCore semantics skeleton before concurrency or
  Iris-facing proof rules.
- Keep the executable interpreter factored so it can be related to a future
  relational GoCore semantics for Iris-Lean. The interpreter is for testing; it
  should not be the only semantic authority.
- Thread structured errors through GoCore:
  `panic`, `unsupported`, `stuck`, and `internal`.
- Classify nil pointer dereference and Go-defined runtime traps as `panic`, not
  `stuck`.
- Extend the integer/string model beyond the current fixed-width and byte-string
  slices: constants, rune iteration/conversions, broader conversion families,
  more integer edge cases, and exact architecture-dependent `int`/`uint` policy
  in the future relation.
- Replace `execStmt : ExecState -> Except ... ExecState` with an explicit
  `ExecOutcome` for normal completion, return, break, continue, panic,
  unsupported, and stuck behavior.
- Add broader control-flow coverage around nested `if`, early `return`, and
  later labeled control flow.
- Keep expression evaluation able to grow to calls-in-expressions, allocation,
  map operations, and channel operations without changing its public shape
  again.
- Continue slices with descriptor values over backing locations, following
  `docs/slice-model.md`. Do not model slices as copied vectors.
- Keep append capacity growth explicit in tests. The executable interpreter now
  has a deterministic policy for Go-vs-Lean differential runs; the later
  relational semantics should still allow implementation-specific fresh
  capacities.
- Track semantic policy choices that remain open for differential refinement,
  especially allocation limits, append growth, zero-capacity slices, string
  slicing, and panic-message details.
- Keep improving artifact-generation scalability. Gobra exports are now
  incremental by source hash, but a cold export still invokes SBT/Gobra once per
  fixture. Prefer batched package export or a native Go frontend path once
  practical.
- Treat Gobra's permission-argument variants of `copy` and `append` as
  frontend artifacts. The Gobra fork may enrich `--printInternalJson` with
  plain-Go nodes such as `GoSliceCopy` and `GoSliceAppend`; do not add Gobra
  permission semantics to GoCore just to support them.
- Evaluate lvalues and rvalues before committing stores, so multiple assignment
  and call assignment match Go's sequencing rules.
- Bounds-check indexed locations when evaluating the lvalue, including
  address-of-index operations such as `&a[i]`.
- Keep GoCore free of Gobra verification constructs. Gobra assertions,
  preconditions, postconditions, invariants, predicates, and ghost artifacts are
  frontend wire data only unless a later proof-extraction design explicitly
  reinterprets them outside the runtime semantics.

## GoCore Memory Milestone

- Track frontend gaps separately from semantic gaps. For example, Gobra
  currently rejects the Go `delete` builtin, so map deletion needs either Gobra
  fork enrichment or a future native Go frontend before it can enter the active
  Gobra-fronted differential suite.
- Add regression tests that observe memory effects through ordinary Go returns
  or Go-side output, not Gobra assertions.
- Add richer call-frame tests, including returned values and nested calls.
- Add method-call tests from Gobra JSON beyond `examples/swap`.
- Track Gobra frontend gaps found while promoting semantic-edge cases: Gobra accepts
  variadic calls/spreads but rejects `range` directly over a `...int`
  parameter, so `features/variadic.gobra` uses `len`/index iteration.
- Track Gobra frontend gaps found while promoting conversion cases: Gobra
  rejects legal Go integer-to-string conversions such as `string(65)` and
  `string(byte(255))`, so active differential coverage cannot use the Gobra
  frontend for this rune-conversion slice yet.
- Track Gobra frontend gaps found while promoting switch cases: Gobra accepts
  basic and expressionless switches but rejects explicit `fallthrough` in the
  parser.

## Completed GoCore Memory Milestone Items

- Split the former monolithic `GoLean/IR.lean` into GoCore syntax, value import
  point, state, operations, and executable evaluation modules. `GoLean/IR.lean`
  remains as a compatibility import.
- Converted GoCore expression and assignee evaluation to return an updated
  `ExecState`, preserving Go's evaluate-before-store assignment discipline while
  leaving room for calls-in-expressions, receives, and effectful builtins.
- Moved concrete `GoError`, `Loc`, `SliceValue`, `MapValue`, and `GoValue`
  definitions into `GoLean/GoCore/Value.lean`; `GoLean/Runtime.lean` is now only
  a compatibility import.
- Replaced raw value-shape equality with type-directed GoCore equality and
  type-directed map-key comparison.
- Added first typed integer support: GoCore integer kinds, Gobra integer-kind
  lowering, fixed-width normalization on typed stores/arithmetic, a 64-bit
  executable policy for `int`/`uint`, and `int8` overflow differential coverage.
- Added first integer conversion support: Gobra `Conversion` decoding/lowering,
  GoCore integer-to-integer conversion normalization, and `byte(300) == 44`
  differential coverage. Non-integer conversions remain explicitly unsupported.
- Added byte-backed string literals and string/`[]byte` conversions:
  Gobra JSON now exports exact `StringLit.bytes`, Lean rejects stale string
  literal JSON, GoCore has explicit byte-string conversion nodes, and the
  differential suite covers escaped arbitrary bytes plus conversion copy
  semantics.
- Added first shift support: Gobra `ShiftLeft`/`ShiftRight` decoding/lowering,
  fixed-width left/right shift normalization, signed arithmetic right shift,
  and negative-shift panic coverage.
- Added string byte indexing: indexing a Go string reads from its UTF-8 byte
  sequence and returns a `uint8`, with direct and differential coverage.
- Switched GoCore string values from Lean `String` to byte-backed `GoString`,
  matching Go's byte-level string operations and Perennial/new Goose's
  `go_string` model.
- Added two-index string slicing over bytes, including an invalid-UTF-8
  substring differential case.
- Added bitwise integer operators: `&`, `|`, `^`, `&^`, and unary `^`, using
  fixed-width modular bit patterns and type-directed result normalization.
- Replaced stable variable references with heap-backed locals.
- Added `Loc.base` and `Loc.field` path-like locations.
- Added load, store, address-of, dereference, struct field get, and field ref.
- Added `Value.struct` and struct literals.
- Added direct function and method calls with fresh local frames and shared heap.
- Made `examples/swap` execute as ordinary Go after Gobra assertions/specs are
  erased at lowering.
- Added GoCore `if`, explicit `return`, and unlabeled `break`/`continue`, with
  Gobra-fronted differential smoke coverage.
- Added fixed-array `len`/`cap`, with Gobra-fronted differential smoke
  coverage.
- Added fixed-array zero-value initialization, nested arrays, arrays through
  function parameters/results, and pointer-to-array indexing/assignment.
- Added type-aware `len`/`cap` for pointer-to-array values, including nil
  pointers, so GoCore matches Go's non-dereferencing array-pointer behavior.
- Reviewed Goose/Perennial/Gobra slice designs and selected a descriptor over
  backing locations as the direction for GoCore slices.
- Added the first descriptor-backed slice subset: nil slice defaults, array
  slicing, slice indexing/addressing, two-index and full slicing, Gobra `Slice`
  JSON decoding/lowering, and differential array-to-slice alias coverage.
- Added Gobra `MakeSlice` decoding/lowering and nonzero-capacity `make` support
  with differential coverage.
- Added Gobra `NewSliceLit` decoding/lowering and slice literal differential
  coverage.
- Enriched the Gobra JSON fork so `--printInternalJson` accepts plain Go
  `copy`/`append` and emits `GoSliceCopy`/`GoSliceAppend`; added GoCore
  execution and differential coverage for overlapping copy and append
  in-place/growth aliasing.
- Refined append growth to allocate real backing capacity tail cells and match
  current focused Go differential cases that observe post-reallocation `cap`.
- Added the first executable interface-value subset: `ToInterface` boxes carry
  a dynamic type tag, Gobra `SafeTypeAssertion` and expression `TypeAssertion`
  lower to GoCore, interface method calls dynamically dispatch to concrete
  methods where Gobra exposes method metadata, and focused differential coverage
  passes for interface dispatch, interface-to-interface assertions, concrete
  assertions, assertion panics, and interface storage-copy cases.
- Next interface semantics targets are typed-nil interface equality,
  dynamic interface equality/comparability panics, and type switches. Keep
  frontend-export failures separate; many typed-nil and error idiom cases are
  still blocked before Lean by the current Gobra path.
- Made `scripts/gobra-smoke` manifest-driven for Lean execution and expanded
  the differential suite to 29 cases, including typed nil slices, nil/empty
  slice distinctions, nil append, variadic overlap append, full slicing,
  full-slice bounds panics, zero-length `make`, nil copy, and short copy.
- Added source-hash based Gobra artifact caching, so warm `scripts/gobra-smoke`
  runs reuse unchanged successful exports.

## Proof Generation

- Deferred until after the executable semantics and differential harness cover a
  substantial Go subset.
- Define a relational small-step or big-step GoCore semantics over the same
  syntax, values, locations, errors, and outcomes as the executable interpreter.
- Prove, where practical, that the executable interpreter is sound with respect
  to the relational semantics on supported deterministic terminating runs.
- Generate struct typed points-to predicates as field-wise ownership.
- Generate field load/store/access lemmas over `Loc.field`.
- Prototype a Lean WP/VCG layer over GoCore.
- Evaluate where Iris-Lean should enter for heap and concurrency reasoning.
