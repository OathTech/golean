# Go to Lean via Gobra: Discussion Plan (2026-06-26)

> **Provenance.** Written 2026-06-26 in the `go-lean/` workspace root as `PLAN.md`,
> outside this repository; relocated here unchanged on 2026-07-29 during a pre-wipe
> backup audit. Paths of the form `deps/…` below are relative to the workspace
> root — i.e. `../deps/…` from this repo root.

## North Star

The goal is not merely to produce a pleasant Lean view of a small Go subset. The goal is a practical path toward a broad Go semantics and verification pipeline in Lean.

Project priorities:

- Differential testing everywhere: every translation layer should have executable or checkable artifacts that can be compared against Go, Gobra, Goose/Perennial examples, or Lean evaluation.
- Coverage-first: handle as much real Go/Gobra code as possible, with explicit unsupported markers rather than silent semantic narrowing.
- AI-backed proofs: generated proof obligations may be broad and messy; we should optimize for proof-state structure, source mapping, generated lemmas, and agent-friendly iteration rather than requiring a tiny proof-friendly source subset.
- Best-ideas reuse: borrow Aeneas's generated Lean/WP ergonomics, Goose/Perennial's heap/resource semantics organization, Strata's Lean-native VCG/SMT/transformation ideas, and Gobra's frontend/specification coverage.
- Lean-native implementation: use Lean's standard libraries, `Std.Do`/WP idioms, Lake organization, JSON support, metaprogramming, and eventually Iris-Lean or an Iris-like Lean resource layer where appropriate.

This changes the strategy from "choose Aeneas or Goose" to "build a Lean semantic core that can support both execution and proof, then expose ergonomic generated code and proof scaffolding around it."

## Current Baseline

- Gobra is cloned at `deps/gobra`.
- Aeneas is cloned for reference at `deps/aeneas`.
- Goose is cloned for reference at `deps/goose`.
- Perennial is cloned for reference at `deps/perennial`; this includes the current integrated Goose work and the Rocq/Iris GooseLang semantics.
- Strata is cloned for reference at `deps/strata`.
  - Commit: `e912c9bba0ad82244185e9c75b9535a6aedbd0f3`.
  - It is a Lean 4 dialect/IVL/VCG/SMT framework, not a Go semantics.
  - Review notes are in `STRATA_REVIEW.md`.
- Gobra builds with `sbt compile` using the local launcher at `deps/sbt-launch-1.12.4.jar`.
- Use `./scripts/gobra-sbt compile` from this workspace to rebuild.
- Z3 is available at `/opt/homebrew/bin/z3`; the installed version is 4.16.0.
- A no-verification sample run works:

```sh
./scripts/gobra-sbt "run --noVerify --printInternal --printVpr -i src/test/resources/regressions/examples/swap.gobra"
```

This emits `swap.gobra.internal` and `swap.gobra.vpr` beside the input file.

Focused Gobra test targets that passed locally:

```sh
./scripts/gobra-sbt 'set Test / javaOptions += "-DGOBRATESTS_Z3_EXE=/opt/homebrew/bin/z3"' 'testOnly viper.gobra.GobraPackageTests'
./scripts/gobra-sbt 'set Test / javaOptions += "-DGOBRATESTS_Z3_EXE=/opt/homebrew/bin/z3"' 'testOnly viper.gobra.GobraTests -- -z swap.gobra'
./scripts/gobra-sbt 'set Test / javaOptions += "-DGOBRATESTS_Z3_EXE=/opt/homebrew/bin/z3"' 'testOnly viper.gobra.GobraTutorialTests'
```

The full `test` target starts and runs many tests, but with Z3 4.16.0 it reached a long-running solver call in the regression suite and was interrupted. Gobra's documentation and comments mention Z3 4.8.7 as the tested version, so full-suite reliability probably needs a pinned older Z3.

## What Gobra Gives Us

Gobra's main pipeline is:

```text
Go/Gobra source
  -> parser frontend AST
  -> type information
  -> desugared Gobra internal AST: viper.gobra.ast.internal.Program
  -> internal transformations
  -> Viper/Silver AST: viper.silver.ast.Program
  -> Silicon/Carbon backend verification
```

The key source locations are:

- `deps/gobra/src/main/scala/viper/gobra/Gobra.scala`: orchestration of parsing, typechecking, desugaring, internal transforms, Viper encoding, verification.
- `deps/gobra/src/main/scala/viper/gobra/ast/internal/Program.scala`: Gobra's internal program representation.
- `deps/gobra/src/main/scala/viper/gobra/translator/Translator.scala`: entry point from Gobra internal AST to Viper/Silver AST.
- `deps/gobra/src/main/scala/viper/gobra/translator/encodings/programs/ProgramsImpl.scala`: program-level Viper AST construction.
- `deps/gobra/src/test/resources`: useful seed corpus for incremental testing.

## Aeneas Design Takeaways

Aeneas is not primarily a deep embedding of Rust. Its Lean backend generates shallow Lean definitions that execute in an error/divergence monad, plus weakest-precondition specifications and tactics for reasoning about those generated definitions.

The important pipeline is:

```text
Rust source
  -> Charon LLBC
  -> Aeneas symbolic interpreter
  -> Pure AST
  -> many Pure micro-passes
  -> Lean definitions + external model templates + translation manifest
```

The key trick is Rust-specific: safe Rust's ownership and borrowing discipline lets Aeneas functionalize mutable references. Mutable state is usually passed and returned as values; returned borrows become values plus backward continuations. This avoids a general heap model for the safe Rust subset.

The Lean side is still very relevant:

- `Result T` models success, failure, and divergence.
- Checked scalar and collection operations are executable Lean definitions with specs.
- Hoare/WP notation, written in Aeneas as `f x <{ r => post r }>` conceptually, gives a proof style close to the generated code.
- The `step` tactic discharges monadic plumbing and applies registered operation/function specs.
- Loops are factored into auxiliary recursive definitions or a `loop` combinator with invariant/measure specs.
- External models are generated as templates and maintained by hand.
- `translation.json` records source-to-Lean declaration metadata.
- A large micro-pass layer matters: generated code needs simplification and naming passes before it is pleasant to prove against.

For this project, the reusable lesson is the backend shape, not the Rust memory trick.

## Go Memory Model Consequence

Safe Go is memory-safe in the garbage-collected language sense: no explicit free, no dangling pointers, nil and bounds errors trap, and ordinary safe code cannot do arbitrary pointer arithmetic. This stops being true for `unsafe`, cgo, and racy concurrent programs; Go's memory model explicitly allows races on multiword values to observe inconsistent state, which can become memory corruption.

But Go is not Rust-like for verification. It has ordinary shared aliases:

```go
p := &x
q := p
*p = 1
return *q
```

No ownership rule lets us erase the heap here. Gobra also explicitly targets heap-manipulating and concurrent Go programs using implicit dynamic frames, permissions, predicates, fractional permissions, and permission transfer. Therefore, for "almost any Go code Gobra supports", we should assume an explicit heap/resource model is required.

This suggests a two-level Lean story:

- An executable shallow embedding for concrete, deterministic Go behavior.
- A proof/resource layer, likely using Iris-Lean or a similar separation-logic framework, for Gobra-style permissions, shared heap reasoning, and concurrency.

Iris-Lean should be treated as a proof layer over the generated semantics, not as a blocker for the first concrete differential-testing backend.

## Goose and Perennial Takeaways

Goose is the closest Go-shaped precedent, but it is not a drop-in backend. It translates a selected subset of Go into Rocq definitions for GooseLang, and Perennial supplies the Iris program logic for heap, concurrency, FFI, and crash reasoning.

Useful design lessons:

- Goose/Perennial validates the explicit-heap direction for Go.
- Locals are heap-allocated when addressability matters.
- Struct values and struct field locations are both modeled.
- Slices carry pointer/len/cap and index into heap-backed arrays.
- Maps, channels, interfaces, package initialization, `defer`, `panic`, loops, and `select` are handled through explicit semantic support.
- Points-to predicates are fractional, which lines up conceptually with Gobra permissions.
- Current Perennial separates trusted Go definitions, generated code, generated proof scaffolding, and manual proof libraries.
- Goose has a semantics test workflow: run small Go tests and generated proof-assistant/interpreter tests to validate translation behavior.

Main differences from our target:

- Goose targets a deep-ish GooseLang in Rocq; our current target should remain shallow Lean definitions over a Go runtime/effect monad.
- Goose does not consume Gobra specifications or internal IR.
- Goose's subset is proof-oriented and smaller/different than "almost any Go code Gobra supports."
- Perennial proof scripts and Iris libraries are conceptually relevant, not mechanically portable to Lean.

The plan should borrow Goose's heap/resource/proof-organization ideas while borrowing Aeneas's generated-code/WP ergonomics.

## Strata Takeaways

Strata is a Lean-native platform for defining dialects, transformations, verification-condition generation, and SMT solver backends. Its Core language is roughly Boogie-like; its lower `Imperative` dialect is parameterized by pure expressions and has commands, structured statements, loops with invariants, a symbolic evaluator, a generic executable stepper, and a relational small-step semantics.

Useful ideas:

- dialect and transformation organization;
- executable interpreter plus relational semantics in Lean;
- symbolic evaluation that collects path conditions and proof obligations;
- loop elimination into assert/assume obligations;
- Boogie-like procedure contract handling;
- SMT term encoding and an abstract incremental solver interface;
- two-query VC classification using `P and Q` and `P and not Q`;
- source metadata and diagnostics discipline.

Important limitation: Strata Core is not a Go semantics. Its heap examples encode heaps manually with maps over abstract references and fields. That is a useful IVL pattern, but it does not give us native semantics for Go pointers, addressable locals, slices, maps, interfaces, channels, package initialization, panic/defer, or Gobra permissions.

Recommendation: use Strata as a design reference now and as a candidate VCG/SMT library later. Do not make it the first execution substrate. Our first milestone still needs a custom `GoCore` and executable `GoM` runtime so differential testing can compare concrete Go execution against concrete Lean execution.

## Main Research Choice

### Semantic Foundation Choice

The project should be Goose-like at the semantic foundation and Aeneas-like at the generated-proof interface.

In particular, the Lean semantics should not live only as ad hoc helper functions used by generated shallow code. We want a named, inspectable GoCore/GoLean semantic layer:

```text
Go/Gobra source
  -> Gobra frontend/export, and possibly other Go frontends later
  -> typed GoCore/GoLean IR
  -> Lean executable semantics and proof semantics
  -> generated Lean wrappers/specs/proof scaffolding
```

This supports the "complete Go semantics" goal better than a pure Aeneas-style direct shallow translation, while preserving Aeneas-like ergonomics for users and AI proof agents.

### Option A: Shallow Lean Translation from Gobra Internal IR

This is the more Aeneas-like route. Gobra remains the frontend and normalizer; our tool translates `viper.gobra.ast.internal.Program` into shallow Lean definitions over a Go effect/runtime monad.

Pros:

- Closer to Go than Viper/Silver is.
- Avoids committing Lean to Viper's verification-oriented encoding choices.
- The internal IR is already typed, desugared, and normalized enough to be a plausible semantics input.
- Gobra's test corpus can drive incremental feature coverage.

Cons:

- We must define semantics for Gobra's internal concepts, including heap, aliases, permissions/specifications, and eventually concurrency.
- The internal IR is an implementation interface, not necessarily designed as a stable external contract.
- Differential testing against Gobra becomes indirect once Gobra proceeds into Viper and SMT.

### Option B: Lean Semantics for Viper/Silver AST Emitted by Gobra

This treats Gobra as a source-to-Viper compiler and gives Lean a semantics for the generated Viper/Silver subset.

Pros:

- Easiest to compare against Gobra's existing backend path.
- `--printVpr` already gives a stable textual artifact for early experiments.
- Smaller semantic gap to Gobra's verifier result.

Cons:

- This is less a Go semantics and more a semantics for Gobra's Viper encoding.
- Viper has separation-logic and verification-condition concepts that may be heavier than the Go subset we want first.
- If our long-term target is Go-level reasoning in Lean, we may bake in the wrong abstraction boundary.

### Working Recommendation

Start with Option A, but keep Option B as an oracle and debugging artifact.

Concretely: export both the transformed internal IR and the generated Viper AST for every seed program. Translate the internal IR to shallow Lean first. Use the Viper artifact to explain mismatches and to keep Gobra's existing verification behavior visible while the Lean semantics is incomplete.

The first Lean runtime should be executable enough for differential testing:

```lean
GoM State Error a
```

or an equivalent `EStateM`-style monad with a structured heap, checked integer operations, nil/bounds/division/overflow errors, and JSON-serializable observable results. Later, the same primitive operations should get Iris-style WP/spec lemmas.

Strata adds a possible Option C: translate some proof obligations to Strata Core or reuse pieces of its VCG/SMT infrastructure. This should be explored after the first Go-vs-Lean execution loop works. If Strata accelerates VC generation without forcing the runtime semantics through a Boogie-like map-heap encoding, it is worth integrating. If it starts determining the shape of the Go semantics too early, keep it as reference material.

## Proposed Phases

### Phase 1: Artifact Export and Corpus Harness

Goal: make Gobra a deterministic producer of comparison artifacts.

- Add or wrap a Gobra entry point that stops after internal transformations and emits a machine-readable artifact, preferably JSON or S-expressions rather than pretty-printed text.
- Emit Viper/Silver AST artifacts for the same inputs.
- Build a corpus manifest from `src/test/resources/regressions`, starting with tiny examples such as simple functions, assignments, structs, pointers, and methods.
- Add Goose/Perennial examples and ordinary Go packages as secondary corpora for non-Gobra executable Go coverage.
- Keep Strata Core examples as a tertiary verification-shape corpus, not as Go execution tests.
- Record expected Gobra behavior: parse/type/desugar success, Viper encoding success, and, where Z3 is available, verifier success/failure.

Deliverable: `go-lean` command or test target that regenerates artifacts for a small pinned corpus.

### Phase 2: Lean Core for a Tiny Shallow Subset

Goal: prove the workflow before covering Go broadly.

- Define Lean runtime types for checked integers, booleans, structs, addresses, heap cells, and errors.
- Define executable primitives for locals, assignment, load/store through pointers, allocation, sequencing, conditionals, and simple functions.
- Keep the initial IR/runtime custom rather than making GoCore a Strata dialect immediately; revisit Strata once concrete execution and JSON comparison are working.
- Use Goose/Perennial's local-variable convention as a serious baseline: ordinary immutable temporaries may compile to Lean lets, but addressable locals and mutable variables should be represented by heap locations.
- Model structs at two levels early: value records for pure values, plus field-addressable heap layout for pointers to structs.
- Generate shallow Lean function definitions from exported Gobra internal IR.
- Keep pure/no-heap functions as plain Lean where possible; use `GoM` as soon as addressable storage or aliasing appears.
- For seed examples, generate Lean files that typecheck and can be evaluated by a Lean harness.

Deliverable: one Gobra example translated into a Lean module with an executable evaluation result, plus a small manually written WP theorem for a representative primitive.

### Phase 3: Differential Testing Strategy

Goal: compare generated Lean execution against real Go execution without pretending Gobra's verifier is an execution oracle.

- Syntactic differential tests: Gobra internal IR export is stable across rebuilds; Lean AST generation is deterministic.
- Runtime differential tests: generated Go harnesses and generated Lean harnesses run the same concrete inputs and emit comparable JSON.
- Cross-frontend differential tests, where possible: compare behavior on examples accepted by both Gobra and Goose or by Gobra and plain `go test`.
- Metamorphic tests: generate small Go programs or inputs that vary harmless syntax, evaluation order constraints, aliases, and boundary values.
- Verification-shape tests: Gobra-accepted examples should generate Lean obligations of the expected shape, even before all obligations are automatically proved.
- Optional Strata comparison tests: for examples lowered to Strata Core, compare generated obligation labels and SMT outcomes against our Lean obligation generation.
- Negative tests: Gobra-rejected examples should fail before Lean translation, or generate explicit unsupported-feature markers rather than unsound Lean.

Deliverable: a test matrix with each corpus example labeled as `export-only`, `lean-syntax`, `lean-exec`, or `lean-proof`.

The comparison should be:

```text
Go source + generated Go harness -> JSON result
Gobra internal IR -> generated Lean + Lean harness -> JSON result
compare observable return values, final reachable heap/state, and error class
```

Gobra verifier behavior remains a separate comparison:

```text
Gobra verifier accept/fail vs generated Lean proof obligations/proof status
```

### Phase 4: Feature Expansion

Suggested order:

1. Pure expressions and integer model, including Gobra's `int32`/default integer configuration.
2. Locals, assignment, sequencing, conditionals, loops with invariants.
3. Functions and methods with pre/postconditions.
4. Structs and pointers.
5. Arrays and slices.
6. Maps and basic package/external models.
7. Ghost code and assertions.
8. Permissions and separation-logic assertions, probably via an Iris-Lean layer.
9. Interfaces, concurrency/channels, `defer`/`panic`, and advanced Gobra features.

The checkpoint after each feature is not "all of Gobra works"; it is "the corpus slice using this feature has exported artifacts, Lean output, and explicit unsupported markers for the rest."

### Phase 5: Proof Automation and AI Workflow

Goal: make generated proof obligations tractable for both humans and AI agents.

- Emit source maps from Go/Gobra declarations and statements to Lean definitions, goals, and generated lemmas.
- Generate small named specs for primitive operations and user functions, not one giant theorem per package.
- Prefer proof obligations with stable names, local hypotheses, and explicit resource assertions.
- Maintain generated proof scaffolding separately from manual/AI-written proof files, following the Goose/Perennial split.
- Use Lean LSP tooling to drive proof iteration and collect failure modes as regression tests.
- Treat proof automation as an evolving layer: first generated simp/WP lemmas, then tactics, then AI proof search over structured obligations.

## Immediate Questions to Decide Together

- Should the first exporter live as a small patch inside `deps/gobra`, or should this repo wrap Gobra without modifying it?
- Should the machine-readable artifact preserve Gobra's Scala ADT names exactly, or define a smaller external schema that we own?
- Should we vendor/copy the useful parts of Aeneas's `Result`/WP/step design, or define a smaller `GoM` API and only mirror the proof style?
- Should Iris-Lean be introduced immediately as a dependency, or after the executable runtime differential loop works for heap aliases?
- Should Strata stay source-level reference material for now, or should we run a small experiment translating selected GoCore obligations into Strata Core?
- Do we want a pinned older Z3 for Gobra's full suite, or should early work stay on focused tests and `--noVerify` artifacts?
