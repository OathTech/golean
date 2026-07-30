# Strata Design Review (2026-06-26)

> **Provenance.** Written 2026-06-26 in the `go-lean/` workspace root as `STRATA_REVIEW.md`,
> outside this repository; relocated here unchanged on 2026-07-29 during a pre-wipe
> backup audit. Paths of the form `deps/…` below are relative to the workspace
> root — i.e. `../deps/…` from this repo root.

## Local Checkout

- Repository: `https://github.com/strata-org/Strata`
- Local path: `deps/strata`
- Commit: `e912c9bba0ad82244185e9c75b9535a6aedbd0f3`
- Lean toolchain: `leanprover/lean4:v4.29.1`
- Lake dependencies from `lake-manifest.json`:
  - `StrataDDM` at `fbd9f71d6f03f56d71dc0ea4c40fcca7f4ebb6f8`
  - `plausible` at `4bdad1f417437e3331492708ce8320aec350280a`

I reviewed Strata at the source level. I did not build it; its Lake packages were not fetched in this checkout. The machine has `cvc5` and `z3` on `PATH`, so the likely missing step is just Lake dependency fetching/building if we decide to exercise it.

## What Strata Is

Strata is a Lean 4 platform for defining languages, transformations, and analyses. It is organized around MLIR-inspired "dialects" and a Dialect Definition Mechanism (DDM) that can generate syntax, parsers, printers, preliminary type checkers, and ASTs.

The current verification-centered stack is:

```text
custom dialect or Strata Core syntax
  -> dialect-specific AST
  -> type checking
  -> transformations
  -> symbolic evaluation / VCG
  -> SMT encoding
  -> solver result classification
```

The design is relevant because it is Lean-native and already contains an imperative semantic layer, a Boogie-like verification language, transformation passes, source metadata, SMT encoding, and solver orchestration.

## Imperative Dialect

The reusable low-level layer is `Strata.DL.Imperative`.

Important source files:

- `deps/strata/Strata/DL/Imperative/Cmd.lean`
- `deps/strata/Strata/DL/Imperative/Stmt.lean`
- `deps/strata/Strata/DL/Imperative/CmdEval.lean`
- `deps/strata/Strata/DL/Imperative/StmtEval.lean`
- `deps/strata/Strata/DL/Imperative/CmdSemantics.lean`
- `deps/strata/Strata/DL/Imperative/StmtSemantics.lean`
- `deps/strata/Strata/DL/Imperative/CFGSemantics.lean`

The core imperative language is parameterized by a `PureExpr` implementation. Commands include `init`, `set`, `assert`, `assume`, and `cover`. Statements add blocks, conditionals, loops with invariants and optional measures, labeled exits, function declarations, and type declarations.

There are three distinct pieces that matter:

- A symbolic evaluator via `EvalContext`, collecting path conditions and `ProofObligation`s.
- A generic executable stepper via `RunOps` and `runStmt`, with fuel.
- A relational small-step semantics via `StepStmt` and `StepStmtStar`.

This is a strong precedent for our own split between executable differential testing and proof semantics. It also shows one possible Lean style for keeping the interpreter and the relational semantics near each other.

## Strata Core

Strata Core is roughly a Boogie-like IVL.

Important source files:

- `deps/strata/Strata/Languages/Core/Program.lean`
- `deps/strata/Strata/Languages/Core/Procedure.lean`
- `deps/strata/Strata/Languages/Core/Statement.lean`
- `deps/strata/Strata/Languages/Core/Verifier.lean`
- `deps/strata/Strata/Languages/Core/SMTEncoder.lean`

Core supports abstract types, axioms, distinct declarations, pure functions, procedures, contracts, old-state expressions, input/output/inout parameters, maps, bitvectors, integers, Booleans, datatypes, and SMT-oriented operators. Procedure calls are specified Boogie-style: assert checked preconditions, havoc outputs, assume postconditions.

This is valuable for verification-condition generation, but it is not itself a Go semantics. Its heap reasoning example, `deps/strata/Examples/HeapReasoning.core.st`, models heap manually as maps over abstract references and fields. That is useful as an IVL encoding pattern, but it is not a built-in operational model of Go allocation, pointers, slices, maps, interfaces, channels, or Gobra permissions.

## Transformations and SMT

Important transformation files:

- `deps/strata/Strata/Transform/LoopElim.lean`
- `deps/strata/Strata/Transform/CallElim.lean`
- `deps/strata/Strata/Transform/ProcBodyVerify.lean`
- `deps/strata/Strata/Transform/StructuredToUnstructured.lean`
- `deps/strata/Strata/Transform/ANFEncoder.lean`

Important SMT files:

- `deps/strata/Strata/DL/SMT/Term.lean`
- `deps/strata/Strata/DL/SMT/Solver.lean`
- `deps/strata/Strata/DL/SMT/AbstractSolver.lean`
- `deps/strata/Strata/Languages/Core/Verifier.lean`

The VCG path is mature enough to be practically interesting:

- Loops are passivized using invariant/measure obligations.
- Calls can be transformed through pre/postcondition reasoning.
- Obligations are classified using two SMT queries: `P and Q` for reachability/satisfiability and `P and not Q` for validity.
- There is both batch SMT-LIB generation and an abstract incremental solver interface.
- Solver results distinguish verified, refuted, unreachable, unknown, and bug-finding modes.

The proof story is still evolving. `ProcBodyVerifyCorrect.lean` contains substantial correctness proofs over the small-step semantics, but `CallElimCorrect.lean` is explicitly deprecated because it relied on older big-step semantics. The README also warns that Strata is under active development and may have breaking changes.

## Relevance to Go-to-Lean

Strata is relevant, but probably not as the first semantic foundation.

Strong ideas to reuse:

- Dialect and transformation organization.
- Keeping executable and relational semantics close.
- `EvalContext`-style symbolic evaluation that accumulates path conditions and proof obligations.
- SMT term/solver abstraction and two-query VC classification.
- Loop elimination shape for invariant and termination obligations.
- Explicit source metadata and diagnostic plumbing.
- The discipline that unhandled backend constructs should abort rather than silently approximate unsoundly.

Weak fit for the core Go semantics:

- Core is Boogie-like, not Go-like.
- Heap reasoning is encoded manually with maps, not provided as a native Go heap/resource model.
- Go needs executable semantics for concrete differential testing; Strata Core is optimized around verification conditions.
- Gobra permissions, predicates, fractional access, concurrency, channels, slices, maps, interfaces, panic/defer, package initialization, and Go's addressability rules would still need a Go-specific semantic layer.
- Strata's DDM and generic AST machinery may be more infrastructure than we need for the first tiny executable backend.
- The project is active and depends on `main` for `StrataDDM`, so pinning it as a foundational dependency could add churn.

## Recommendation

Use Strata as a design reference now and as a candidate library later, not as the first primary IR.

The first milestone should still be a custom Lean `GoCore` plus executable `GoM` runtime, because differential testing against actual Go execution is central. That runtime needs direct control over observable Go state: locals, heap locations, nil, panics, integer behavior, slices, maps, and eventually goroutines/channels.

Strata should remain in the plan in two concrete ways:

1. Borrow its VCG architecture: symbolic evaluation to proof obligations, loop/call transforms, SMT classification, source metadata.
2. Revisit it after the first `GoM` differential loop works, either by translating selected GoCore proof obligations into Strata Core or by depending on pieces of Strata's SMT/VC infrastructure.

The fallback rule should be: if a Strata dependency accelerates proof obligation generation without constraining Go runtime semantics, use it; if it forces Go through a Boogie-like map-heap encoding too early, keep it as reference material.

## Suggested Experiment

After the first tiny `GoM` examples work, run a narrow Strata experiment:

```text
tiny GoCore function with assignment/if/loop invariant
  -> generated Lean executable GoM definition for differential testing
  -> separate generated Strata Core obligation program for VCG/SMT
```

That experiment would answer whether Strata can be a verification backend while `GoM` remains the execution semantics.
