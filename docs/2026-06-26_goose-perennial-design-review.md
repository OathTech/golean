# Goose and Perennial Design Review (2026-06-26)

> **Provenance.** Written 2026-06-26 in the `go-lean/` workspace root as `GOOSE_REVIEW.md`,
> outside this repository; relocated here unchanged on 2026-07-29 during a pre-wipe
> backup audit. Paths of the form `deps/…` below are relative to the workspace
> root — i.e. `../deps/…` from this repo root.

## Local Checkouts

- Goose standalone checkout: `deps/goose`
  - Commit: `3be88bbb4982f58e5813b6f0344302d5582c8e8a`
  - README says development has moved to Perennial.
- Perennial checkout: `deps/perennial`
  - Commit: `c7214070e69a5ada13858d25fde7d65ccca94814`
  - Includes an integrated `goose/` tree and the current `new/` Goose/Go semantics work.

I did not build either repository; this review is source-level.

## What Goose Is

Goose translates a selected subset of Go into Rocq definitions targeting Perennial. Its README describes the target as GooseLang: an untyped lambda calculus with references, concurrency, and special Go support. Perennial supplies the Iris-based program logic and WP rules used to verify the generated programs.

The old high-level pipeline is:

```text
Go source
  -> go/packages + go/ast + go/types
  -> Goose translator
  -> GooseLang/Rocq generated code
  -> Perennial GooseLang semantics + Iris proofs
```

Current Perennial also has a newer structure:

```text
Go source
  -> Goose
  -> New.code.* generated Rocq files
  -> New.golang.defn trusted Go semantics
  -> New.golang.theory proof rules/tactics
  -> New.generatedproof + New.manualproof
```

This newer structure is more relevant to us than the older README alone suggests.

## Translator Shape

The main standalone translator is `deps/goose/goose.go`. It uses Go's standard frontend libraries:

- `go/ast` for syntax;
- `go/types` for types;
- `golang.org/x/tools/go/packages` for package loading.

The intermediate output is represented by Go structs in `deps/goose/glang/`, especially `glang/coq.go` and `glang/types.go`, then pretty-printed to Rocq.

Generated code is not shallow Lean-like functional code. It is shallow Rocq syntax for a deeply specified language:

```coq
Definition Log__mkHdr_impl ... : val :=
  fun: "log" <>,
    exception_do (
      let: "log" := GoAlloc (go.PointerType Log) "log" in
      ...
      ![go.uint64] (StructFieldRef Log "sz"%go ...)
    ).
```

Important design details:

- Function parameters are commonly allocated into heap locations with `GoAlloc`, so local variables are addressable.
- Loads and stores go through typed instructions such as `![t] e` and `e1 <-[t] e2`.
- Struct fields are accessed through `StructFieldRef`, `StructFieldGet`, and `StructFieldSet`.
- Builtins are modeled through `FuncResolve go.len`, `FuncResolve go.append`, etc.
- Methods are modeled through `MethodResolve`.
- Control flow uses an exception-style encoding for early returns, break, continue, panic, defer, and loops.
- Goroutines translate to `Fork`.
- Channels, select, maps, slices, interfaces, and type assertions have explicit semantic support.

## Subset and Limitations

Goose is intentionally not full Go. The README emphasizes a carefully selected subset. Older documentation specifically says assignment was not supported, only bindings, though the current translator clearly has machinery for assignment into heap-backed locals and lvalues. The practical lesson is that Goose evolves by choosing proof-friendly Go idioms rather than chasing the full language surface at once.

The test corpus is useful:

- `deps/goose/testdata/examples/unittest`
- `deps/goose/testdata/examples/semantics`
- `deps/goose/testdata/examples/channel`
- generated gold files such as `*.gold.v`

The semantics test approach is especially relevant: Goose has Go tests and generated Rocq interpreter tests for functions shaped like `func test*() bool`.

## Perennial Runtime and Logic

The core language lives in `deps/perennial/src/goose_lang/lang.v`. It defines:

- values and expressions;
- heap primitives;
- `Fork`;
- prophecy operations;
- FFI hooks;
- Go-specific instructions such as `GoLoad`, `GoStore`, `GoAlloc`, `FuncResolve`, `MethodResolve`, `StructFieldRef`, `Index`, `Slice`, `SelectStmt`, etc.

`deps/perennial/src/goose_lang/lifting.v` connects the language to Iris:

- `heap_pointsto l dq v` is a fractional points-to predicate over a non-atomic heap;
- `gooseGlobalGS`, `gooseLocalGS`, and `heapGS` bundle Iris, crash, FFI, prophecy, heap, and Go package state;
- lifting lemmas provide WP rules for primitive steps.

The newer Go layer is split into:

- `deps/perennial/new/golang/defn`: trusted definitions for Go types, maps, slices, channels, loops, exceptions, package initialization, etc.
- `deps/perennial/new/golang/theory`: WP rules and proof automation for those definitions.
- `deps/perennial/new/code`: generated or trusted code models for packages.
- `deps/perennial/new/generatedproof`: generated proof scaffolding, including typed points-to instances.
- `deps/perennial/new/manualproof`: hand-written proof models.

This is a strong precedent for separating trusted definitions, generated code, generated proof scaffolding, and manual proof libraries.

## Memory Model

Goose/Perennial strongly confirms that a Go verification target needs an explicit heap/resource model.

Some important ideas:

- Locals are modeled as heap allocations when addressability matters.
- Structs are represented as Rocq records at the value level, but struct allocation expands into separately addressable field locations.
- Slices contain pointer/len/cap and use array-index address computations.
- Maps are modeled as semantic values with operations such as lookup, insert, delete, and domain.
- Channels get a substantial ghost-state/protocol model in the proof layer.
- Points-to ownership is fractional, which lines up conceptually with Gobra's permissions.

This aligns much more with Gobra than Aeneas does.

## Trusted Boundary

The trusted base is larger than Aeneas's generated shallow Lean definitions:

- Goose translator is trusted.
- GooseLang operational semantics is trusted.
- Go semantic instruction definitions are trusted.
- FFI models are trusted.
- Generated code is then verified against Iris specs.

For a Gobra-to-Lean project, we should be explicit about our own trusted boundary. If we generate shallow executable Lean over `GoM`, the generated definitions and runtime primitives form the trusted executable model; an Iris-Lean layer would provide proof rules over those same primitives.

## Lessons for Gobra-to-Lean

Transferable:

- Use an explicit heap and resource logic for Go.
- Keep local variables addressable where needed.
- Model structs as both values and field-addressable heap layouts.
- Separate generated code, trusted runtime definitions, generated proof scaffolding, and manual proof libraries.
- Use generated semantic tests comparing Go execution to proof-assistant execution.
- Preserve package/module metadata and source locations.
- Treat channels/concurrency as proof-layer heavy features, not early runtime-only features.

Not directly transferable:

- Goose targets a deep-ish untyped language in Rocq, while our intended target is shallow Lean definitions.
- Goose does not consume Gobra annotations or Gobra's internal IR.
- Goose's selected Go subset is smaller and proof-oriented; Gobra's supported language and specifications are different.
- Perennial is Rocq/Iris, so proof scripts and libraries do not port mechanically to Lean.

## Plan Impact

Goose shifts our design confidence toward:

```text
Gobra internal IR
  -> shallow Lean definitions over an executable GoM heap runtime
  -> concrete Go-vs-Lean differential testing
  -> generated proof scaffolding
  -> Iris-Lean or Iris-like resource proofs for heap permissions/concurrency
```

It also suggests a useful first validation loop:

```text
small executable Go function
  -> Go harness returns JSON
  -> generated Lean GoM harness returns JSON
  -> compare
```

and a second, later verification loop:

```text
Gobra permissions/contracts
  -> generated Lean/Iris resource specs
  -> proof obligations and generated points-to/access instances
  -> compare proof status with Gobra verifier behavior
```
