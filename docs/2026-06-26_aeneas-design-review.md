# Aeneas Design Review for Go/Gobra-to-Lean (2026-06-26)

> **Provenance.** Written 2026-06-26 in the `go-lean/` workspace root as `AENEAS_REVIEW.md`,
> outside this repository; relocated here unchanged on 2026-07-29 during a pre-wipe
> backup audit. Paths of the form `deps/…` below are relative to the workspace
> root — i.e. `../deps/…` from this repo root.

## What Aeneas Actually Does

Aeneas is an Aeneas-specific backend pipeline, not just a syntax translator:

```text
Rust source
  -> Charon LLBC
  -> Aeneas symbolic interpreter
  -> Pure AST
  -> Pure micro-passes
  -> backend extraction, especially Lean
```

The central implementation path is in `deps/aeneas/src/Translate.ml`:

- `translate_function_to_symbolics` runs symbolic interpretation on LLBC function bodies.
- `translate_function_to_pure_aux` turns symbolic ASTs into the Pure AST.
- `translate_crate_to_pure` translates types, globals, signatures, functions, traits, and trait implementations.
- `PureMicroPasses` then rewrites the generated Pure AST before extraction.

This means Aeneas is doing a real semantic functionalization pass. The generated Lean is shallow, but it is not produced by directly pretty-printing Rust.

## The Rust-Specific Trick

Aeneas depends heavily on safe Rust's ownership discipline. Mutable references can often be translated into value input/output. If a mutable borrow is returned, Aeneas returns a value plus a backward continuation that propagates the eventual update.

This is why Aeneas can avoid a general heap model for safe Rust. The borrow checker gives a strong static aliasing theorem, and Aeneas exploits that theorem during symbolic interpretation.

This does not carry over directly to Go.

## Lean Backend Shape

The Lean backend is still a strong model for us:

- `Aeneas.Std.Result` has `ok`, `fail`, and `div`.
- Runtime failures are explicit errors: assertion failure, overflow, division by zero, bounds errors, panic, undefined behavior.
- Translated functions use `do` notation over `Result`.
- WP notation, conceptually `f x <{ r => post r }>`, states successful execution with a postcondition.
- `spec_bind`, `spec_mono`, and related lemmas reason about monadic programs.
- The `step` tactic uses registered specs to discharge generated-code plumbing.
- Loops use either auxiliary recursive definitions or the `loop` combinator with invariant/measure specs.
- External functions/types are emitted as templates, then maintained by hand.
- `translation.json` connects generated Lean declarations back to source declarations.

For Go/Gobra, the target should look like this proof workflow, but with a Go-aware runtime monad rather than Aeneas's mostly heap-free `Result`.

## Why Go Needs a Heap Model

Safe Go is memory-safe in the ordinary managed-language sense, except for `unsafe`, cgo, and racy concurrent programs. However, Go does not have Rust's affine ownership discipline. Aliasing is common and observable:

```go
p := &x
q := p
*p = 1
return *q
```

Gobra's own tutorial describes it as a verifier for heap-manipulating concurrent Go programs using implicit dynamic frames, access permissions, predicates, fractional permissions, and permission transfer.

Therefore, if we want to support almost any Go code Gobra supports, we should assume:

- addresses are first-class semantic values;
- allocation and nil are observable;
- loads/stores must operate on a heap;
- structs, arrays, slices, maps, interfaces, channels, and closures all need runtime models;
- Gobra permissions need a resource logic, not just plain postconditions.

## Proposed Adaptation

The Aeneas-like architecture should be:

```text
Gobra internal IR
  -> Go-specific normalization/micro-passes
  -> shallow Lean definitions over GoM
  -> executable harnesses for differential testing
  -> WP/resource specs for verification
```

`GoM` should initially be an executable state/error monad:

```lean
abbrev GoM a := EStateM GoError GoState a
```

or a custom equivalent that can represent divergence/partiality where needed. Its state should include a typed heap and enough metadata to serialize observable test results.

Pure non-address-taking functions can still be emitted as plain Lean or as trivial `GoM` computations. Once pointers, slices, maps, channels, closures, or addressable locals appear, the heap model should be used.

## Iris-Lean Position

Iris-Lean is plausible for the proof/resource layer, especially because Gobra's native logic is already permission/resource oriented. It should not be the first execution substrate.

Recommended split:

```text
Executable layer:
  generated Lean + GoM primitives
  concrete evaluation
  Go-vs-Lean JSON differential tests

Proof layer:
  WP/spec lemmas for GoM primitives
  Gobra permissions modeled as resources
  possibly Iris-Lean for separation logic, invariants, concurrency, and channels
```

This keeps differential testing simple and computable while leaving room for Iris-style reasoning when we model Gobra's verification story.

## Existing Go-to-Lean Backend Search

A subagent search found no mature direct Go-to-Lean backend. The relevant precedents are:

- Gobra itself as the Go/Gobra frontend and Viper encoder.
- Aeneas as the Rust-to-Lean backend design reference.
- Goose/Perennial as the closest Go verification precedent, but in Coq/Iris rather than Lean.
- Go SSA as an alternate frontend, but it would lose Gobra annotations and specs.
- Viper/Silver as a possible Lean target, but that would reason about Gobra's encoding rather than Go.

The primary path remains Gobra internal IR to Lean, with Viper output retained as a debugging and verifier-comparison artifact.
