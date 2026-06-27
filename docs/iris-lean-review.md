# Iris-Lean Review

Reference checkout:

```text
../deps/iris-lean
```

Repository:

```text
https://github.com/leanprover-community/iris-lean
```

Revision reviewed:

```text
3877dbe feat: port `bi/monpred.v` (MonPred BI) (#481)
```

## Current Status

Iris-Lean is an active Lean 4 port of Iris. The repository provides:

- MoSeL-style proof mode and tactics;
- the BI interface and derived laws;
- `UPred` and `IProp`;
- a selection of Iris resource algebras;
- invariants, fancy updates, later credits, and generalized heap resources;
- an Iris `ProgramLogic` layer with language, primitive-step, weakest
  precondition, lifting, and adequacy infrastructure;
- a HeapLang port with syntax, relational operational semantics, primitive
  laws, and proof-mode support.

The package is split into `Iris/` and `IrisMath/` subprojects. The core `Iris`
Lake package currently uses Lean `v4.31.0`; this project currently uses
`v4.29.1`. Direct dependency integration will require aligning Lean versions or
pinning an Iris-Lean release compatible with our toolchain.

## Relevant Shape

The most important interface is `Iris.ProgramLogic.Language`:

```lean
class ToVal (Expr : Type _) (Val : outParam (Type _)) where
  toVal : Expr -> Option Val
  ofVal : Val -> Expr

class PrimStep (Expr : Type _) (State : outParam (Type _)) (Obs : outParam (Type _)) where
  primStep : Expr × State -> Obs -> Expr × State × List Expr -> Prop

class Language (Expr State Obs Val) extends
    PrimStep Expr State (List Obs), ToVal Expr Val where
  val_stuck : ...
```

Weakest preconditions are defined over this relational `primStep`, not over an
interpreter function. The WP state interpretation has shape:

```lean
stateInterp : State -> Nat -> List Obs -> Nat -> IProp GF
```

So an Iris-compatible GoCore should eventually provide:

- `Expr`: a step-level GoCore expression/statement/control term;
- `Val`: GoCore values;
- `State`: GoCore execution state;
- `Obs`: observations for panics, external events, or concurrency events;
- `PrimStep`: a relational transition system.

Our executable evaluator should be treated as a test runner for deterministic
concrete runs, then related to this relational semantics.

## Heap And Resources

`Iris.BI.Lib.GenHeap` is directly relevant. It provides generalized heap
ownership:

```lean
pointsTo (l : L) (dq : DFrac) (v : V) : IProp GF
genHeapInterp σ
```

and allocation/update lemmas. This is a good target for GoCore heap ownership:

- `Loc` can be the heap key type;
- `GoValue` can be the heap value type;
- path-like `Loc.field` and `Loc.index` fit the generalized heap interface if
  they have decidable equality/order support where required.

This supports the current direction of using explicit GoCore locations rather
than encoding heap behavior inside Gobra-specific assertions.

## HeapLang Lessons

Iris-Lean's HeapLang is not a Go model, but its structure is useful:

- syntax and values are separate;
- values are recognized by `toVal`;
- reduction is an inductive `BaseStep` relation;
- evaluation context machinery lifts base steps to full primitive steps;
- primitive load/store/CAS laws are proved over WP;
- executable evaluation is not the semantic authority.

For GoCore, we do not need to mirror HeapLang exactly. Go has statements,
multi-result calls, panics, `defer`, goroutines, and Go-specific assignment
sequencing. But the Iris-compatible direction is clear: define GoCore's
relation in small enough steps that WP/lifting lemmas can target individual
semantic primitives.

## Design Implications

- Keep `GoCore` syntax independent from the interpreter implementation.
- Keep `GoValue`, `Loc`, `ExecState`, `GoError`, and `ExecOutcome` reusable by
  a future relational semantics.
- Avoid adding semantics only as recursive evaluator code. Every feature should
  have an obvious future rule shape.
- Treat panics and stuckness carefully: Iris already distinguishes reducibility,
  values, and stuck states. Go panics are program behavior; semantic `stuck`
  should remain an implementation/modeling gap.
- Consider whether GoCore should eventually be expressed as a small-step
  statement/control language rather than only as big-step statement execution.
  Small-step is a closer fit to Iris `PrimStep`, concurrency, `defer`, and
  observations.

## Near-Term Recommendation

Do not add Iris-Lean as a project dependency yet. Keep it checked out as a
reference while the executable differential harness matures.

Before dependency integration:

- align Lean versions or select a compatible Iris-Lean release;
- define a minimal relational GoCore step relation for the existing scalar,
  heap-local, struct, array, and call subset;
- prove or test a correspondence theorem shape between the evaluator and the
  relation for terminating deterministic runs;
- prototype a `genHeap` interpretation of `ExecState.heap` keyed by GoCore
  `Loc`.

The current hardening changes are consistent with this direction: typed errors,
explicit outcomes, location-based memory, and assignment sequencing all make the
future relation cleaner.
