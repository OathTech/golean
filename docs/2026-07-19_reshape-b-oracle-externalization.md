# Reshape B — oracle externalization (2026-07-19)

Goal (master plan §8, task #18): the state type shared by the relation, the
interpreter's correspondence, and the proof layer must be **oracle-free**, so
that a relation step (which never touches the nondeterminism oracle) and an
interpreter step relate on the same `ExecState`. Today `ExecState.choices : List
Nat` (the "parser of randomness") lives inside the compared state, so once the
interpreter consumes a choice, its state diverges from the relation's — the
correspondence goes false (master plan §8 C1). Fix: move `choices` out of
`ExecState` into an **external stream** the interpreter threads explicitly.

## Footprint (measured, not assumed)

`ExecState.choices` is consumed at **exactly two sites**, both statement-level:

- `execAppendSlice` (Eval.lean ~620) — post-reallocation slice capacity.
- `execMapRangeLoop` (Eval.lean ~825) — map iteration order.

The ~30-function **expression cluster** (`evalExpr` and friends, first mutual
block) never consumes. The **relation** (`Rel.lean`) and **proof layer**
(`GoLeanProofs.lean`) never reference `choices` at all (verified by grep). So:

- Interpreter churn is confined to the **statement cluster** (`execStmt`,
  `execStmts`, `execStmtList`, `execMapRangeLoop`, `execFunctionWithValues`,
  `execFunctionCallWithLocs`, `execFunctionCall`) **plus** `execAppendSlice` —
  ~8 functions get the stream threaded in and the remainder returned.
- `Rel.lean` / `Correspondence.lean` / `GoLeanProofs.lean` need **zero** changes
  from dropping the field (it was dead weight there).

## Decision: localized statement-cluster threading

Rejected alternatives:

- **Whole-interpreter monad refactor** (`StateT (ExecState × List Nat)`): a large,
  risky rewrite of an explicit-threaded `partial` interpreter for no benefit —
  the expression layer doesn't consume, so it shouldn't pay.
- **`RtState` projection** (keep `choices` in the interpreter's `ExecState`,
  introduce an oracle-free `RtState` for the relation/proofs): moves the churn to
  `Rel.lean`+proofs instead, and hits Lean structure-inheritance method-
  resolution friction (`(e : ExecState).alloc` won't auto-find `RtState.alloc`).

Chosen: `choices` leaves `ExecState` entirely. `ExecState.consume` becomes a
standalone `Choices.consume : List Nat → Nat → Nat × List Nat`. The statement
cluster threads `List Nat` as an explicit parameter and returns the remainder
alongside its result; entry points (`runFunctionWithContext` …) seed the stream.
A single stream threaded through calls reproduces today's global-`choices`
semantics exactly (callee consumes from and returns to the shared stream).

## Slices

1. **Oracle externalization** (this doc's core). Drop `choices` from `ExecState`;
   thread it through the statement cluster + `execAppendSlice`; seed at entry.
   **Validation gate:** `lake build` + `lake exe gocore-eval-tests` + the focused
   differential slice — the failing-case-id set must be **identical** to the
   baseline (a pure refactor; behavior on `choices := []` and on explicit choice
   streams is preserved). Any new red is a regression to investigate before
   commit.
2. **Existential `mapRange` rule** in `Rel.lean`: a rule that relates a map-range
   loop to *any* iteration order (the relation over-approximates; the interpreter
   instantiates via the external stream). Validation: proofs build.
3. **Correspondence for `mapRange`**: the interpreter's oracle-instantiated
   iteration is one projection of the existential rule. Validation: proofs build;
   the correspondence lemma holds on the now oracle-free `ExecState`.

Slice 1 lands first and is validated on the differential corpus before 2/3
(which are proof-facing and don't touch the interpreter).

## Why this unblocks interpreter totalization

The paused big-step `execStmt` totalization (task #14) was deferred because its
correspondence goes false once `mapRange` runs with the oracle in state. With
`choices` external, `mapRange`'s interpreter step and the existential relation
rule compare on the same oracle-free `ExecState`, so the correspondence is
statable — totalization can resume against the corrected shape.
