# Architecture

GoCore is the semantic center of the project.

The pipeline is:

```text
Go/Gobra source -> Gobra frontend/export -> Gobra JSON wire AST -> GoCore -> Lean execution/proofs
```

Gobra is useful as a mature frontend and source of typed/transformed artifacts,
but Gobra IR is not intended to be the verification language we expose or build
proof principles around. It is also not assumed to be the permanent frontend;
GoCore should be able to accept a future native Go frontend without changing
the semantics.

## Layers

- `GoLean.GobraJson`: strict wire-format decoder for Gobra's exported internal IR.
- `GoLean.GobraToIR`: lowering from Gobra-specific wire nodes into GoCore.
- `GoLean.GoCore`: clean deep embedding plus the executable semantics used by differential tests.
- `GoLean.GobraEval`: compatibility wrapper used by the CLI while Gobra JSON remains the only frontend.

## Design Rule

Frontend-specific complications should be handled in `GobraToIR`. Semantic
constructs should be added to GoCore only when they are part of Go's behavior,
not merely artifacts of Gobra's internal representation.

Gobra assertions, preconditions, postconditions, predicates, invariants, and
ghost constructs are frontend wire data. They are not executable GoCore
statements or function contracts.

See `docs/semantics.md` for the current GoCore semantics design and
`docs/roadmap.md` for the phased implementation plan. See
`docs/archive/architecture-audit.md` for the current scaling audit and refactor gates.

## Proof-layer map (layering doctrine, 2026-08-01)

Doctrine of record: `docs/2026-08-01_tcb-and-layering-doctrine.md`. The
proof layer (`proofs/`) divides into strict layers; module names and
contents in the general layers describe **Go constructs, never targets**.

```text
base defs            GoLean.GoCore.* (Syntax/Value/Machine/MachineSound; Iris-free)
  └─ machine         Steps/Step, execStmt/stepFn — the trusted relation + interpreter
       └─ general proof infra (works for ANY GoLean proof; imports NO Specs/*)
            GoLeanProofs.Lang, HeapBridge, Ghost, Lifting, Inversions,
            GoLeanProofs.Laws.* (Eval, Assign, Init, Control, Loop, Call,
              Range, Unwind, Values, StmtOps — per-construct WP laws),
            GoLeanProofs.Tactics.GoWalk (imports only Lean + Iris proof
              mode/WP — no GoCore, so it cannot name a target),
            GoLeanProofs.Adequacy,
            GoLeanProofs.NegativeSpecs (machine-level negative guardrails
              — stuck/no-panic refutations over the bare machine;
              Iris-free, no target pin — classified here at the
              2026-08-01 audit response, previously absent from this map)
       └─ surface statements (Iris-free judgment language humans read)
            GoLeanProofs.Surface (Heaplet/HProp/sat, GoTriple, Progress,
              GoInvariant, GoSpec, GoFuncSpec) + the exit pipes
              (SurfaceBridge, SurfaceExit — Iris-side, general)
            └─ target layer (rests on the general layer + surface —
                 drawn as their sibling until the 2026-08-01 audit
                 response, contradicting the direction rule below)
                 GoLeanProofs.Specs.* ONLY: program pins
                 (GoldenProgram, GoldenQuorum), pin projections +
                 witnesses (GoldenQuorumPin, and the witnesses in
                 GoldenSliceWP), target statements (GoldenTargets,
                 QuorumTargets, QuorumRefSpec, AutomationTargets), and
                 the walks/discharges (GoldenSliceWP, GoldenSurface,
                 GoldenRecover, GoldenQuorumWP, GoldenQuorumThree,
                 GoldenQuorumAll)
```

**Direction rule**: the target layer *uses* the general layer, never the
reverse. No module outside `Specs/` may import `GoLeanProofs.Specs.*`
(the root aggregator `GoLeanProofs.lean` and the gate `proofs/Audit.lean`
are structurally exempt — they import everything by design), and
`Tactics/` may not import GoCore at all. Mechanized in `scripts/ci`
("import-direction lint"), fail-closed, currently with **zero
exceptions**; laws live in `Laws/*` and witnesses live beside the pinned
programs they instantiate (`Specs/*`). The statement TCB is gated
separately: the surface-purity scan (Iris-free import chains for the
statement-bearing modules) and the statement-TCB deletion-test gate in
`proofs/Audit.lean` (no Iris constant in any designated headline
theorem's statement closure).
