# Architecture

GoCore is the semantic center of the project.

The pipeline is:

```text
Go/Gobra source -> Gobra frontend/export -> Gobra JSON wire AST -> GoCore -> Lean execution/proofs
```

Gobra is useful as a mature frontend and source of typed/transformed artifacts,
but Gobra IR is not intended to be the verification language we expose or build
proof principles around.

## Layers

- `GoLean.GobraJson`: strict wire-format decoder for Gobra's exported internal IR.
- `GoLean.GobraToIR`: lowering from Gobra-specific wire nodes into GoCore.
- `GoLean.GoCore`: clean deep embedding plus the executable semantics used by differential tests.
- `GoLean.GobraEval`: compatibility wrapper used by the CLI while Gobra JSON remains the only frontend.

## Design Rule

Frontend-specific complications should be handled in `GobraToIR`. Semantic
constructs should be added to GoCore only when they are part of Go's behavior,
not merely artifacts of Gobra's internal representation.

See `docs/semantics.md` for the current GoCore semantics design.
