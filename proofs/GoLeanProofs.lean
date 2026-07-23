import GoLeanProofs.Lang
import GoLeanProofs.HeapBridge
import GoLeanProofs.Ghost
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Loop
import GoLeanProofs.Adequacy
import GoLeanProofs.Specs.Slice
import GoLeanProofs.Specs.SliceCorrespondence
import GoLeanProofs.Specs.GoldenSlice
import GoLeanProofs.Specs.GoldenSliceWP
import GoLeanProofs.Surface
import GoLeanProofs.SurfaceBridge
import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.GoldenSurface
import GoLeanProofs.NegativeSpecs

/-!
# GoCore ⇒ Iris — the proof layer (root)

Module structure (design of record:
`docs/2026-07-20_proofs-structure-backlog.md` — four strata, one-way deps):

- **Infrastructure**: `Lang` (Config ⇒ Iris wiring), `HeapBridge` (heap model +
  `HeapWf`), `Ghost` (`GoCoreGS`, state interpretation), `Lifting` (store/alloc
  step cores), `Inversions` (determinism lemmas).
- **Laws/** — one file per construct family, law + witness co-located:
  `Control`, `Assign`, `Init`, `Call`.
- **Specs/** — one file per verified target program: `Slice`.
- **Adequacy** — functor bundle + `go_adequacy`.

The in-build gate is `Audit.lean` (a sibling default target); every module here
is in its sweep via the root import closure, which `scripts/ci` enforces.
-/
