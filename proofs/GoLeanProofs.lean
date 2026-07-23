import GoLeanProofs.Lang
import GoLeanProofs.HeapBridge
import GoLeanProofs.Ghost
import GoLeanProofs.Specs.GoldenProgram

/-!
# GoCore ⇒ Iris — the proof layer (root) — PRUNED at reshape S4 (2026-07-23)

LIVE through the prune: `Specs.GoldenProgram` — the golden-lowering pin
(`sliceLowered`), extracted to pure syntax at S4 so `scripts/check-golden`
stays armed while the semantics-dependent modules below are rebuilt.

RESTORED (R3, 2026-07-23): `Lang` (Config ⇒ Iris wiring — `val_stuck`
held with the identical proof over the new rules), `HeapBridge`, `Ghost`
(namespace-only ports; the heap model and state interpretation never
depended on the big-step rules).

The reshape (branch `reshape-smallstep`;
`docs/2026-07-23_reshape-r1r2-machine-design.md`, executing the F4
deletion directive in `docs/2026-07-22_f4-concurrency-model.md` §2)
deleted the big-step semantics (`ExprR`, the old `Rel.Step`, `Eval`'s
big-step cluster, `Correspondence`) that every module below consumed. The
whole proof layer is R3 scope: it is rebuilt against
`GoLean.GoCore.Machine` (fine-grained relation + iterated `stepFn`), and
this import list is the RESTORATION CHECKLIST — each module returns here
as it is re-proven, and the reshape branch does not merge until this list
is restored and the Surface statement content is byte-identical (design
note §6 merge gate).

Pruned modules (files kept on disk as the porting source; also on
`scripts/ci`'s `STANDALONE_PROOFS` allowlist until restored):

- `GoLeanProofs.Lifting` — step cores (R3: bind-form laws, `wp_atomic`)
- `GoLeanProofs.Inversions` — determinism lemmas (per-rule now)
- `GoLeanProofs.Laws.Control` / `.Assign` / `.Init` / `.Call` / `.Loop`
- `GoLeanProofs.Adequacy` — functor bundle + `go_adequacy` family
- `GoLeanProofs.Specs.Slice` / `.SliceCorrespondence` / `.GoldenSlice` /
  `.GoldenSliceWP`
- `GoLeanProofs.Surface` — Layer S (statements restored byte-identical;
  `execStmt`-shaped wrapper over iterated `stepFn`, F4 §2)
- `GoLeanProofs.SurfaceBridge` / `.SurfaceExit` /
  `.Specs.GoldenSurface` — the exit pipes and golden discharges
- `GoLeanProofs.NegativeSpecs`
-/
