import GoLeanProofs.Lang
import GoLeanProofs.LangC
import GoLeanProofs.LangD
import GoLeanProofs.HeapBridge
import GoLeanProofs.Ghost
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Loop
import GoLeanProofs.Laws.Range
import GoLeanProofs.Laws.Values
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Adequacy
import GoLeanProofs.Specs.GoldenProgram
import GoLeanProofs.Specs.GoldenTargets
import GoLeanProofs.Specs.GoldenSliceWP
import GoLeanProofs.Surface
import GoLeanProofs.SurfaceBridge
import GoLeanProofs.SurfaceExit
import GoLeanProofs.Specs.GoldenSurface
import GoLeanProofs.Specs.GoldenRecover
import GoLeanProofs.Specs.GoldenQuorum
import GoLeanProofs.Specs.GoldenQuorumPin
import GoLeanProofs.Specs.QuorumTargets
import GoLeanProofs.Specs.QuorumRefSpec
import GoLeanProofs.Specs.Statements
import GoLeanProofs.Specs.GoldenQuorumWP
import GoLeanProofs.Specs.AutomationTargets
import GoLeanProofs.Specs.GoldenQuorumThree
import GoLeanProofs.Specs.GoldenQuorumAll
import GoLeanProofs.Specs.TotalPins
import GoLeanProofs.Specs.ForkJoinTargets
import GoLeanProofs.Specs.GoldenForkJoin
import GoLeanProofs.Specs.GoldenSelectDone
import GoLeanProofs.Specs.ImportedGooseBlock
import GoLeanProofs.Specs.ImportedGooseDefer
import GoLeanProofs.Specs.ImportedGooseNil
import GoLeanProofs.Specs.ImportedGooseNew
import GoLeanProofs.Specs.ImportedGooseVars
import GoLeanProofs.Specs.ImportedGooseSelectTricky
import GoLeanProofs.Specs.ImportedGooseMuxer
import GoLeanProofs.Specs.ImportedGooseActris
import GoLeanProofs.Specs.GooseParityKit
import GoLeanProofs.Specs.GooseParityNilWP
import GoLeanProofs.Specs.GooseParityBlockWP
import GoLeanProofs.Specs.GooseParityNewWP
import GoLeanProofs.Specs.GooseParityVarsWP
import GoLeanProofs.Specs.GooseParityChannels
import GoLeanProofs.Specs.ImportedGooseMapliteral
import GoLeanProofs.Specs.ImportedGooseConst
import GoLeanProofs.Specs.ImportedGooseRune
import GoLeanProofs.NegativeSpecs

/-!
# GoCore ⇒ Iris — the proof layer (root)

R3 REBUILD COMPLETE (2026-07-23, branch `reshape-smallstep`;
`docs/2026-07-23_reshape-r1r2-machine-design.md`): every stratum restored
over the fine-grained machine.

- **Infrastructure**: `Lang` (Config ⇒ Iris wiring), `HeapBridge`,
  `Ghost` (state interpretation, now pinning functions AND methods),
  `Lifting` (the four rule-agnostic step cores), `Inversions` (ONE
  generic `step_det` replaces the old per-form inversion family).
- **Laws/** — `Control` and `Init` (rules survived the reshape verbatim);
  NEW `Eval` (the expression-walk step laws — the machine's answer to
  `wp_bind`); `Assign`, `Call`, `Loop` rewritten as composed walks, each
  with same-commit witnesses (`wp_assign_lit`, the golden frame-entry
  instances, `wp_while_eq_once`).
- **Specs/** — `GoldenProgram` (the pure-syntax frontend pin),
  `GoldenSliceWP` (the golden walk: body lemmas + `wp_goldenCall`(/`_inv`)
  + `wp_goldenDriver`), `GoldenSurface` (all six step-0 targets
  re-proven).
- **Surface** stack — Layer S over the `execStmt`-shaped wrapper (two
  recorded statement deltas, both strengthenings: env as a wrapper
  argument after `ExecState.locals` died; the `HeapFrag` fragment
  side-condition retired because machine soundness is total),
  `SurfaceBridge` (untouched), `SurfaceExit` (fragment shape checks
  gone).
- `NegativeSpecs` — trivialization guards over the machine.

RETIRED at R3 (files deleted; the deleted content remains at git rev
5a9eab2 and in `Audit.lean`'s historical ledger): `Specs.Slice` and
`Specs.SliceCorrespondence` (the hand-model slice and its fragment-scoped
interpreter⇄relation bridge — superseded by the golden pipeline and the
total `stepFn_sound`/`step_complete`/`runConfig_sound`), `Specs.GoldenSlice`
(pin moved to `GoldenProgram`; walk rewritten in `GoldenSliceWP`; the
existential-address `*_computes` readouts superseded by the Surface
pinned forms).

The in-build gate is `Audit.lean` (a sibling default target); every module
here is in its sweep via the root import closure, which `scripts/ci`
enforces.
-/
