import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.CanonRun

/-!
# WordCount — EmptyRun

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The harness form (statement-form ruling 2026-08-13)

The user-facing statement shape: a fixed Go HARNESS function — setup
phase builds the memory from scalar parameters, the call under test,
test phase folds the verdict into return values — observed ONLY through
`runFunctionWithContextM` termination + return values, quantified over
the `GoValue` arguments. The pinned lowering carries three such
harnesses (`maxCountEmpty`/`maxCountOne`/`maxCountFour`). This module
ships the form at `maxCountEmpty` (the zero-parameter instance — the
run is address-concrete throughout, so no shared entry-glue is needed);
the parameterized instances consume the shared harness entry-glue layer
plus this module's placement-generic inductions (`wc_range_loop` is
already placement-generic in `B`/`na`/`tail`; the address-CONCRETE defs
`frontC`/`envB`/`frameK` are the re-parameterization point — see the
slice report). -/

/-- The `maxCountEmpty` harness's `Func` record, verbatim from the
pinned lowering (the `example` pin ties it by `rfl`): setup builds an
empty `[]uint64`, the call under test runs `maxCount`, the result
returns. -/
def maxCountEmptyFunc : Func :=
  { id := { key := "maxCountEmpty" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "$c7", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c7") (.int .uint64) (.intLit 0 .int)
              (some (.intLit 0 .int))],
        .seqn
          #[.initialization { id := "$c8", typ := .int .uint64 },
            .call #[.var "$c8"] { key := "maxCount" } #[.var "$c7"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c8"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

example : findFunctionIn? wordCountLowered.funcs ⟨"maxCountEmpty"⟩
    = some maxCountEmptyFunc := rfl

/-- The harness run's terminal state (probe-pinned; re-checked by the
`rfl` below). -/
def σEmptyFin : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [
      (.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩),
      (.base ⟨1⟩, ⟨some (.slice tU64), .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩⟩),
      (.base ⟨2⟩, ⟨some (.array 0 tU64), .array #[]⟩),
      (.base ⟨3⟩, ⟨some tU64, .int 0 .uint64⟩),
      (.base ⟨4⟩, ⟨some (.slice tU64), .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩⟩),
      (.base ⟨5⟩, ⟨some tU64, .int 0 .uint64⟩),
      (.base ⟨6⟩, ⟨some tMap, .map ⟨some (.base ⟨7⟩)⟩⟩),
      (.base ⟨7⟩, ⟨none, .mapData #[]⟩),
      (.base ⟨8⟩, ⟨some tMap, .map ⟨some (.base ⟨7⟩)⟩⟩),
      (.base ⟨9⟩, ⟨some (.int .int), .int 0 .int⟩),
      (.base ⟨10⟩, ⟨some .bool, .bool false⟩),
      (.base ⟨11⟩, ⟨some tU64, .int 0 .uint64⟩)],
    nextAddr := 12 }

set_option maxHeartbeats 12000000 in
/-- The whole harness run at the empty-map instance: 158 steps, every
address concrete, NO choice consumed (an empty snapshot picks
nothing) — the stream rides through untouched. -/
theorem wc_empty_run (ch : Choices) :
    stepFnIter 158
      { types := wordCountLowered.typeDefs.toList,
        functions := wordCountLowered.funcs,
        methods := wordCountLowered.methods,
        heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop))
      ch
      = .ok (.next .stop, σEmptyFin, ch) := by
  with_unfolding_all rfl


end GoLean.Examples.WordCount
