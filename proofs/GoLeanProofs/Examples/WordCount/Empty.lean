import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.EmptyRun

/-!
# WordCount — Empty

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

/-- **The harness-form statement at the empty instance** (ruling
2026-08-13): the fixed harness `maxCountEmpty` — observed only through
the native entry `runFunctionWithContextM`, termination + return
value — returns exactly `maxMultiplicity []` past one fuel bound, at
EVERY choice stream. The zero-parameter degenerate of the form: the
∀-args quantifier is empty and the empty map consumes no pick; the
parameterized instances (`maxCountOne`/`maxCountFour`) are the shared
entry-glue layer's consumers (slice report, gap G1). -/
theorem wordcount_empty_ok :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
        wordCountLowered.funcs maxCountEmptyFunc #[]
        wordCountLowered.methods ch
        = .ok ⟨#[.int ((maxMultiplicity [] : Nat) : Int) .uint64]⟩ := by
  refine ⟨158, fun fuel hfuel ch => ?_⟩
  have hrun := wc_empty_run ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - 158)
  rw [show 158 + (fuel - 158) = fuel from by omega] at hfold
  have hfull : runConfig fuel
      { types := wordCountLowered.typeDefs.toList,
        functions := wordCountLowered.funcs,
        methods := wordCountLowered.methods,
        heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop))
      ch = .ok (σEmptyFin, ch) := by
    rw [hfold, runConfig_next_stop]
  have hshape : runFunctionWithContextM fuel
      wordCountLowered.typeDefs.toList wordCountLowered.funcs
      maxCountEmptyFunc #[] wordCountLowered.methods ch
      = (do
          let r ← runConfig fuel
            { types := wordCountLowered.typeDefs.toList,
              functions := wordCountLowered.funcs,
              methods := wordCountLowered.methods,
              heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)],
              nextAddr := 1 }
            (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
              (.frame [] [] [] [] .stop))
            ch
          return { values := (← loadMany r.1 [.base ⟨0⟩]).toArray }) := by
    with_unfolding_all rfl
  rw [hshape, hfull]
  with_unfolding_all rfl


end GoLean.Examples.WordCount
