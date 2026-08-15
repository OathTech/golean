import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Examples.WordCount.Machine
import GoLeanProofs.Examples.WordCount.Pure

/-!
# WordCount — EmptyRun

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). The user-facing headline theorems live in
the thin root module `GoLeanProofs.Examples.WordCount`; the module
docstring there records the example's design.

## The program-generic run (slice 1.5, 2026-08-14)

`wc_empty_run`'s STATEMENT is byte-identical to the pre-split module —
**CHECKED, not asserted** (C-M5, 2026-08-15): every line from `theorem
wc_empty_run (ch : Choices) :` through `= .ok (.next .stop, σEmptyFin,
ch)` matches `6256228d^` exactly. Only the proof differs, and only past
the `:=` — which is why `artifacts/g4/verbatim-check.py`, comparing
whole declaration BLOCKS (statement plus proof), lists this name as
differing: the old block ended `:= by`, this one delegates to
`wc_empty_run_generic`. The proof was restated after the slice-1
blocker measurement: the
original single 158-step `with_unfolding_all rfl` made the kernel whnf
concrete configurations whose `ExecState` embeds the WHOLE pinned
program (`wordCountLowered.funcs`), costing 82 s / 50.8 GiB alone and
growing superlinearly with the corpus program (+1 harness function →
~77 GiB, past the 64G cap — the slice-1 record has both measurements).

The restatement is the E-form taken one step further — PROGRAM-generic,
not just placement-generic: every segment is stated over an abstract
`σ : ExecState` with only `heap`/`nextAddr` pinned concrete
(`{ σ with heap := …, nextAddr := … }`), so the unifier and kernel only
ever see 12-cell heaps and never a program-embedding state. The single
step that genuinely consults the program — the `maxCount` frame entry —
is conditioned on its `enterFrame` fact (`wc_empty_enterFrame_step`),
discharged ONCE by `rfl` at the concrete instantiation. Measured effect:
1.9 GiB / ~86 s for this whole shard (was 50.8 GiB), and the cost no
longer grows with the corpus program. Same-file worked template for the
parameterized instances (`maxCountOne`/`maxCountFour`); technique
recorded in `docs/2026-08-14_phase2-slice1-spec-swaps.md` and the
StepKit module docstring.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

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
composition below). -/
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

/-! ## Phase-boundary vocabulary (probe-pinned, 2026-08-14)

The three heap fronts of the empty run — after the harness prelude
(4 cells), after `maxCount`'s frame entry (6 cells), and terminal
(12 cells, `σEmptyFin.heap` verbatim) — plus the environments and
continuations at the two internal boundaries. All addresses concrete;
the program context stays abstract throughout. -/

/-- Heap after the harness prelude (`$c7` slice made, `$c8` declared):
step 20 of the run. -/
private def wcE_heapA : Heap :=
  [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩),
   (.base ⟨1⟩, ⟨some (.slice tU64), .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩⟩),
   (.base ⟨2⟩, ⟨some (.array 0 tU64), .array #[]⟩),
   (.base ⟨3⟩, ⟨some tU64, .int 0 .uint64⟩)]

/-- Heap after `maxCount`'s frame entry (`words` param at 4, `$res0`
result at 5): step 21. -/
private def wcE_heapB : Heap :=
  wcE_heapA ++
  [(.base ⟨4⟩, ⟨some (.slice tU64), .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩⟩),
   (.base ⟨5⟩, ⟨some tU64, .int 0 .uint64⟩)]

/-- The terminal heap — `σEmptyFin.heap`, verbatim (the composition's
final state is `{ σ with heap := wcE_heapFin, nextAddr := 12 }`, which
is definitionally `σEmptyFin` at the concrete instantiation). -/
private def wcE_heapFin : Heap :=
  [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩),
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
   (.base ⟨11⟩, ⟨some tU64, .int 0 .uint64⟩)]

/-- The harness frame's environment after the prelude. -/
private def wcE_env : LocalEnv :=
  [[("$c8", .base ⟨3⟩), ("$c7", .base ⟨1⟩)], [("$res0", .base ⟨0⟩)]]

/-- The continuation below the call: the harness tail (`$res0 := $c8;
return`) under the outer frame. -/
private def wcE_tailK : Cont :=
  .seq [.seqn #[.assign (.var "$res0") (.var "$c8"), .returnStmt]] wcE_env
    (.frame [] [] [] [] .stop)

/-- The call's caller-target plan (`$c8` receives the result). -/
private def wcE_plans : List (TargetShape × List Expr) := [(.chain [], [.ref "$c8"])]

/-- The empty slice `$c7` passes to `maxCount`. -/
private def wcE_sliceV : GoValue := .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩

/-- `maxCount`'s frame environment (`$res0` at 5, `words` at 4). -/
private def wcE_frameEnv : LocalEnv := [[("$res0", .base ⟨5⟩), ("words", .base ⟨4⟩)]]

/-! ## The program-generic segments

Stated over an abstract `σ : ExecState` with only `heap`/`nextAddr`
pinned — the storm-diagnosis rule extended from placement-generic to
PROGRAM-generic: `stepFn` reduces definitionally through every step that
does not consult `σ.types`/`σ.functions`/`σ.methods` (all
`defaultValue`/`normalizeValueForTy` uses here are at structural types,
and the empty snapshot's self-normalization check is vacuous), so the
kernel only ever whnf's small concrete heaps. -/

/-- Segment 1: the harness prelude — `$c7 := make([]uint64, 0)`, `$c8`
declared, the call's argument evaluated. 20 steps, program-free. -/
private theorem wc_empty_seg1 (σ : ExecState) (ch : Choices) :
    stepFnIter 20
      { σ with heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop)) ch
      = .ok (.retV wcE_sliceV
          (.callArgsK ⟨"maxCount"⟩ wcE_plans [] [] wcE_env wcE_tailK),
        { σ with heap := wcE_heapA, nextAddr := 4 }, ch) := by
  with_unfolding_all rfl

/-- The conditioned frame-entry step: a `.retV` at a drained
`callArgsK` is exactly one `enterFrame`, keyed on its result. PROMOTED
to `StepKit.stepFn_call_enter` (phase-2 slice 1) when its second
consumer landed — the `reverse_harness_v` entry into `reverse`. This
module is one of the promotion's two fixture witnesses; the abbreviation
below keeps the local name a one-liner over the kit lemma. -/
private theorem wc_empty_enterFrame_step {σ σ' : ExecState} {fid : FuncId}
    {v : GoValue} {vals : List GoValue}
    {plans : List (TargetShape × List Expr)} {env : LocalEnv} {k : Cont}
    {ch : Choices} {func : Func} {frameEnv : LocalEnv} {locs : List Loc}
    (h : enterFrame σ fid (vals ++ [v]) = .ok (func, frameEnv, locs, σ')) :
    stepFn σ (.retV v (.callArgsK fid plans vals [] env k)) ch
      = .ok (.exec func.body frameEnv
          (.frame plans env locs [] k func.wrapper), σ', ch) :=
  stepFn_call_enter h

set_option maxHeartbeats 12000000 in
/-- Segment 2: the whole `maxCount` body on the empty slice (zero
counting iterations, empty-map snapshot picks nothing), the frame exit
into `$c8`, and the harness tail through `return`. 137 steps,
program-free given the entry. -/
private theorem wc_empty_seg2 (σ : ExecState) (ch : Choices) :
    stepFnIter 137 { σ with heap := wcE_heapB, nextAddr := 6 }
      (.exec maxCountFunc.body wcE_frameEnv
        (.frame wcE_plans wcE_env [.base ⟨5⟩] [] wcE_tailK)) ch
      = .ok (.next .stop,
        { σ with heap := wcE_heapFin, nextAddr := 12 }, ch) := by
  with_unfolding_all rfl

/-- The whole 158-step empty run, program-generic: the ONLY fact about
the program context is the `enterFrame` hypothesis. -/
private theorem wc_empty_run_generic (σ : ExecState) (ch : Choices)
    (henter : enterFrame { σ with heap := wcE_heapA, nextAddr := 4 }
        ⟨"maxCount"⟩ [wcE_sliceV]
      = .ok (maxCountFunc, wcE_frameEnv, [.base ⟨5⟩],
          { σ with heap := wcE_heapB, nextAddr := 6 })) :
    stepFnIter 158
      { σ with heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop)) ch
      = .ok (.next .stop,
        { σ with heap := wcE_heapFin, nextAddr := 12 }, ch) :=
  stepFnIter_chain
    (stepFnIter_chain (wc_empty_seg1 σ ch)
      (stepFnIter_one (wc_empty_enterFrame_step henter)))
    (wc_empty_seg2 σ ch)

/-- The whole harness run at the empty-map instance: 158 steps, every
address concrete, NO choice consumed (an empty snapshot picks
nothing) — the stream rides through untouched. Statement byte-identical
to the original monolithic-`rfl` form; the proof instantiates the
program-generic composition above, discharging the one `enterFrame`
fact by `rfl` (the only place the pinned program is ever unfolded, and
`maxCount` is the funcs array's head). -/
theorem wc_empty_run (ch : Choices) :
    stepFnIter 158
      { types := wordCountLowered.typeDefs.toList,
        functions := wordCountLowered.funcs,
        methods := wordCountLowered.methods,
        heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop))
      ch
      = .ok (.next .stop, σEmptyFin, ch) :=
  wc_empty_run_generic
    { types := wordCountLowered.typeDefs.toList,
      functions := wordCountLowered.funcs,
      methods := wordCountLowered.methods,
      heap := [], nextAddr := 0 } ch
    (by with_unfolding_all rfl)


end GoLean.Examples.WordCount
