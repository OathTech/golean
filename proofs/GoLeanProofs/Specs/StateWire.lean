import GoLeanProofs.Specs.TwinProgram
import GoLean.GoCore.StepFn

/-!
# The checkpoint reflector — `twinCheckpoint%` (campaign Arc 2, U2;
route memo `docs/2026-08-22_campaign-arc2-witness-route.md` §4c/§5)

The WirePin trust story at STATE scale: a term elaborator that runs the
COMPILED interpreter to a mid-run point at elaboration time and
reflects the reached `(heap, nextAddr, config, choices)` as plain
literals. The segment theorems downstream are `stepFnIter … = .ok …`
facts over `{ twinBase with heap := H, nextAddr := na }` — the
PROGRAM-GENERIC spelling (kit L4): the 9.3 MB tables appear once, in
`twinBase`, shared by every checkpoint, never re-reflected.

Trust story (unchanged from `WirePin.lean`): the emitted term is a
plain literal — no meta machinery, no IO, no interpreter call appears
in the pinned term or its type. The elaborator is scaffolding that
runs once; a WRONG literal cannot produce a false theorem, because the
kernel checks every downstream segment equation against the same
`stepFn` the statement quantifies over — a drifted checkpoint makes
the segment `rfl` FAIL, never lie. Fail-loud: any interpreter error,
fuel exhaustion, or table drift during reflection fails elaboration;
no defaults.

The `ToExpr` derives are STANDALONE (GoCore untouched — meta-side,
outside the semantic core; same as `WirePin.lean`'s).
-/

namespace GoLean.StateWire

open GoLean.GoCore GoLean.GoCore.Machine


deriving instance Lean.ToExpr for GoLean.SliceValue
deriving instance Lean.ToExpr for GoLean.MapValue
deriving instance Lean.ToExpr for GoLean.ChanValue
deriving instance Lean.ToExpr for GoLean.SyncPrim
deriving instance Lean.ToExpr for GoLean.GoValue
deriving instance Lean.ToExpr for GoLean.GoCore.HeapCell
deriving instance Lean.ToExpr for GoLean.GoCore.ChoiceSite
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.StrictOp
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.StmtOp
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.TargetStep
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.TargetShape
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.TargetRef
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.RhsOp
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.ChanStOp
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.SyncOp
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.EvClause
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.PanicEntry
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.Cont
deriving instance Lean.ToExpr for GoLean.GoCore.Machine.Config

/-- The shared table-carrying base state: the tables are the pinned
lowering's, verbatim; heap empty, allocator at 0. Every checkpoint
downstream is `{ twinBase with heap := …, nextAddr := … }`. -/
def twinBase : ExecState :=
  { types := GoLean.Examples.RaftTwin.twinLowered.typeDefs.toList
    functions := GoLean.Examples.RaftTwin.twinLowered.funcs
    methods := GoLean.Examples.RaftTwin.twinLowered.methods
    methodSets := GoLean.Examples.RaftTwin.twinLowered.methodSets }

/-- The compiled run to a checkpoint: `runProgramSetupM`'s OWN wiring
(find → arity → seed → `StateWf` → `$pkginit` → bind — zero drift from
the statement's entry), then exactly `n` subject-phase steps by
`stepFnIter`. Verifies the reached state still carries `twinBase`'s
tables (the program-generic spelling's soundness condition — `stepFn`
does not write the tables; this CHECKS it rather than assuming it) and
returns the four reflectable components. -/
def checkpointAt (n : Nat) :
    Except GoError (Heap × Nat × Config × Choices) := do
  let (c₀, s₃, _resultLocs, ch₁) ←
    runProgramSetupM 10000000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[]
  let (c', σ', ch') ← stepFnIter n s₃ c₀ ch₁
  let stripped : ExecState :=
    { σ' with heap := twinBase.heap, nextAddr := twinBase.nextAddr }
  if (stripped == twinBase) = false then
    throw (.internal "checkpointAt: tables drifted from twinBase — the program-generic spelling would be unsound; reflect refused")
  return (σ'.heap, σ'.nextAddr, c', ch')

/-- `twinCheckpoint% n` — elaborates to the literal
`(heap, nextAddr, config, choices) : Heap × Nat × Config × Choices`
reached after `n` subject-phase steps of the pinned twin (post-prelude,
`runProgramSetupM`'s wiring). Fails elaboration loudly on any
interpreter error or table drift. -/
elab "twinCheckpoint% " n:num : term => do
  match checkpointAt n.getNat with
  | .error e =>
      throwError "twinCheckpoint%: run failed: {reprStr e}"
  | .ok r => return Lean.toExpr r

end GoLean.StateWire
