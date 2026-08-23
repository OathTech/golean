import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.FastEval.Heap
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

/-! ## The TRIE-form emitter (campaign Arc 2 U4, route (d)) -/

deriving instance Lean.ToExpr for GoLean.FastEval.HeapT

/-- Compiled list→trie conversion for reflection (scaffolding only —
a wrong conversion fails the downstream kernel checks, never lies:
the segment sims and the `γF σF₀ = s₃` equality are checked over the
emitted literal). -/
def trieOfHeap (h : Heap) : GoLean.FastEval.HeapT :=
  h.foldl
    (fun t e =>
      match e with
      | (.base a, cell) => t.set a.id cell
      | _ => t)
    .leaf

/-- `twinCheckpointF% n` — the trie-form checkpoint: elaborates to the
literal `(heapT, nextAddr, config, choices)` reached after `n`
subject-phase steps, with the heap converted to the FastEval trie at
reflection time. Fail-loud as `twinCheckpoint%`. -/
elab "twinCheckpointF% " n:num : term => do
  match checkpointAt n.getNat with
  | .error e =>
      throwError "twinCheckpointF%: run failed: {reprStr e}"
  | .ok (h, na, c, ch) =>
      return Lean.toExpr (trieOfHeap h, na, c, ch)

/-- The full post-prelude tuple, trie form: `(c₀, heapT, nextAddr,
resultLocs, ch₁)` from `runProgramSetupM`'s own wiring (zero drift —
it IS that call). Table-drift-checked like `checkpointAt`. -/
def preludeF :
    Except GoError (Config × GoLean.FastEval.HeapT × Nat × List Loc × Choices) := do
  let (c₀, s₃, resultLocs, ch₁) ←
    runProgramSetupM 10000000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[]
  let stripped : ExecState :=
    { s₃ with heap := twinBase.heap, nextAddr := twinBase.nextAddr }
  if (stripped == twinBase) = false then
    throw (.internal "preludeF: tables drifted from twinBase; reflect refused")
  return (c₀, trieOfHeap s₃.heap, s₃.nextAddr, resultLocs, ch₁)

/-- `twinPreludeF%` — the reflected post-prelude tuple. Fail-loud. -/
elab "twinPreludeF%" : term => do
  match preludeF with
  | .error e => throwError "twinPreludeF%: run failed: {reprStr e}"
  | .ok r => return Lean.toExpr r

/-! ## The BATCH emitter (campaign Arc 2, U5 — the one-compiled-pass
lever, memo §6.8 item 1) -/

/-- One compiled pass over the subject phase, reflecting the trie-form
tuple at each ascending index — the U5 batch lever: per-index reruns of
the prelude + prefix are replaced by incremental continuation from the
previous index. Fail-loud and table-drift-checked at EVERY checkpoint,
exactly as `checkpointAt`. -/
def checkpointsAt (ns : List Nat) :
    Except GoError
      (List (Nat × (GoLean.FastEval.HeapT × Nat × Config × Choices))) := do
  let (c₀, s₃, _resultLocs, ch₁) ←
    runProgramSetupM 10000000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[]
  let mut cur : Nat := 0
  let mut σ := s₃
  let mut c := c₀
  let mut ch := ch₁
  let mut acc :
      Array (Nat × (GoLean.FastEval.HeapT × Nat × Config × Choices)) := #[]
  for n in ns do
    if n < cur then
      throw (.internal
        s!"checkpointsAt: indices must be ascending ({n} after {cur})")
    let (c', σ', ch') ← stepFnIter (n - cur) σ c ch
    let stripped : ExecState :=
      { σ' with heap := twinBase.heap, nextAddr := twinBase.nextAddr }
    if (stripped == twinBase) = false then
      throw (.internal
        s!"checkpointsAt: tables drifted from twinBase at index {n}; reflect refused")
    acc := acc.push (n, (trieOfHeap σ'.heap, σ'.nextAddr, c', ch'))
    cur := n; σ := σ'; c := c'; ch := ch'
  return acc.toList

open Lean Lean.Elab Lean.Elab.Command in
/-- `twin_ckpt_groupF% ckptF [n₁, n₂, …]` — defines
`ckptF_<nᵢ> : HeapT × Nat × Config × Choices` (current namespace) for
each ascending subject-step index, all from ONE compiled incremental
pass. Fail-loud: interpreter error, table drift, or non-ascending
indices fail elaboration; no defaults. The emitted literals are
scaffolding with `twinCheckpointF%`'s exact trust story — every
downstream segment equation is kernel-checked against them, so a
drifted literal fails a proof, never lies. Declarations are added
WITHOUT compiled code (their only consumers are kernel checks). -/
elab "twin_ckpt_groupF% " pre:ident " [" ns:num,* "]" : command => do
  let idxs := (ns.getElems.map (fun n => n.getNat)).toList
  match checkpointsAt idxs with
  | .error e => throwError "twin_ckpt_groupF%: run failed: {reprStr e}"
  | .ok rs =>
      liftTermElabM do
        let nsCur ← getCurrNamespace
        for (n, r) in rs do
          let nm := nsCur ++ pre.getId.appendAfter s!"_{n}"
          let val := Lean.toExpr r
          let typ ← Lean.Meta.inferType val
          Lean.addDecl (.defnDecl {
            name := nm, levelParams := [], type := typ, value := val,
            hints := .abbrev, safety := .safe })

end GoLean.StateWire
