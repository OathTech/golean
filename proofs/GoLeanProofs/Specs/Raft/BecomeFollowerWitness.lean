import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Specs.Raft.HandlerEq

/-!
# A4-U1: the discharge witness for `alt_call_span` (pinned program)

Non-vacuity (constitution §3.3): `alt_call_span` ships with every
premise discharged on a concrete state over the PINNED lowering —
`twinLowered`'s real function/method/type tables, a raft cell built
from the machine's own `defaultValue` at `raft.raft` (its `raftLog`
pointed at a default `raft.raftLog` cell so the `absRaftNode`
projection is `some`, not vacuously mismatched).

HONEST SCOPE, recorded: this state is WELL-FORMED-BY-CONSTRUCTION
(the machine's own zero values at the pinned types), not proved
REACHABLE from the seeded twin start — kernel-checking a reachable
mid-run state needs Arc-2's checkpoint-reflection machinery (its
route study measured raw kernel evaluation infeasible beyond ~10³
steps; the first `becomeFollower` call sits ~22k steps in). The
witness discharges every premise of the span lemma — the law is not
vacuous — and the reachable-state upgrade is a numbered gap in the
arc log (GAP-U1-W1), not silently claimed.

Every `rfl` below was `#eval`-checked first
(`artifacts/probe/WitnessProbe.lean` — the `#eval`-before-`decide`
rule): the 15-step run completes at `.next .stop`, the store lands.
-/

namespace GoLean.RaftSeam

open GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.Examples.RaftTwin (twinLowered)

def tyRaft : Ty := .defined ⟨"raft.raft"⟩
def tyRaftLog : Ty := .defined ⟨"raft.raftLog"⟩

/-- The pinned program's tables, no heap. -/
def wBase : ExecState :=
  { types := twinLowered.typeDefs.toList, functions := twinLowered.funcs,
    methods := twinLowered.methods, methodSets := twinLowered.methodSets }

/-- The machine's own zero value of `raft.raft`, with `raftLog`
pointed at cell 1 (so the projection chain is live). Any construction
failure collapses to `.nil`, which would fail every discharge below —
fail closed, never a silent wrong witness. -/
def wRaftVal : GoValue :=
  match defaultValue wBase tyRaft with
  | .ok (.struct tid fs) =>
      match StructFields.set fs "raftLog" (.addr (.base ⟨1⟩)) with
      | .ok fs2 => .struct tid fs2
      | .error _ => .nil
  | _ => .nil

/-- The raft-cell field array (shape-asserted by `wRaftVal_shape`). -/
def wRaftFields : Array (String × GoValue) :=
  match wRaftVal with
  | .struct _ fs => fs
  | _ => #[]

def wLogVal : GoValue := (defaultValue wBase tyRaftLog).toOption.getD .nil

/-- The witness pre-state: raft cell at 0, raftLog cell at 1. -/
def wσ : ExecState :=
  { wBase with
      heap := [(.base ⟨0⟩, ⟨some tyRaft, wRaftVal⟩),
               (.base ⟨1⟩, ⟨some tyRaftLog, wLogVal⟩)],
      nextAddr := 2 }

set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
-- L5 (kit guide §5): long concrete evaluations; the option is what
-- collapses the raw-`rfl` route on this file's window shapes.
set_option smartUnfolding false

/-- The pinned `abortLeaderTransfer` `Func` (shape-asserted below). -/
def wAltF : Func :=
  match findFunctionIn? twinLowered.funcs fidALT with
  | some f => f
  | none => { id := fidALT, args := #[], results := #[], body := .seqn #[] }

/-- The transcribed body in `HandlerEq.altBody` IS the pinned one. -/
theorem wAltF_body : wAltF.body = altBody := by
  with_unfolding_all rfl

/-- Post-frame-entry state: the param cell for `r` at address 2. -/
def wσ₁ : ExecState :=
  { wσ with
      heap := Heap.set wσ.heap (.base ⟨2⟩)
        ⟨some (.pointer tyRaft), .addr (.base ⟨0⟩)⟩,
      nextAddr := 3 }

/-- Frame entry at the pinned tables, discharged by evaluation. -/
theorem wEnter : enterFrame wσ fidALT [.addr (.base ⟨0⟩)]
    = .ok (wAltF, [[("r", .base ⟨2⟩)]], [], wσ₁) := by
  with_unfolding_all rfl

/-- The field update on the witness fields. -/
def wRaftFields' : Array (String × GoValue) :=
  (StructFields.set wRaftFields "leadTransferee"
    (.int 0 .uint64)).toOption.getD #[]

/-- The re-normalized post struct. -/
def wPostVal : GoValue :=
  (normalizeValueForTy wσ₁ tyRaft
    (.struct ⟨"raft.raft"⟩ wRaftFields')).toOption.getD .nil

/-- **THE DISCHARGE WITNESS** (constitution §3.3): `alt_call_span`
with every premise proved on the concrete pinned-program state — the
15-step run crosses the whole call and lands the field store. -/
theorem alt_call_span_witness :
    stepFnIter 15 wσ
      (.retV (.addr (.base ⟨0⟩)) (.callArgsK fidALT [] [] [] [] .stop)) []
      = .ok (.next .stop,
          { wσ₁ with heap := (Heap.set wσ₁.heap (.base ⟨0⟩)
              ⟨some tyRaft, wPostVal⟩) }, []) := by
  refine alt_call_span wσ wσ₁ ⟨0⟩ wAltF [[("r", .base ⟨2⟩)]] [] .stop []
    (fs := wRaftFields) (fs' := wRaftFields') (nv := wPostVal)
    wEnter wAltF_body ?_ ?_ ?_ ?_ ?_
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl

/-- The projection readout at the witness: `abortLeaderTransfer`
touches no projected field, so `absRaftNode` is UNCHANGED across the
call — and it is `some` (a live projection, not a vacuous `none`). -/
theorem alt_witness_projection :
    absRaftNode { wσ₁ with heap := (Heap.set wσ₁.heap (.base ⟨0⟩)
        ⟨some tyRaft, wPostVal⟩) } ⟨0⟩
      = absRaftNode wσ ⟨0⟩
    ∧ absRaftNode wσ ⟨0⟩
      = some ⟨0, 0, 0, 0, 0, 0⟩ := by
  constructor
  · with_unfolding_all rfl
  · with_unfolding_all rfl

end GoLean.RaftSeam
