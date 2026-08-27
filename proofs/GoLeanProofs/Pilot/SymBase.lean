import GoLeanProofs.Sym.TableExt
import GoLeanProofs.Specs.TwinProgram

/-!
# W1 pilot scaffolding: the symbolic embedding base

HARVESTED at the W1 pilot (2026-08-27) from branch `campaign-arc4d`
(`BecomeFollowerWitness.lean`: the pinned tables `wBase` and the
machine's own zero raft/raftLog values; `HandlerEqSym.lean`: the
concrete→symbolic embedding `embedGo`, the field-override
`setSymField`, and the pinned table pack `bfTB`). Verbatim content,
trimmed to the defs the Leg-A chain consumes (the alt/abort pilot
material and the deleted-era witnesses are NOT resurrected).

STATUS: proof-body scaffolding for the pilot Leg A `CallSpec`.
Retirement condition: superseded by W3's regenerated fixtures at the
transport-compliant layout (design note §3 finding 3).
-/

namespace GoLean.RaftSeam

open GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
open GoLean.Examples.RaftTwin (twinLowered)

def tyRaft : Ty := .defined ⟨"raft.raft"⟩
def tyRaftLog : Ty := .defined ⟨"raft.raftLog"⟩

/-- The pinned program's tables, no heap. -/
def wBase : ExecState :=
  { types := twinLowered.typeDefs.toList, functions := twinLowered.funcs,
    methods := twinLowered.methods, methodSets := twinLowered.methodSets }

/-- The machine's own zero value of `raft.raft`, with `raftLog`
pointed at cell 1 (so the projection chain is live). Any construction
failure collapses to `.nil`, which would fail every discharge —
fail closed, never a silent wrong fixture. -/
def wRaftVal : GoValue :=
  match defaultValue wBase tyRaft with
  | .ok (.struct tid fs) =>
      match StructFields.set fs "raftLog" (.addr (.base ⟨1⟩)) with
      | .ok fs2 => .struct tid fs2
      | .error _ => .nil
  | _ => .nil

def wLogVal : GoValue := (defaultValue wBase tyRaftLog).toOption.getD .nil

/-! ## Embedding concrete values into the symbolic domain
(HandlerEqSym provenance) -/

/-- Fueled embedding of a concrete `GoValue` as a mirror value (every
scalar a literal term). Fuel exhaustion yields an `atom`, which QUITS
on any use — fail closed, never a silent wrong embedding. -/
def embedGoF : Nat → GoValue → SymValue
  | 0, _ => .atom 0
  | _ + 1, .unit => .unit
  | _ + 1, .bool b => .bool (.lit b)
  | _ + 1, .int v k => .int (.lit v) k
  | _ + 1, .float bits k => .float bits k
  | _ + 1, .string s => .string s
  | _ + 1, .addr l => .addr l
  | _ + 1, .nil => .nil
  | fuel + 1, .interface d v => .interface d (embedGoF fuel v)
  | fuel + 1, .struct tid fs =>
      .struct tid (fs.map (fun p => (p.1, embedGoF fuel p.2)))
  | fuel + 1, .array vs => .array (vs.map (embedGoF fuel))
  | _ + 1, .slice sv => .slice sv
  | _ + 1, .map mv => .map mv
  | fuel + 1, .mapData entries =>
      .mapData (entries.map (fun p => (embedGoF fuel p.1, embedGoF fuel p.2)))
  | _ + 1, .chan cv => .chan cv
  | fuel + 1, .chanData buf cap closed =>
      .chanData (buf.map (embedGoF fuel)) cap closed
  | fuel + 1, .funcVal fid captured =>
      .funcVal fid (captured.map (embedGoF fuel))
  | _ + 1, .syncData p => .syncData p

def embedGo (v : GoValue) : SymValue := embedGoF valueEqbFuel v

/-- Replace one named field's payload in a mirror struct value. -/
def setSymField (v : SymValue) (name : String) (nv : SymValue) : SymValue :=
  match v with
  | .struct tid fs =>
      .struct tid (fs.map (fun p => if p.1 == name then (p.1, nv) else p))
  | v => v

/-- The pinned program's type table. -/
def twinTypes : TypeEnv := wBase.types

/-- The pinned-table pack (all four tables = the twin's). -/
def bfTB : SymTables :=
  { types := twinTypes
    functions := twinLowered.funcs
    methods := twinLowered.methods
    methodSets := twinLowered.methodSets }

end GoLean.RaftSeam
