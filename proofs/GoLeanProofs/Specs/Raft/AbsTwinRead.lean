import GoLeanProofs.Specs.Raft.AbsStateV2

/-! # The round-boundary twin reader (`AbsTwinV0` / `absTwinRead`)

Extracted VERBATIM at the W0 reset (kill-list K-C, 2026-08-27) from
the deleted `RoundStatement.lean`: the PAIRING VOCABULARY — total,
fail-closed, first-order lens reads of the twin state (checker
counters, per-node shells, net multiset through `absMessage`) plus
the deep per-node reader. Kept per kill-list criterion (a): the clean
proof path states its invariants over these readers. The donor's
R-form statement former (`RoundLemmaShape`), `RoundFam`, and the
heartbeat-round fixture witness were fixed-trajectory content
(archived — docs/ARCHIVE.md).

Fail-closed hardening carried over from the landing fix round: the
twin and shell struct TypeIds are CHECKED (`twinTid`/`twinNodeTid`/
`rawNodeTid`) and the integer reader refuses `.nil`, so a mis-located
or mis-shaped cell reads back `none`, never a well-formed abstract
state. -/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore

/-- The abstract twin view at a round boundary, v0: the checker
counters, the harness-observed per-node shells (state, term, commit,
applied), and the net multiset with liveness flags. -/
structure AbsTwinV0 where
  violations : Int
  claims : Int
  committed : Int
  nodes : List (Int × Int × Int × Int)
  net : List (Bool × AbsMessage)
  deriving Repr, DecidableEq

/-- Read a plain integer field, fail closed: anything but an `.int`
value — including `.nil` — is `none`. (The twin's shell fields are
non-pointer scalars whose machine zero value is `.int 0 _`, never
`.nil`; the protobuf pointer-scalar nil→0 convention belongs to
`AbsStateV2.derefI32` ONLY.) -/
private def readIntField (fs : Array (String × GoValue)) (n : String) :
    Option Int :=
  match StructFields.lookup fs n with
  | some (.int v _) => some v
  | _ => none

/-- The twin struct's TypeId and the shell node's — pinned so the
readers below refuse mis-located cells. -/
def twinTid : TypeId := ⟨"main.twin"⟩
def twinNodeTid : TypeId := ⟨"main.twinNode"⟩
def rawNodeTid : TypeId := ⟨"raft.RawNode"⟩

/-- One twinNode shell (harness-observed fields only — the deep raft
state is `absTwinNodeRaft`'s). -/
private def readShell (σ : ExecState) : GoValue → Option (Int × Int × Int × Int)
  | .addr l => do
      let c ← Heap.lookup σ.heap l
      match c.value with
      | .struct tid fs => do
          guard (tid == twinNodeTid)
          let st ← readIntField fs "state"
          let tm ← readIntField fs "term"
          let cm ← readIntField fs "commit"
          let ap ← readIntField fs "applied"
          pure (st, tm, cm, ap)
      | _ => none
  | _ => none

private def sliceElems (σ : ExecState) : GoValue → Option (List GoValue)
  | .slice sv => do
      match sv.base with
      | none => if sv.len == 0 then some [] else none
      | some b => do
          let c ← Heap.lookup σ.heap b
          match c.value with
          | .array vs =>
              let l := (vs.toList.drop sv.offset).take sv.len
              if l.length == sv.len then some l else none
          | _ => none
  | _ => none

private def readBool : GoValue → Option Bool
  | .bool b => some b
  | _ => none

/-- **THE ROUND-BOUNDARY READER, v0** (total, fail-closed; every
access through value-level lens reads). `tl` is the twin struct's
location (located once by shape; an invariant of the seeded run,
carried not re-derived). -/
def absTwinRead (σ : ExecState) (tl : Loc) : Option AbsTwinV0 := do
  let tc ← Heap.lookup σ.heap tl
  match tc.value with
  | .struct tid fs => do
      guard (tid == twinTid)
      let violations ← readIntField fs "violations"
      let claims ← readIntField fs "claims"
      let committed ← readIntField fs "committed"
      let ndPtrs ← (StructFields.lookup fs "nodes").bind (sliceElems σ)
      let nodes ← ndPtrs.mapM (readShell σ)
      let netPtrs ← (StructFields.lookup fs "net").bind (sliceElems σ)
      let msgs ← netPtrs.mapM (absMessage σ)
      let liveVs ← (StructFields.lookup fs "live").bind (sliceElems σ)
      let lives ← liveVs.mapM readBool
      if msgs.length == lives.length then
        pure { violations, claims, committed, nodes,
               net := lives.zip msgs }
      else none
  | _ => none

/-- The deep per-node reader: `twin.nodes[i] → .rn → .raft` — the
delivered node's raft cell address (then read with the lens). -/
def absTwinNodeRaft (σ : ExecState) (tl : Loc) (i : Nat) : Option Addr := do
  let tc ← Heap.lookup σ.heap tl
  match tc.value with
  | .struct tid fs => do
      guard (tid == twinTid)
      let ndPtrs ← (StructFields.lookup fs "nodes").bind (sliceElems σ)
      let ndv ← ndPtrs[i]?
      match ndv with
      | .addr ndl => do
          let nc ← Heap.lookup σ.heap ndl
          match nc.value with
          | .struct ntid nfs => do
              guard (ntid == twinNodeTid)
              match StructFields.lookup nfs "rn" with
              | some (.addr rnl) => do
                  let rc ← Heap.lookup σ.heap rnl
                  match rc.value with
                  | .struct rtid rfs => do
                      guard (rtid == rawNodeTid)
                      match StructFields.lookup rfs "raft" with
                      | some (.addr (.base a)) => some a
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | _ => none
  | _ => none

end GoLean.RaftSeam
