import GoLeanProofs.Specs.Raft.SpanS23Maps

/-!
# The apply span's cell machinery (A4d-SM2, support layer)

The `main.twin.apply` walk reads and WRITES the `twinNode` struct
(the S3 cursors), bumps `t.committed`, and evaluates the guard
comparisons + the byte-slice conversion. This module carries:

1. **`nodeFs`** — the `main.twinNode` struct at the pinned
   declaration's field order (`artifacts/probe/twintypes.out`),
   symbolic in every payload; `rn`/`st`/`got` are opaque (`normalize`
   is the identity at pointer/map types — no arm matches), the six
   uint64-classed fields carry `.int` payloads (`state` sits at the
   DEFINED `raft.StateType`, which the table resolves to uint64 —
   `applyprobe.out`).
2. **`normalize_nodeFs`** + the two cursor stores
   (`storeTarget_node_applied`/`_lastTrm`) — the `twinFs`/
   `storeTarget_twin_*` pattern at the node cell (every cursor store
   re-normalizes the whole node struct at the declared type).
3. **`storeTarget_twin_committed`** — the `claims` single's pattern
   at the `committed` field (`committed++`).
4. **Comparison/conversion singles** — `eqCmp` at `int`, `neqCmp` at
   `uint64`/`string`/the `raftpb.EntryType` alias chain, slice
   `length`, and `stringFromByteSlice` (the byte fold; the
   `sliceVisibleValues` fact enters as a hypothesis — the `SliceMem`
   append-family precedent, so the span stays shape-generic in the
   slice's offset/backing).

LINEAGE: conditioned-single machine facts (StepKit/SliceMem).
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.RaftSeam.UtoaSpan (twinSt)
open GoLean.RaftSeam.SpanCells

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-! ## 1. The node struct at symbolic payloads -/

/-- The `main.twinNode` field array at the pinned declaration's
order — symbolic in every payload the checker touches. `gm` is the
`got` map's data-cell address; the six numeric fields carry `.int`
uint64 payloads (`state`'s declared type resolves to uint64). -/
def nodeFs (idv : Int) (rnV stV : GoValue) (tmv cmv stv : Int)
    (apl ltm : Int) (gm : Nat) : Array (String × GoValue) :=
  #[("id", .int idv .uint64), ("rn", rnV), ("st", stV),
    ("term", .int tmv .uint64), ("commit", .int cmv .uint64),
    ("state", .int stv .uint64), ("applied", .int apl .uint64),
    ("lastTrm", .int ltm .uint64),
    ("got", .map ⟨some (.base ⟨gm⟩)⟩)]

/-- The node declaration, spelled. -/
def nodeDecl : Array FieldDef :=
  #[⟨"id", .int .uint64, false⟩,
    ⟨"rn", .pointer (.defined ⟨"raft.RawNode"⟩), false⟩,
    ⟨"st", .pointer (.defined ⟨"raft.MemoryStorage"⟩), false⟩,
    ⟨"term", .int .uint64, false⟩,
    ⟨"commit", .int .uint64, false⟩,
    ⟨"state", .defined ⟨"raft.StateType"⟩, false⟩,
    ⟨"applied", .int .uint64, false⟩,
    ⟨"lastTrm", .int .uint64, false⟩,
    ⟨"got", .map .string .bool, false⟩]

/-- **PIN**: the type table's `main.twinNode` IS the spelled
declaration (`artifacts/probe/twintypes.out`). -/
theorem nodeDecl_pinned :
    TypeEnv.lookup twinTypes ⟨"main.twinNode"⟩
      = some (.struct nodeDecl) := by
  kernel_rfl

/-- **PIN**: `raft.StateType` resolves to uint64
(`artifacts/probe/applyprobe.out`). -/
theorem stateTypeDecl_pinned :
    TypeEnv.lookup twinTypes ⟨"raft.StateType"⟩
      = some (.defined (.int .uint64)) := by
  kernel_rfl

/-- **PIN**: `raftpb.EntryType` resolves to int32
(`artifacts/probe/applyprobe.out`). -/
theorem entryTypeResolve_pinned :
    TypeEnv.lookup twinTypes ⟨"raftpb.EntryType"⟩
      = some (.defined (.int .int32)) := by
  kernel_rfl

section NodeLookups

variable {idv tmv cmv stv apl ltm : Int} {rnV stV : GoValue} {gm : Nat}

theorem nodeFs_id :
    StructFields.lookup (nodeFs idv rnV stV tmv cmv stv apl ltm gm)
      "id" = some (.int idv .uint64) := rfl

theorem nodeFs_applied :
    StructFields.lookup (nodeFs idv rnV stV tmv cmv stv apl ltm gm)
      "applied" = some (.int apl .uint64) := rfl

theorem nodeFs_lastTrm :
    StructFields.lookup (nodeFs idv rnV stV tmv cmv stv apl ltm gm)
      "lastTrm" = some (.int ltm .uint64) := rfl

theorem nodeFs_term :
    StructFields.lookup (nodeFs idv rnV stV tmv cmv stv apl ltm gm)
      "term" = some (.int tmv .uint64) := rfl

theorem nodeFs_got :
    StructFields.lookup (nodeFs idv rnV stV tmv cmv stv apl ltm gm)
      "got" = some (.map ⟨some (.base ⟨gm⟩)⟩) := rfl

end NodeLookups

/-- In-range payloads make the spelled node struct its own normal
form at the node type (the identity every cursor store routes
through). -/
theorem normalize_nodeFs {σ : ExecState}
    (htypes : σ.types = twinTypes)
    {idv tmv cmv stv apl ltm : Int} {rnV stV : GoValue} {gm : Nat}
    (h1 : 0 ≤ idv) (h2 : idv < 2 ^ 64)
    (h3 : 0 ≤ tmv) (h4 : tmv < 2 ^ 64)
    (h5 : 0 ≤ cmv) (h6 : cmv < 2 ^ 64)
    (h7 : 0 ≤ stv) (h8 : stv < 2 ^ 64)
    (h9 : 0 ≤ apl) (h10 : apl < 2 ^ 64)
    (h11 : 0 ≤ ltm) (h12 : ltm < 2 ^ 64) :
    normalizeValueForTy σ (.defined ⟨"main.twinNode"⟩)
        (.struct ⟨"main.twinNode"⟩
          (nodeFs idv rnV stV tmv cmv stv apl ltm gm))
      = .ok (.struct ⟨"main.twinNode"⟩
          (nodeFs idv rnV stV tmv cmv stv apl ltm gm)) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    have hraw : normalizeValueForTy
        ⟨twinTypes, functions, methods, methodSets, heap, nextAddr⟩
        (.defined ⟨"main.twinNode"⟩)
        (.struct ⟨"main.twinNode"⟩
          (nodeFs idv rnV stV tmv cmv stv apl ltm gm))
        = .ok (.struct ⟨"main.twinNode"⟩
            (nodeFs (IntKind.normalize .uint64 idv) rnV stV
              (IntKind.normalize .uint64 tmv)
              (IntKind.normalize .uint64 cmv)
              (IntKind.normalize .uint64 stv)
              (IntKind.normalize .uint64 apl)
              (IntKind.normalize .uint64 ltm) gm)) := by
      kernel_rfl
    rw [hraw, GoLean.SliceMem.unorm_of_range h1 h2,
      GoLean.SliceMem.unorm_of_range h3 h4,
      GoLean.SliceMem.unorm_of_range h5 h6,
      GoLean.SliceMem.unorm_of_range h7 h8,
      GoLean.SliceMem.unorm_of_range h9 h10,
      GoLean.SliceMem.unorm_of_range h11 h12]

/-! ## 2. The node cursor stores + the committed store -/

/-- The node cell payload shorthand. -/
abbrev ndCell (idv : Int) (rnV stV : GoValue) (tmv cmv stv : Int)
    (apl ltm : Int) (gm : Nat) : HeapCell :=
  ⟨some (.defined ⟨"main.twinNode"⟩),
    .struct ⟨"main.twinNode"⟩
      (nodeFs idv rnV stV tmv cmv stv apl ltm gm)⟩

section Stores

variable {σ : ExecState} {nw : Nat}
  {idv tmv cmv stv apl ltm : Int} {rnV stV : GoValue} {gm : Nat}

/-- `nd.applied = v'` through the `fieldAddr` chain. -/
theorem storeTarget_node_applied
    (htypes : σ.types = twinTypes)
    (hNw : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCell idv rnV stV tmv cmv stv apl ltm gm))
    {v' : Int}
    (h1 : 0 ≤ idv) (h2 : idv < 2 ^ 64)
    (h3 : 0 ≤ tmv) (h4 : tmv < 2 ^ 64)
    (h5 : 0 ≤ cmv) (h6 : cmv < 2 ^ 64)
    (h7 : 0 ≤ stv) (h8 : stv < 2 ^ 64)
    (h9 : 0 ≤ v') (h10 : v' < 2 ^ 64)
    (h11 : 0 ≤ ltm) (h12 : ltm < 2 ^ 64) :
    storeTarget σ (.chain (.addr (.base ⟨nw⟩)) []
        [.field ⟨"main.twinNode"⟩ "applied"]) (.int v' .uint64)
      = .ok { σ with heap := Heap.set σ.heap (.base ⟨nw⟩) (ndCell idv rnV stV tmv cmv stv v' ltm gm) } := by
  have hset : StructFields.set
      (nodeFs idv rnV stV tmv cmv stv apl ltm gm) "applied"
      (.int v' .uint64)
      = .ok (nodeFs idv rnV stV tmv cmv stv v' ltm gm) := by
    with_unfolding_all rfl
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, storeLoc, loadLoc, hNw]
  rw [show ((⟨"main.twinNode"⟩ : TypeId) != (⟨"main.twinNode"⟩ : TypeId))
    = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, hset,
    normalize_nodeFs htypes h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]

/-- `nd.lastTrm = v'`. -/
theorem storeTarget_node_lastTrm
    (htypes : σ.types = twinTypes)
    (hNw : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCell idv rnV stV tmv cmv stv apl ltm gm))
    {v' : Int}
    (h1 : 0 ≤ idv) (h2 : idv < 2 ^ 64)
    (h3 : 0 ≤ tmv) (h4 : tmv < 2 ^ 64)
    (h5 : 0 ≤ cmv) (h6 : cmv < 2 ^ 64)
    (h7 : 0 ≤ stv) (h8 : stv < 2 ^ 64)
    (h9 : 0 ≤ apl) (h10 : apl < 2 ^ 64)
    (h11 : 0 ≤ v') (h12 : v' < 2 ^ 64) :
    storeTarget σ (.chain (.addr (.base ⟨nw⟩)) []
        [.field ⟨"main.twinNode"⟩ "lastTrm"]) (.int v' .uint64)
      = .ok { σ with heap := Heap.set σ.heap (.base ⟨nw⟩) (ndCell idv rnV stV tmv cmv stv apl v' gm) } := by
  have hset : StructFields.set
      (nodeFs idv rnV stV tmv cmv stv apl ltm gm) "lastTrm"
      (.int v' .uint64)
      = .ok (nodeFs idv rnV stV tmv cmv stv apl v' gm) := by
    with_unfolding_all rfl
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, storeLoc, loadLoc, hNw]
  rw [show ((⟨"main.twinNode"⟩ : TypeId) != (⟨"main.twinNode"⟩ : TypeId))
    = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, hset,
    normalize_nodeFs htypes h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]

end Stores

section TwinStore

variable {σ : ExecState} {tw : Nat}
  {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
  {c cm w sq : Int} {tr : GoString}

/-- `t.committed = v'` (the `claims` single's pattern at the
`committed` field). -/
theorem storeTarget_twin_committed
    (htypes : σ.types = twinTypes)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV))
    {cm' : Int}
    (hc0 : -(2 ^ 63) ≤ c) (hc1 : c < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm') (hm1 : cm' < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    storeTarget σ (.chain (.addr (.base ⟨tw⟩)) []
        [.field ⟨"main.twin"⟩ "committed"]) (.int cm' .int)
      = .ok { σ with heap := Heap.set σ.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV c cm' w pendV drvV sq tr hlV) } := by
  have hset : StructFields.set (twinFs nodesV netV liveV lm byV c cm w
      pendV drvV sq tr hlV) "committed" (.int cm' .int)
      = .ok (twinFs nodesV netV liveV lm byV c cm' w pendV drvV sq
          tr hlV) := by
    with_unfolding_all rfl
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, storeLoc, loadLoc, hTw]
  rw [show ((⟨"main.twin"⟩ : TypeId) != (⟨"main.twin"⟩ : TypeId))
    = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, hset,
    normalize_twinFs htypes hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1]

end TwinStore

/-! ## 3. Comparison singles -/

/-- `==` at `int` (the `len(…) == 0` guard). -/
theorem applyStrictOp_eqCmp_int {σ : ExecState} {a b : Int} :
    applyStrictOp σ (.eqCmp (.int .int))
        [.int a .int, .int b .int]
      = .ok (.bool (a == b), σ) := by
  simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel]

/-- `!=` at `uint64` (the S2 term comparison). -/
theorem applyStrictOp_neqCmp_u64 {σ : ExecState} {a b : Int} :
    applyStrictOp σ (.neqCmp (.int .uint64))
        [.int a .uint64, .int b .uint64]
      = .ok (.bool (!(a == b)), σ) := by
  simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel]

/-- `!=` at `string` (the S2 data comparison). -/
theorem applyStrictOp_neqCmp_string {σ : ExecState} {l r : GoString} :
    applyStrictOp σ (.neqCmp .string) [.string l, .string r]
      = .ok (.bool (!(l == r)), σ) := by
  simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel]

/-- `!=` at the `raftpb.EntryType` defined chain (the anomaly guard;
resolves through the pinned table to int32). -/
theorem applyStrictOp_neqCmp_entryType {σ : ExecState}
    (htypes : σ.types = twinTypes) {a b : Int} :
    applyStrictOp σ (.neqCmp (.defined ⟨"raftpb.EntryType"⟩))
        [.int a .int32, .int b .int32]
      = .ok (.bool (!(a == b)), σ) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    kernel_rfl

/-- `<=` at wrapped ints (the S3 index guard; `valueAtMost` is
kind-blind on int payloads). -/
theorem applyStrictOp_atMostCmp_int {σ : ExecState} {a b : Int}
    {k1 k2 : IntKind} :
    applyStrictOp σ .atMostCmp [.int a k1, .int b k2]
      = .ok (.bool (decide (a ≤ b)), σ) := by
  simp [applyStrictOp, valueAtMost, Bind.bind, Except.bind,
    pure, Except.pure]

/-- `<` at wrapped ints (the S3 term guard). -/
theorem applyStrictOp_lessCmp_int' {σ : ExecState} {a b : Int}
    {k1 k2 : IntKind} :
    applyStrictOp σ .lessCmp [.int a k1, .int b k2]
      = .ok (.bool (decide (a < b)), σ) := by
  simp [applyStrictOp, valueLess, Bind.bind, Except.bind,
    pure, Except.pure]

/-- `len` of a well-formed slice. -/
theorem applyStrictOp_length_slice {σ : ExecState} {b : Loc}
    {off n cap : Nat} (hnc : n ≤ cap) :
    applyStrictOp σ (.lengthOf (some (.slice (.int .uint8))))
        [.slice ⟨some b, off, n, cap⟩]
      = .ok (.int (n : Int) .int, σ) := by
  simp [applyStrictOp, validateSlice, Bind.bind, Except.bind, pure,
    Except.pure, Nat.not_lt.mpr hnc]

/-! ## 4. The byte-slice conversion -/

/-- The machine encoding of a byte list as array elements. -/
def bytesArr (bs : List UInt8) : Array GoValue :=
  ⟨bs.map (fun b => .int (b.toNat : Int) .uint8)⟩

private theorem byteFold_generic
    (f : GoValue → Array UInt8 → Except GoError (ForInStep (Array UInt8)))
    (hf : ∀ (b : UInt8) (r : Array UInt8),
      f (.int (b.toNat : Int) .uint8) r = .ok (.yield (r.push b))) :
    ∀ (bs : List UInt8) (acc : Array UInt8),
    forIn (m := Except GoError)
        (bs.map (fun b => GoValue.int (b.toNat : Int) .uint8)) acc f
      = .ok (acc ++ ⟨bs⟩)
  | [], acc => by
    simp only [List.map_nil, List.forIn_nil, pure, Except.pure]
    rfl
  | b :: rest, acc => by
    rw [List.map_cons, List.forIn_cons, hf]
    simp only [Bind.bind, Except.bind]
    rw [byteFold_generic f hf rest (acc.push b)]
    congr 1
    apply Array.ext'
    simp

/-- **`string(bytes)`** at a slice whose visible values are the byte
list: the result is exactly the `GoString` of those bytes. The
`sliceVisibleValues` fact enters as a hypothesis (the `SliceMem`
append-family precedent), keeping the span shape-generic in the
slice's offset and backing. -/
theorem applyStrictOp_stringFromByteSlice {σ : ExecState}
    {sv : SliceValue} {bs : List UInt8}
    (hvis : sliceVisibleValues σ sv = .ok (bytesArr bs)) :
    applyStrictOp σ .stringFromByteSlice [.slice sv]
      = .ok (.string ⟨⟨bs⟩⟩, σ) := by
  simp only [applyStrictOp, valueAsSlice, Bind.bind, Except.bind, pure,
    Except.pure, hvis, ← Array.forIn_toList]
  rw [show (bytesArr bs).toList
    = bs.map (fun b => GoValue.int (b.toNat : Int) .uint8) from rfl]
  rw [byteFold_generic _ ?hf bs #[]]
  case hf =>
    intro b r
    have hb : b.toNat < 256 := b.toNat_lt
    have hcond : (decide ((b.toNat : Int) < 0)
        || decide ((b.toNat : Int) > 255)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not,
        Int.not_lt]
      omega
    simp only [hcond, Bool.false_eq_true, if_false, Int.toNat_natCast,
      UInt8.ofNat_toNat]
  show Except.ok (GoValue.string ⟨#[] ++ ⟨bs⟩⟩, σ) = _
  rw [show (#[] : Array UInt8) ++ (⟨bs⟩ : Array UInt8)
    = (⟨bs⟩ : Array UInt8) from by
      apply Array.ext'
      simp]

end GoLean.RaftSeam.SpanS23
