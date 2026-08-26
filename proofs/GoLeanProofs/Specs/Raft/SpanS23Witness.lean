import GoLeanProofs.Specs.Raft.SpanS23

/-!
# `s23_span_computes` witnesses (A4d-SM2, witness-in-same-slice)

Concrete five-branch discharges of the span theorem at the U23
bridge's OWN events (`NativeCheckerBridge.s23w_fire2/fire3/clean`):

- **S2 fire** at the bridge's `⟨1,2,2,7⟩ / ⟨2,2,2,8⟩` pair: the
  stored slot's data byte `[6]` codes to `encGS = 7` and the incoming
  payload `[7]` to `8` — the machine's string comparison at the walk
  IS the model's `7 ≠ 8` at the projection.
- **S3 fire** (re-applied index) and **clean insert** at the same
  fixture family.
- The model ties (`s2HitB` readouts, `s23Step` at the projected
  event) verified `rfl`/axiom-free.

Every premise of `s23_span_computes` is discharged on concrete cells
(the non-vacuity gate's requirement).
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanApplyGetters (tidE)
open GoLean.RaftSeam.NativeSpec (s23Step s2Hit)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## The fixture (the `applyprobe.out` shape: twin 50, node 52,
entry 45, Type/Term/Index cells 30/31/32, data array 34, leaderOf 55,
got 56, byIndex 57) -/

/-- The witness entry fields. -/
def wEntryFs : Array (String × GoValue) :=
  #[("Type", .addr (.base ⟨30⟩)), ("Term", .addr (.base ⟨31⟩)),
    ("Index", .addr (.base ⟨32⟩)), ("Data",
      .slice ⟨some (.base ⟨34⟩), 0, 1, 1⟩)]

/-- The witness heap: entry `(idx = ixv, trm = tmv)` with one data
byte `db`, node cursors `(apl, ltm)`, byIndex `bkvs`. -/
def wHeap (ixv tmv : Nat) (db : UInt8) (apl ltm : Nat)
    (bkvs : List (Int × SlotA)) : Heap :=
  [(.base ⟨45⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩),
      .struct tidE wEntryFs⟩),
   (.base ⟨30⟩, ⟨some (.defined ⟨"raftpb.EntryType"⟩),
      .int 0 .int32⟩),
   (.base ⟨31⟩, ⟨some (.int .uint64), .int (tmv : Int) .uint64⟩),
   (.base ⟨32⟩, ⟨some (.int .uint64), .int (ixv : Int) .uint64⟩),
   (.base ⟨34⟩, ⟨some (.array 1 (.int .uint8)),
      .array #[.int (db.toNat : Int) .uint8]⟩),
   (.base ⟨50⟩, twCell .nil .nil .nil 55 (.map ⟨some (.base ⟨57⟩)⟩)
      3 1 0 .nil .nil 9 (gs [97]) .nil),
   (.base ⟨52⟩, ndCellN 2 .nil .nil 5 0 2 apl ltm 56),
   (.base ⟨55⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨56⟩, ⟨none, .mapData (toEntriesS [])⟩),
   (.base ⟨57⟩, ⟨none, .mapData (toEntriesB bkvs)⟩)]

/-- The witness span instance, discharged for any in-range fixture
parameters (the branch witnesses below pick the bridge's events). -/
theorem s23w_span (ixv tmv : Nat) (db : UInt8) (apl ltm : Nat)
    (bkvs : List (Int × SlotA))
    (hix : ixv < 2 ^ 64) (htm : tmv < 2 ^ 64)
    (hapl : apl < 2 ^ 64) (hltm : ltm < 2 ^ 64)
    (hsl : ∀ p ∈ bkvs, p.2.1 < 2 ^ 64 ∧ p.2.2.2 < 2 ^ 64) :
    ∃ m ≤ 18400, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m (twinSt (wHeap ixv tmv db apl ltm bkvs) 60)
          (.retV (.addr (.base ⟨45⟩))
            (.callArgsK ⟨"main.twin.apply"⟩ []
              [.addr (.base ⟨50⟩), .addr (.base ⟨52⟩)] [] [] .stop))
          []
        = .ok (.next .stop, σ', [])
      ∧ Heap.lookup σ'.heap (.base ⟨52⟩)
          = some (ndCellN 2 .nil .nil 5 0 2 ixv tmv 56)
      ∧ Heap.lookup σ'.heap (.base ⟨50⟩)
          = some (twCell .nil .nil .nil 55
              (.map ⟨some (.base ⟨57⟩)⟩) 3
              (1 + (if encGS ⟨⟨[db]⟩⟩ = 0 then 0 else 1))
              (0 + ((if ixv ≤ apl then 1 else 0)
                + (if tmv < ltm then 1 else 0)
                + (if encGS ⟨⟨[db]⟩⟩ = 0 then 0
                    else s2HitB bkvs ixv tmv ⟨⟨[db]⟩⟩) : Nat))
              .nil .nil 9 tr' .nil)
      ∧ Heap.lookup σ'.heap (.base ⟨57⟩)
          = some ⟨none, .mapData (toEntriesB
              (if encGS ⟨⟨[db]⟩⟩ = 0 then bkvs
                else bInsertIfAbsent bkvs (ixv : Int)
                  (tmv, ⟨⟨[db]⟩⟩, 2)))⟩ := by
  have h := s23_span_computes (envC := []) (Kc := .stop)
    (tw := 50) (nw := 52) (ew := 45) (li := 32) (lt2 := 31)
    (lty := 30) (da := 34) (gm := 56) (bm := 57)
    (fsE := wEntryFs)
    (nodesV := .nil) (netV := .nil) (liveV := .nil) (pendV := .nil)
    (drvV := .nil) (hlV := .nil) (rnV := .nil) (stV := .nil)
    (lm := 55) (cc := 3) (cm := 1) (w := 0) (sq := 9)
    (tr := gs [97])
    (idvN := 2) (tmvN := 5) (cmvN := 0) (stvN := 2)
    (apl := apl) (ltm := ltm) (ixN := ixv) (tmN := tmv)
    (doff := 0) (dcap := 1) (dbs := [db])
    (darr := #[.int (db.toNat : Int) .uint8])
    (gkvs := []) (bkvs := bkvs)
    (twinSt (wHeap ixv tmv db apl ltm bkvs) 60) []
    ⟨rfl, rfl, rfl, rfl⟩
    (by
      intro x hx
      have hx60 : 60 ≤ x := hx
      show Heap.lookup (wHeap ixv tmv db apl ltm bkvs)
        (.base ⟨x⟩) = none
      unfold wHeap
      show (if (45 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (30 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (31 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (32 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (34 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (50 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (52 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (55 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (56 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      show (if (57 : Nat) == x then _ else _) = none
      rw [if_neg (by simp; omega)]
      rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by
      intro i hi
      match i, hi with
      | 0, _ => rfl)
    (by simp)
    rfl rfl rfl rfl
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    hix htm (by omega) (by omega) (by omega) (by omega)
    hapl hltm hsl
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  obtain ⟨m, hm, σ', tr', hrun, hnd, htw, hgot, hby, _, _, _, _, _⟩
    := h
  exact ⟨m, hm, σ', tr', hrun, hnd, htw, hby⟩

/-! ## The branch witnesses at the bridge's events -/

/-- **The S2 fire** at the bridge's event pair: node 1 stored
`(idx 2, term 2, data ⟨[6]⟩)` (the model row `(2, 2, 7, 1)`), node 2
applies `(2, 2, ⟨[7]⟩)` (the event `⟨2,2,2,8⟩`) — the walk fires. -/
theorem s23w_span_s2fire :
    ∃ m ≤ 18400, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m
          (twinSt (wHeap 2 2 7 1 2 [(2, (2, ⟨⟨[6]⟩⟩, 1))]) 60)
          (.retV (.addr (.base ⟨45⟩))
            (.callArgsK ⟨"main.twin.apply"⟩ []
              [.addr (.base ⟨50⟩), .addr (.base ⟨52⟩)] [] [] .stop))
          []
        = .ok (.next .stop, σ', [])
      ∧ Heap.lookup σ'.heap (.base ⟨50⟩)
          = some (twCell .nil .nil .nil 55
              (.map ⟨some (.base ⟨57⟩)⟩) 3 2 1 .nil .nil 9 tr'
              .nil) := by
  obtain ⟨m, hm, σ', tr', hrun, hnd, htw, hby⟩ :=
    s23w_span 2 2 7 1 2 [(2, (2, ⟨⟨[6]⟩⟩, 1))]
      (by omega) (by omega) (by omega) (by omega)
      (by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨by show (2 : Nat) < 2 ^ 64; omega,
          by show (1 : Nat) < 2 ^ 64; omega⟩)
  refine ⟨m, hm, σ', tr', hrun, ?_⟩
  rw [htw]
  rfl

/-- **The S3 fire** (re-applied index): `idx 2 ≤ applied 2`. -/
theorem s23w_span_s3fire :
    ∃ m ≤ 18400, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m (twinSt (wHeap 2 2 7 2 2 []) 60)
          (.retV (.addr (.base ⟨45⟩))
            (.callArgsK ⟨"main.twin.apply"⟩ []
              [.addr (.base ⟨50⟩), .addr (.base ⟨52⟩)] [] [] .stop))
          []
        = .ok (.next .stop, σ', [])
      ∧ Heap.lookup σ'.heap (.base ⟨50⟩)
          = some (twCell .nil .nil .nil 55
              (.map ⟨some (.base ⟨57⟩)⟩) 3 2 1 .nil .nil 9 tr'
              .nil) := by
  obtain ⟨m, hm, σ', tr', hrun, hnd, htw, hby⟩ :=
    s23w_span 2 2 7 2 2 [] (by omega) (by omega) (by omega)
      (by omega) (by intro p hp; cases hp)
  refine ⟨m, hm, σ', tr', hrun, ?_⟩
  rw [htw]
  rfl

/-- **The clean insert**: fresh index, rising cursors, first data —
zero violations, the slot appended. -/
theorem s23w_span_clean :
    ∃ m ≤ 18400, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m (twinSt (wHeap 4 5 112 3 5 []) 60)
          (.retV (.addr (.base ⟨45⟩))
            (.callArgsK ⟨"main.twin.apply"⟩ []
              [.addr (.base ⟨50⟩), .addr (.base ⟨52⟩)] [] [] .stop))
          []
        = .ok (.next .stop, σ', [])
      ∧ Heap.lookup σ'.heap (.base ⟨50⟩)
          = some (twCell .nil .nil .nil 55
              (.map ⟨some (.base ⟨57⟩)⟩) 3 2 0 .nil .nil 9 tr'
              .nil)
      ∧ Heap.lookup σ'.heap (.base ⟨57⟩)
          = some ⟨none, .mapData (toEntriesB
              [((4 : Int), (5, ⟨⟨[112]⟩⟩, 2))])⟩ := by
  obtain ⟨m, hm, σ', tr', hrun, hnd, htw, hby⟩ :=
    s23w_span 4 5 112 3 5 [] (by omega) (by omega) (by omega)
      (by omega) (by intro p hp; cases hp)
  refine ⟨m, hm, σ', tr', hrun, ?_, ?_⟩
  · rw [htw]
    rfl
  · rw [hby]
    rfl

/-! ## The model ties (axiom-free) -/

/-- The S2 witness's machine readout IS the model's `s2Hit` at the
projected bridge event `⟨2,2,2,8⟩` against the row `(2,2,7,1)`. -/
theorem s23w_s2hit_model :
    s2HitB [(2, (2, ⟨⟨[6]⟩⟩, 1))] 2 2 ⟨⟨[7]⟩⟩
      = s2Hit ⟨projBy [(2, (2, ⟨⟨[6]⟩⟩, 1))], fun _ => 1,
          fun _ => 2, 0, 0⟩ ⟨2, 2, 2, encGS ⟨⟨[7]⟩⟩⟩ := rfl

/-- The projected event data ARE the bridge's `7`/`8`. -/
theorem s23w_data_codes :
    encGS ⟨⟨[6]⟩⟩ = 7 ∧ encGS ⟨⟨[7]⟩⟩ = 8 := ⟨rfl, rfl⟩

end GoLean.RaftSeam.SpanS23
