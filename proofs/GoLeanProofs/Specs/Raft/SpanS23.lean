import GoLeanProofs.Specs.Raft.SpanS23Walk5

/-!
# `s23_span_computes` — the apply span IS the model step
(A4d-SM2 item 3, the I4 interface's interpreter half for S23)

The headline: the interpreter running the WHOLE `main.twin.apply`
call from ANY symbolic checker state (EntryNormal entry — the
model's own scope, per the U23/C4 note) performs exactly `s23Step`
on the abstract projection:

- the cursors (`nd.applied`/`nd.lastTrm`) EXACT;
- `violations` delta = the two S3 guard readouts + the S2 hit —
  the MODEL PREDICATES literally in the machine readout;
- `committed`/`got` exactly per the empty-payload branch;
- `byIndex` = append-if-absent, lookup-equal to the model's cons
  (`s23_abs_step`);
- the trace existential (the banked weak form), frame respect,
  frontier, freshness, `Agrees` threaded.

`s23_abs_step` is the data-refinement commutation: the machine
readouts ARE `s23Step`'s fields at the `projBy`/`encGS` projection —
composable through folds by `s23Fold_congr`.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanS1 (tyTwinD tyNodeD tidT tidN idE)
open GoLean.RaftSeam.SpanApplyGetters (tidE xCell)
open GoLean.RaftSeam.NativeSpec (AEv S23St lookupIdx s2Hit s23Step)
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

/-! ## 1. The abstraction step -/

/-- **The model-side half**: the machine's whole-span readout is
`s23Step` at the projection — cursors and counters EQUAL, `byIndex`
lookup-extensional (machine append vs model cons). -/
theorem s23_abs_step {bkvs : List (Int × SlotA)} (hwf : KeysWfB bkvs)
    (ap lt : Nat → Nat) (v2 v3 : Nat) (nid ixN tmN : Nat)
    (dv : GoString) (hix : ixN < 2 ^ 64) :
    LookupEqB
      ⟨projBy (if encGS dv = 0 then bkvs
          else bInsertIfAbsent bkvs (ixN : Int) (tmN, dv, nid)),
        fun n => if n = nid then ixN else ap n,
        fun n => if n = nid then tmN else lt n,
        v2 + (if encGS dv = 0 then 0 else s2HitB bkvs ixN tmN dv),
        v3 + (if ixN ≤ ap nid then 1 else 0)
          + (if tmN < lt nid then 1 else 0)⟩
      (s23Step ⟨projBy bkvs, ap, lt, v2, v3⟩
        ⟨nid, ixN, tmN, encGS dv⟩) := by
  refine ⟨?_, rfl, rfl, ?_, rfl⟩
  · -- byIndex lookups
    intro i
    show lookupIdx (projBy (if encGS dv = 0 then bkvs
        else bInsertIfAbsent bkvs (ixN : Int) (tmN, dv, nid))) i
      = lookupIdx (if encGS dv = 0 then projBy bkvs
        else match lookupIdx (projBy bkvs) ixN with
          | some _ => projBy bkvs
          | none => (ixN, tmN, encGS dv, nid) :: projBy bkvs) i
    by_cases hz : encGS dv = 0
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz,
        lookupIdx_projBy hwf hix]
      unfold bInsertIfAbsent
      cases hbi : bIdxOf? bkvs (ixN : Int) with
      | some j =>
        obtain ⟨sj, hbg, _⟩ := bIdxOf?_some_bget? hbi
        rw [hbg]
        simp only [Option.map_some]
      | none =>
        rw [bIdxOf?_none_bget? hbi]
        show lookupIdx (projBy (bkvs ++ [((ixN : Int),
          (tmN, dv, nid))])) i = _
        rw [lookupIdx_projBy_append hwf hix hbi (tmN, dv, nid) i]
        simp only [Option.map_none]
  · -- the S2 counter
    show v2 + (if encGS dv = 0 then 0
        else s2HitB bkvs ixN tmN dv)
      = v2 + s2Hit ⟨projBy bkvs, ap, lt, v2, v3⟩
          ⟨nid, ixN, tmN, encGS dv⟩
    congr 1
    unfold s2Hit
    by_cases hz : encGS dv = 0
    · rw [if_pos hz]
      show (0 : Nat) = if (⟨nid, ixN, tmN, encGS dv⟩ : AEv).data = 0
        then 0 else _
      rw [if_pos hz]
    · rw [if_neg hz]
      show s2HitB bkvs ixN tmN dv
        = if (⟨nid, ixN, tmN, encGS dv⟩ : AEv).data = 0 then 0
          else match lookupIdx (projBy bkvs) ixN with
            | some (t, d, _) =>
                if t ≠ tmN ∨ d ≠ encGS dv then 1 else 0
            | none => 0
      rw [if_neg hz, lookupIdx_projBy hwf hix]
      unfold s2HitB
      cases hbg : bget? bkvs (ixN : Int) with
      | none => rfl
      | some sj => rfl

/-! ## 2. The headline -/

section Headline

variable {envC : LocalEnv} {Kc : Cont}
  {tw nw ew li lt2 lty da gm bm : Nat}
  {dtyEw dtyI dtyT2 dtyTy dtyD : Option Ty}
  {fsE : Array (String × GoValue)}
  {nodesV netV liveV pendV drvV hlV rnV stV : GoValue} {lm : Nat}
  {cc cm w sq : Int} {tr : GoString}
  {idvN tmvN cmvN stvN apl ltm : Nat}
  {ixN tmN : Nat} {doff dcap : Nat} {dbs : List UInt8}
  {darr : Array GoValue}
  {gkvs : List (GoString × Bool)} {bkvs : List (Int × SlotA)}

/-- **THE S23 SPAN-COMPUTES-MODEL THEOREM** (the I4 interface's
interpreter half for S23, banked weak form): the interpreter running
the whole `main.twin.apply` call from ANY symbolic checker state
performs exactly `s23Step` on the abstract projection — the cursors
EXACT, `violations` carrying the two S3 guard readouts plus the S2
hit LITERALLY, `committed`/`got`/`byIndex` per the empty-payload
branch, the trace existential, everything else framed
(`s23_abs_step` transports the readouts into the model). Scope: the
entry is `EntryNormal` (the model's own scope — v1 proposes no conf
changes; the U23/C4 note). -/
theorem s23_span_computes
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    -- the entry
    (hEw : Heap.lookup σ.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩)
    (hfI : StructFields.lookup fsE "Index" = some (.addr (.base ⟨li⟩)))
    (hfT : StructFields.lookup fsE "Term" = some (.addr (.base ⟨lt2⟩)))
    (hfTy : StructFields.lookup fsE "Type"
      = some (.addr (.base ⟨lty⟩)))
    (hfD : StructFields.lookup fsE "Data"
      = some (.slice ⟨some (.base ⟨da⟩), doff, dbs.length, dcap⟩))
    (hIc : Heap.lookup σ.heap (.base ⟨li⟩)
      = some ⟨dtyI, .int (ixN : Int) .uint64⟩)
    (hTc : Heap.lookup σ.heap (.base ⟨lt2⟩)
      = some ⟨dtyT2, .int (tmN : Int) .uint64⟩)
    (hTyc : Heap.lookup σ.heap (.base ⟨lty⟩)
      = some ⟨dtyTy, .int 0 .int32⟩)
    (harr : Heap.lookup σ.heap (.base ⟨da⟩)
      = some ⟨dtyD, .array darr⟩)
    (hwin : ∀ i, (hi : i < dbs.length) →
      darr[doff + i]? = some (.int ((dbs[i].toNat : Int)) .uint8))
    (hdcp : dbs.length ≤ dcap)
    -- the checker cells
    (hNd : Heap.lookup σ.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm))
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm
          (.map ⟨some (.base ⟨bm⟩)⟩) cc cm w pendV drvV sq tr hlV))
    (hGm : Heap.lookup σ.heap (.base ⟨gm⟩)
      = some ⟨none, .mapData (toEntriesS gkvs)⟩)
    (hBm : Heap.lookup σ.heap (.base ⟨bm⟩)
      = some ⟨none, .mapData (toEntriesB bkvs)⟩)
    -- disjointness (writers {tw, nw, gm, bm} pairwise + vs reads)
    (hd1 : tw ≠ nw) (hd2 : tw ≠ gm) (hd3 : tw ≠ bm) (hd4 : nw ≠ gm)
    (hd5 : nw ≠ bm) (hd6 : gm ≠ bm)
    (hd7 : ew ≠ tw) (hd8 : ew ≠ nw) (hd9 : ew ≠ gm) (hd10 : ew ≠ bm)
    (hd11 : li ≠ tw) (hd12 : li ≠ nw)
    (hd13 : lt2 ≠ tw) (hd14 : lt2 ≠ nw)
    (hd15 : lty ≠ tw) (hd16 : lty ≠ nw)
    (hd17 : da ≠ tw) (hd18 : da ≠ nw) (hd19 : da ≠ gm)
    (hd20 : da ≠ bm)
    -- ranges
    (hix : ixN < 2 ^ 64) (htm : tmN < 2 ^ 64)
    (hidv : idvN < 2 ^ 64) (htmv : tmvN < 2 ^ 64)
    (hcmv : cmvN < 2 ^ 64) (hstv : stvN < 2 ^ 64)
    (hapl : apl < 2 ^ 64) (hltm : ltm < 2 ^ 64)
    (hsl : ∀ p ∈ bkvs, p.2.1 < 2 ^ 64 ∧ p.2.2.2 < 2 ^ 64)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm + 1 < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 3 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ 18400, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σ (.retV (.addr (.base ⟨ew⟩))
          (.callArgsK ⟨"main.twin.apply"⟩ []
            [.addr (.base ⟨tw⟩), .addr (.base ⟨nw⟩)] [] envC Kc)) ch
        = .ok (.next Kc, σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨nw⟩)
          = some (ndCellN idvN rnV stV tmvN cmvN stvN ixN tmN gm)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm
              (.map ⟨some (.base ⟨bm⟩)⟩) cc
              (cm + (if encGS ⟨⟨dbs⟩⟩ = 0 then 0 else 1))
              (w + ((if ixN ≤ apl then 1 else 0)
                + (if tmN < ltm then 1 else 0)
                + (if encGS ⟨⟨dbs⟩⟩ = 0 then 0
                    else s2HitB bkvs ixN tmN ⟨⟨dbs⟩⟩) : Nat))
              pendV drvV sq tr' hlV)
      ∧ Heap.lookup σ'.heap (.base ⟨gm⟩)
          = some ⟨none, .mapData (toEntriesS
              (if encGS ⟨⟨dbs⟩⟩ = 0 then gkvs
                else setks gkvs ⟨⟨dbs⟩⟩ true))⟩
      ∧ Heap.lookup σ'.heap (.base ⟨bm⟩)
          = some ⟨none, .mapData (toEntriesB
              (if encGS ⟨⟨dbs⟩⟩ = 0 then bkvs
                else bInsertIfAbsent bkvs (ixN : Int)
                  (tmN, ⟨⟨dbs⟩⟩, idvN)))⟩
      ∧ (∀ x, x < σ.nextAddr → x ≠ tw → x ≠ nw → x ≠ gm → x ≠ bm →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ.nextAddr + 9 ≤ σ'.nextAddr
      ∧ σ'.nextAddr ≤ σ.nextAddr + 130
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  have htypes : σ.types = twinTypes := hag.1
  -- address bounds
  have hewna : ew < σ.nextAddr := by
    rcases Nat.lt_or_ge ew σ.nextAddr with h | h
    · exact h
    · rw [hfr ew h] at hEw; cases hEw
  have hlina : li < σ.nextAddr := by
    rcases Nat.lt_or_ge li σ.nextAddr with h | h
    · exact h
    · rw [hfr li h] at hIc; cases hIc
  have hlt2na : lt2 < σ.nextAddr := by
    rcases Nat.lt_or_ge lt2 σ.nextAddr with h | h
    · exact h
    · rw [hfr lt2 h] at hTc; cases hTc
  have hltyna : lty < σ.nextAddr := by
    rcases Nat.lt_or_ge lty σ.nextAddr with h | h
    · exact h
    · rw [hfr lty h] at hTyc; cases hTyc
  have hdana : da < σ.nextAddr := by
    rcases Nat.lt_or_ge da σ.nextAddr with h | h
    · exact h
    · rw [hfr da h] at harr; cases harr
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hnwna : nw < σ.nextAddr := by
    rcases Nat.lt_or_ge nw σ.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNd; cases hNd
  have hgmna : gm < σ.nextAddr := by
    rcases Nat.lt_or_ge gm σ.nextAddr with h | h
    · exact h
    · rw [hfr gm h] at hGm; cases hGm
  have hbmna : bm < σ.nextAddr := by
    rcases Nat.lt_or_ge bm σ.nextAddr with h | h
    · exact h
    · rw [hfr bm h] at hBm; cases hBm
  -- SEC1: the getters prelude (117)
  have hSec1 := s23_getters_seg (envC := envC) (Kc := Kc)
    (tw := tw) (nw := nw) σ ch hag hEw hfI hfT hIc hTc hfr hix htm
  let na₀ : Nat := σ.nextAddr
  let σG : ExecState := gettersSt tw nw ew ixN tmN σ
  -- σG facts
  have hlkG : ∀ x : Nat, x < na₀ →
      Heap.lookup σG.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : na₀ + 6 ≠ x),
      lookup_set_other (by omega : na₀ + 8 ≠ x),
      lookup_set_other (by omega : na₀ + 7 ≠ x),
      lookup_set_other (by omega : na₀ + 6 ≠ x),
      lookup_set_other (by omega : na₀ + 3 ≠ x),
      lookup_set_other (by omega : na₀ + 5 ≠ x),
      lookup_set_other (by omega : na₀ + 4 ≠ x),
      lookup_set_other (by omega : na₀ + 3 ≠ x),
      lookup_set_other (by omega : na₀ + 2 ≠ x),
      lookup_set_other (by omega : na₀ + 1 ≠ x),
      lookup_set_other (by omega : na₀ ≠ x)]
  have hTcG : Heap.lookup σG.heap (.base ⟨na₀ + 6⟩)
      = some ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨na₀ + 6⟩) = _
    exact lookup_set_self
  have hIcG : Heap.lookup σG.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩ := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨na₀ + 3⟩) = _
    rw [lookup_set_other (by omega : na₀ + 6 ≠ na₀ + 3),
      lookup_set_other (by omega : na₀ + 8 ≠ na₀ + 3),
      lookup_set_other (by omega : na₀ + 7 ≠ na₀ + 3),
      lookup_set_other (by omega : na₀ + 6 ≠ na₀ + 3)]
    exact lookup_set_self
  have hePG : Heap.lookup σG.heap (.base ⟨na₀ + 2⟩)
      = some (eParA ew) := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨na₀ + 2⟩) = _
    rw [lookup_set_other (by omega : na₀ + 6 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 8 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 7 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 6 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 3 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 5 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 4 ≠ na₀ + 2),
      lookup_set_other (by omega : na₀ + 3 ≠ na₀ + 2)]
    exact lookup_set_self
  have hnPG : Heap.lookup σG.heap (.base ⟨na₀ + 1⟩)
      = some (ndParA nw) := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨na₀ + 1⟩) = _
    rw [lookup_set_other (by omega : na₀ + 6 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 8 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 7 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 6 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 3 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 5 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 4 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 3 ≠ na₀ + 1),
      lookup_set_other (by omega : na₀ + 2 ≠ na₀ + 1)]
    exact lookup_set_self
  have htPG : Heap.lookup σG.heap (.base ⟨na₀⟩)
      = some (tParA tw) := by
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨na₀⟩) = _
    rw [lookup_set_other (by omega : na₀ + 6 ≠ na₀),
      lookup_set_other (by omega : na₀ + 8 ≠ na₀),
      lookup_set_other (by omega : na₀ + 7 ≠ na₀),
      lookup_set_other (by omega : na₀ + 6 ≠ na₀),
      lookup_set_other (by omega : na₀ + 3 ≠ na₀),
      lookup_set_other (by omega : na₀ + 5 ≠ na₀),
      lookup_set_other (by omega : na₀ + 4 ≠ na₀),
      lookup_set_other (by omega : na₀ + 3 ≠ na₀),
      lookup_set_other (by omega : na₀ + 2 ≠ na₀),
      lookup_set_other (by omega : na₀ + 1 ≠ na₀)]
    exact lookup_set_self
  have hfrG : ∀ x, σG.nextAddr ≤ x →
      Heap.lookup σG.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx9 : na₀ + 9 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
      (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set (Heap.set
        (Heap.set σ.heap
        (.base ⟨na₀⟩) _) (.base ⟨na₀ + 1⟩) _) (.base ⟨na₀ + 2⟩) _)
        (.base ⟨na₀ + 3⟩) _) (.base ⟨na₀ + 4⟩) _)
        (.base ⟨na₀ + 5⟩) _) (.base ⟨na₀ + 3⟩) _)
        (.base ⟨na₀ + 6⟩) _) (.base ⟨na₀ + 7⟩) _)
        (.base ⟨na₀ + 8⟩) _) (.base ⟨na₀ + 6⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : na₀ + 6 ≠ x),
      lookup_set_other (by omega : na₀ + 8 ≠ x),
      lookup_set_other (by omega : na₀ + 7 ≠ x),
      lookup_set_other (by omega : na₀ + 6 ≠ x),
      lookup_set_other (by omega : na₀ + 3 ≠ x),
      lookup_set_other (by omega : na₀ + 5 ≠ x),
      lookup_set_other (by omega : na₀ + 4 ≠ x),
      lookup_set_other (by omega : na₀ + 3 ≠ x),
      lookup_set_other (by omega : na₀ + 2 ≠ x),
      lookup_set_other (by omega : na₀ + 1 ≠ x),
      lookup_set_other (by omega : na₀ ≠ x)]
    exact hfr x (by omega)
  have hagG : bfTB.Agrees σG := ⟨rfl, rfl, rfl, rfl⟩
  have hσGna : σG.nextAddr = na₀ + 9 := rfl
  -- SEC2: the S3-index guard
  have hS3a := s3idx_seg (env0 := envG2 na₀) (KK := FKa envC Kc)
    (nxt := s3TermIfS)
    (rest2 := [appliedAsn, lastTrmAsn,
      getterUnit "$c2304" (.defined ⟨"raftpb.EntryType"⟩)
        "raftpb.Entry.GetType",
      anomalyIfS,
      getterUnit "$c2307" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      lenIfS,
      getterUnit "$c2308" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      dataAsn, gotAsn, commitAsn, byIdxBlock])
    rfl rfl rfl rfl σG ch hagG hfrG
    ⟨htPG, hnPG, by rw [hlkG tw (by omega)]; exact hTw,
      by rw [hlkG nw (by omega)]; exact hNd, hIcG, hTcG⟩
    hidv hix hapl hc0 hc1 hm0 (by omega) hw0 (by omega) hq0 hq1
  obtain ⟨m2, hm2b, σ1, tr1, hrun2, hTw1, hfrm1, hlo1, hhi1, hfrs1,
    hag1⟩ := hS3a
  -- SEC3: the S3-term guard at σ1
  have hS3b := s3term_seg (env0 := envG2 na₀) (KK := FKa envC Kc)
    (nxt := appliedAsn)
    (rest2 := [lastTrmAsn,
      getterUnit "$c2304" (.defined ⟨"raftpb.EntryType"⟩)
        "raftpb.Entry.GetType",
      anomalyIfS,
      getterUnit "$c2307" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      lenIfS,
      getterUnit "$c2308" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      dataAsn, gotAsn, commitAsn, byIdxBlock])
    rfl rfl rfl rfl σ1 ch hag1 hfrs1
    ⟨by rw [hfrm1 na₀ (by omega) (by omega)]; exact htPG,
      by rw [hfrm1 (na₀ + 1) (by omega) (by omega)]; exact hnPG,
      hTw1,
      by rw [hfrm1 nw (by omega) (by omega),
        hlkG nw (by omega)]; exact hNd,
      by rw [hfrm1 (na₀ + 3) (by omega) (by omega)]; exact hIcG,
      by rw [hfrm1 (na₀ + 6) (by omega) (by omega)]; exact hTcG⟩
    hidv htm hltm hc0 hc1 hm0 (by omega)
    (by split <;> omega) (by split <;> omega) hq0 hq1
  obtain ⟨m3, hm3b, σ2, tr2, hrun3, hTw2, hfrm2, hlo2, hhi2, hfrs2,
    hag2⟩ := hS3b
  -- σ2 cell facts
  have hlk2 : ∀ x : Nat, x < na₀ → x ≠ tw →
      Heap.lookup σ2.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hx hxtw
    rw [hfrm2 x (by omega) hxtw, hfrm1 x (by omega) hxtw,
      hlkG x (by omega)]
  have hnP2 : Heap.lookup σ2.heap (.base ⟨na₀ + 1⟩)
      = some (ndParA nw) := by
    rw [hfrm2 (na₀ + 1) (by omega) (by omega),
      hfrm1 (na₀ + 1) (by omega) (by omega)]
    exact hnPG
  have htP2 : Heap.lookup σ2.heap (.base ⟨na₀⟩)
      = some (tParA tw) := by
    rw [hfrm2 na₀ (by omega) (by omega),
      hfrm1 na₀ (by omega) (by omega)]
    exact htPG
  have heP2 : Heap.lookup σ2.heap (.base ⟨na₀ + 2⟩)
      = some (eParA ew) := by
    rw [hfrm2 (na₀ + 2) (by omega) (by omega),
      hfrm1 (na₀ + 2) (by omega) (by omega)]
    exact hePG
  have hIc2 : Heap.lookup σ2.heap (.base ⟨na₀ + 3⟩)
      = some ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩ := by
    rw [hfrm2 (na₀ + 3) (by omega) (by omega),
      hfrm1 (na₀ + 3) (by omega) (by omega)]
    exact hIcG
  have hTc2 : Heap.lookup σ2.heap (.base ⟨na₀ + 6⟩)
      = some ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩ := by
    rw [hfrm2 (na₀ + 6) (by omega) (by omega),
      hfrm1 (na₀ + 6) (by omega) (by omega)]
    exact hTcG
  have hNd2 : Heap.lookup σ2.heap (.base ⟨nw⟩)
      = some (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm) := by
    rw [hlk2 nw (by omega) (fun he => hd1 he.symm)]
    exact hNd
  -- SEC4: the cursor stores (22)
  have hCur := s23_cursors_seg (env0 := envG2 na₀)
    (KK := FKa envC Kc)
    (nxt := getterUnit "$c2304" (.defined ⟨"raftpb.EntryType"⟩)
      "raftpb.Entry.GetType")
    (rest4 := [anomalyIfS,
      getterUnit "$c2307" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      lenIfS,
      getterUnit "$c2308" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      dataAsn, gotAsn, commitAsn, byIdxBlock])
    rfl rfl rfl σ2 ch hag2 hnP2 hNd2 hIc2 hTc2
    hidv htmv hcmv hstv hix htm hapl hltm
  let σ3 : ExecState := { σ2 with heap := Heap.set (Heap.set σ2.heap (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN ltm gm)) (.base ⟨nw⟩) (ndCellN idvN rnV stV tmvN cmvN stvN ixN tmN gm) }
  -- σ3 facts
  have hlk3 : ∀ x : Nat, x < na₀ → x ≠ tw → x ≠ nw →
      Heap.lookup σ3.heap (.base ⟨x⟩)
        = Heap.lookup σ.heap (.base ⟨x⟩) := by
    intro x hx hxtw hxnw
    show Heap.lookup (Heap.set (Heap.set σ2.heap (.base ⟨nw⟩) _)
      (.base ⟨nw⟩) _) (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxnw he.symm),
      lookup_set_other (fun he => hxnw he.symm),
      hlk2 x (by omega) hxtw]
  have heP3 : Heap.lookup σ3.heap (.base ⟨na₀ + 2⟩)
      = some (eParA ew) := by
    show Heap.lookup (Heap.set (Heap.set σ2.heap (.base ⟨nw⟩) _)
      (.base ⟨nw⟩) _) (.base ⟨na₀ + 2⟩) = _
    rw [lookup_set_other (by omega : nw ≠ na₀ + 2),
      lookup_set_other (by omega : nw ≠ na₀ + 2)]
    exact heP2
  have hEw3 : Heap.lookup σ3.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    rw [hlk3 ew (by omega) hd7 hd8]
    exact hEw
  have hTyc3 : Heap.lookup σ3.heap (.base ⟨lty⟩)
      = some ⟨dtyTy, .int 0 .int32⟩ := by
    rw [hlk3 lty (by omega) hd15 hd16]
    exact hTyc
  have hfrs3 : ∀ x, σ3.nextAddr ≤ x →
      Heap.lookup σ3.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx2 : σ2.nextAddr ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set σ2.heap (.base ⟨nw⟩) _)
      (.base ⟨nw⟩) _) (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : nw ≠ x),
      lookup_set_other (by omega : nw ≠ x)]
    exact hfrs2 x hx
  -- SEC5: the GetType unit + EntryNormal skip (66)
  have hTyp := s23_type_seg (env0 := envG2 na₀) (KK := FKa envC Kc)
    (nxt := getterUnit "$c2307" (.slice (.int .uint8))
      "raftpb.Entry.GetData")
    (rest5 := [lenIfS,
      getterUnit "$c2308" (.slice (.int .uint8))
        "raftpb.Entry.GetData",
      dataAsn, gotAsn, commitAsn, byIdxBlock])
    rfl σ3 ch hag2 hfrs3 heP3 hEw3 hfTy hTyc3
  let env3 : LocalEnv := (envG2 na₀).declare "$c2304"
    (.base ⟨σ3.nextAddr⟩)
  let σ4 : ExecState := twinSt (Heap.set (Heap.set (Heap.set
    (Heap.set σ3.heap
      (.base ⟨σ3.nextAddr⟩)
        ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
      (.base ⟨σ3.nextAddr + 1⟩) (xCell ew))
      (.base ⟨σ3.nextAddr + 2⟩)
        ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
      (.base ⟨σ3.nextAddr⟩)
        ⟨some (.defined ⟨"raftpb.EntryType"⟩), .int 0 .int32⟩)
    (σ3.nextAddr + 3)
  have hσ3na : σ3.nextAddr = σ2.nextAddr := rfl
  have hσ4na : σ4.nextAddr = σ3.nextAddr + 3 := rfl
  have hlk4 : ∀ x : Nat, x < σ3.nextAddr →
      Heap.lookup σ4.heap (.base ⟨x⟩)
        = Heap.lookup σ3.heap (.base ⟨x⟩) := by
    intro x hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ3.heap
      (.base ⟨σ3.nextAddr⟩) _) (.base ⟨σ3.nextAddr + 1⟩) _)
      (.base ⟨σ3.nextAddr + 2⟩) _) (.base ⟨σ3.nextAddr⟩) _)
      (.base ⟨x⟩) = _
    rw [lookup_set_other (by omega : σ3.nextAddr ≠ x),
      lookup_set_other (by omega : σ3.nextAddr + 2 ≠ x),
      lookup_set_other (by omega : σ3.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ3.nextAddr ≠ x)]
  have hfrs4 : ∀ x, σ4.nextAddr ≤ x →
      Heap.lookup σ4.heap (.base ⟨x⟩) = none := by
    intro x hx
    have hx3 : σ3.nextAddr + 3 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set σ3.heap
      (.base ⟨σ3.nextAddr⟩) _) (.base ⟨σ3.nextAddr + 1⟩) _)
      (.base ⟨σ3.nextAddr + 2⟩) _) (.base ⟨σ3.nextAddr⟩) _)
      (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : σ3.nextAddr ≠ x),
      lookup_set_other (by omega : σ3.nextAddr + 2 ≠ x),
      lookup_set_other (by omega : σ3.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σ3.nextAddr ≠ x)]
    exact hfrs3 x (by omega)
  have hagσ4 : bfTB.Agrees σ4 := ⟨rfl, rfl, rfl, rfl⟩
  have henvE3 : LocalEnv.lookup env3 "e" = some (.base ⟨na₀ + 2⟩) :=
    by
    rw [lookup_declare_ne (by decide) (envG2 na₀)
      (.base ⟨σ3.nextAddr⟩)]
    rfl
  have heP4 : Heap.lookup σ4.heap (.base ⟨na₀ + 2⟩)
      = some (eParA ew) := by
    rw [hlk4 (na₀ + 2) (by omega)]
    exact heP3
  have hEw4 : Heap.lookup σ4.heap (.base ⟨ew⟩)
      = some ⟨dtyEw, .struct tidE fsE⟩ := by
    rw [hlk4 ew (by omega)]
    exact hEw3
  -- ===== SPLIT on the payload =====
  cases hdbs : dbs with
  | nil =>
    -- EMPTY: the early return
    subst hdbs
    have hRet := s23_len_ret (env0 := env3) (envC := envC)
      (Kc := Kc) (na₀ := na₀) (ew := ew) (da := da)
      (doff := doff) (dcap := dcap)
      (nxt := getterUnit "$c2308" (.slice (.int .uint8))
        "raftpb.Entry.GetData")
      (rest6 := [dataAsn, gotAsn, commitAsn, byIdxBlock])
      henvE3 σ4 ch hagσ4 hfrs4 heP4 hEw4
      (by
        rw [show (([] : List UInt8)).length = 0 from rfl] at hfD
        exact hfD)
    let σ5 : ExecState := twinSt (Heap.set (Heap.set (Heap.set
      (Heap.set σ4.heap
        (.base ⟨σ4.nextAddr⟩)
          ⟨some (.slice (.int .uint8)), .slice ⟨none, 0, 0, 0⟩⟩)
        (.base ⟨σ4.nextAddr + 1⟩) (xCell ew))
        (.base ⟨σ4.nextAddr + 2⟩)
          ⟨some (.slice (.int .uint8)),
            .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩)
        (.base ⟨σ4.nextAddr⟩)
          ⟨some (.slice (.int .uint8)),
            .slice ⟨some (.base ⟨da⟩), doff, 0, dcap⟩⟩)
      (σ4.nextAddr + 3)
    have hlk5 : ∀ x : Nat, x < σ4.nextAddr →
        Heap.lookup σ5.heap (.base ⟨x⟩)
          = Heap.lookup σ4.heap (.base ⟨x⟩) := by
      intro x hx
      show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
        σ4.heap (.base ⟨σ4.nextAddr⟩) _)
        (.base ⟨σ4.nextAddr + 1⟩) _) (.base ⟨σ4.nextAddr + 2⟩) _)
        (.base ⟨σ4.nextAddr⟩) _) (.base ⟨x⟩) = _
      rw [lookup_set_other (by omega : σ4.nextAddr ≠ x),
        lookup_set_other (by omega : σ4.nextAddr + 2 ≠ x),
        lookup_set_other (by omega : σ4.nextAddr + 1 ≠ x),
        lookup_set_other (by omega : σ4.nextAddr ≠ x)]
    have hσ5na : σ5.nextAddr = σ4.nextAddr + 3 := rfl
    refine ⟨117 + m2 + m3 + 22 + 66 + 58, by omega, σ5, tr2,
      ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_,
      ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain hSec1 hrun2) hrun3)
        hCur) hTyp) hRet
    · -- the node cell
      rw [hlk5 nw (by omega), hlk4 nw (by omega)]
      show Heap.lookup (Heap.set (Heap.set σ2.heap (.base ⟨nw⟩) _)
        (.base ⟨nw⟩) _) (.base ⟨nw⟩) = _
      exact lookup_set_self
    · -- the twin cell
      rw [hlk5 tw (by omega), hlk4 tw (by omega)]
      show Heap.lookup (Heap.set (Heap.set σ2.heap (.base ⟨nw⟩) _)
        (.base ⟨nw⟩) _) (.base ⟨tw⟩) = _
      rw [lookup_set_other (Ne.symm hd1),
        lookup_set_other (Ne.symm hd1), hTw2]
      rw [show ((w + (if ixN ≤ apl then 1 else 0) : Int)
          + (if tmN < ltm then 1 else 0) : Int)
        = w + (((if ixN ≤ apl then 1 else 0)
            + (if tmN < ltm then 1 else 0)
            + (if encGS ⟨⟨[]⟩⟩ = 0 then 0
                else s2HitB bkvs ixN tmN ⟨⟨[]⟩⟩) : Nat) : Int)
        from by
          rw [if_pos (show encGS ⟨⟨[]⟩⟩ = 0 from rfl)]
          split <;> split <;> omega]
      rw [show ((cm + (if encGS ⟨⟨[]⟩⟩ = 0 then 0 else 1)) : Int)
        = cm from by
          rw [if_pos (show encGS ⟨⟨[]⟩⟩ = 0 from rfl)]
          omega]
    · -- got unchanged
      rw [if_pos (show encGS ⟨⟨[]⟩⟩ = 0 from rfl),
        hlk5 gm (by omega), hlk4 gm (by omega),
        hlk3 gm (by omega) (fun he => hd2 he.symm)
          (fun he => hd4 he.symm)]
      exact hGm
    · -- byIndex unchanged
      rw [if_pos (show encGS ⟨⟨[]⟩⟩ = 0 from rfl),
        hlk5 bm (by omega), hlk4 bm (by omega),
        hlk3 bm (by omega) (fun he => hd3 he.symm)
          (fun he => hd5 he.symm)]
      exact hBm
    · -- frame respect
      intro x hx hxtw hxnw _ _
      rw [hlk5 x (by omega), hlk4 x (by omega),
        hlk3 x (by omega) hxtw hxnw]
    · -- freshness
      intro x hx
      have hx3 : σ4.nextAddr + 3 ≤ x := hx
      show Heap.lookup (Heap.set (Heap.set (Heap.set (Heap.set
        σ4.heap (.base ⟨σ4.nextAddr⟩) _)
        (.base ⟨σ4.nextAddr + 1⟩) _) (.base ⟨σ4.nextAddr + 2⟩) _)
        (.base ⟨σ4.nextAddr⟩) _) (.base ⟨x⟩) = none
      rw [lookup_set_other (by omega : σ4.nextAddr ≠ x),
        lookup_set_other (by omega : σ4.nextAddr + 2 ≠ x),
        lookup_set_other (by omega : σ4.nextAddr + 1 ≠ x),
        lookup_set_other (by omega : σ4.nextAddr ≠ x)]
      exact hfrs4 x (by omega)
  | cons b0 brest =>
    sorry

end Headline

end GoLean.RaftSeam.SpanS23
