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

end GoLean.RaftSeam.SpanS23
