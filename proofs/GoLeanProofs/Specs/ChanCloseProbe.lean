import GoLeanProofs.ChanD
import GoLeanProofs.Specs.GoldenQuorumWP
import GoLean.GoCore.MultiStreams

/-!
# The close-probe witness (channel-logic arc slice 1, the write-path law)

The same-commit discharge witness for `wpD_close_owned` — the one
channel law that WRITES the cell through the D-carrier. A
single-goroutine program (the sequential-degenerate class on the pool
carrier: the closing thread OWNS the cell, no invariant): close a
pre-seeded open channel; the triple pins the closed cell in the post —
the first frame-quantified triple whose post records a CHANNEL-CELL
state change. D1-BOTH pair as always (run-conditioned readout +
seeded completion pin).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris

/-- The probe: close the pre-seeded channel. -/
abbrev chanCloseProg : Stmt := .seqn #[.closeChan (.var "cv")]

abbrev closeEnv : LocalEnv := [[("cv", .base ⟨0⟩)]]

/-- Handle at cell 0, chanData at cell 1 (untyped — `makeChan`'s
shape), capacity 1 so the shape is visibly not the rendezvous one. -/
abbrev closeHandleCell : HeapCell :=
  ⟨some (.chan .both .int), .chan ⟨some (.base ⟨1⟩)⟩⟩
abbrev closeOpenCell : HeapCell := ⟨none, .chanData #[] 1 false⟩
abbrev closeClosedCell : HeapCell := ⟨none, .chanData #[] 1 true⟩

abbrev closePre : HProp :=
  .sep (.pointsTo 0 closeHandleCell) (.pointsTo 1 closeOpenCell)
abbrev closePost : HProp :=
  .sep (.pointsTo 0 closeHandleCell) (.pointsTo 1 closeClosedCell)

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 800000 in
/-- The walk: seq entry, handle load, THE CLOSE (cell write), seq
exit — `wpD_close_owned`'s discharge witness. -/
theorem wpD_chan_close_witness :
    embed (GF := GF) closePre
      ⊢ WP (PoolCfgD.mk (.exec chanCloseProg closeEnv .stop))
        {{ _v, embed (GF := GF) closePost }} := by
  iintro HP
  simp only [closePre, closePost, embed]
  icases HP with ⟨H0, H1⟩
  -- seqn entry
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqn)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred1
  simp only [seqCont]
  -- seq head → the close statement
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqNext)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred2
  -- closeChan entry
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.chanStFirst rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred3
  -- load the handle
  iapply (wpD_eval_var (a := ⟨0⟩) (cell := closeHandleCell) (hres := rfl))
  isplitl [H0]
  · iexact H0
  iintro H0
  -- THE CLOSE (the write-path law)
  iapply (wpD_close_owned (a := ⟨1⟩) (buf := #[]) (cap := 1))
  isplitl [H1]
  · iexact H1
  iintro H1
  -- seq exit, stop
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqDone)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred4
  iapply (wp_value' (v := ()))
  isplitl [H0]
  · iexact H0
  · iexact H1

end

/-- The frame-quantified triple: closing the channel flips exactly the
`closed` bit of the data cell; everything else — the handle, every
frame cell — is intact. -/
theorem chanCloseTripleC :
    GoTripleC [] #[] #[] closeEnv closePre chanCloseProg closePost :=
  goTripleC_of_wpD (fun _hprog _hmeths _htypes => wpD_chan_close_witness)

def closeSeed : ExecState :=
  { types := [], functions := #[], methods := #[],
    heap := [(.base ⟨0⟩, closeHandleCell), (.base ⟨1⟩, closeOpenCell)],
    nextAddr := 2 }

/-- Run-conditioned readout (the D1 pair's first half): every `.normal`
completion leaves the handle intact and the data cell CLOSED. -/
theorem chanCloseReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel closeEnv closeSeed ch chanCloseProg
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.chan ⟨some (.base ⟨1⟩)⟩)
        ∧ loadLoc σf (.base ⟨1⟩) = .ok (.chanData #[] 1 true) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf closeSeed.heap) closePre := by
    show sat (((∅ : Heaplet).insert 1 closeOpenCell).insert 0
      closeHandleCell) closePre
    refine sat_sep_insert ?_ rfl
    rw [heaplet_get?_insert_ne (by omega), heaplet_get?_empty]
  have hsplit := InitialSplit.noFrame (P := closePre)
    (hp := closeSeed.heap) (na := 2)
    (funcs := #[]) (env₀ := closeEnv) (prog := chanCloseProg)
    hsat (by decide +kernel)
  have hres := chanCloseTripleC _ 2 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hsub, _hF, hsatQ⟩ := hres
  obtain ⟨h₁, h₂, hs₁, hs₂, -, hcover⟩ := hsatQ
  have hget0 : hQ.get? 0 = some closeHandleCell := by
    rw [hs₁] at hcover
    exact (hcover 0 closeHandleCell).mpr
      (Or.inl (by rw [heaplet_get?_insert_self]))
  have hget1 : hQ.get? 1 = some closeClosedCell := by
    rw [hs₂] at hcover
    exact (hcover 1 closeClosedCell).mpr
      (Or.inr (by rw [heaplet_get?_insert_self]))
  constructor
  · have hg := hsub 0 closeHandleCell hget0
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg
  · have hg := hsub 1 closeClosedCell hget1
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg

/-- The completion pin's kernel certificate (single goroutine — every
stream is the same run; `#eval`-confirmed before `decide`). -/
theorem chanCloseAllStreamsCert :
    allStreamsOkPool
      (fun σf =>
        match loadLoc σf (.base ⟨0⟩), loadLoc σf (.base ⟨1⟩) with
        | .ok (.chan ⟨some (.base ⟨1⟩)⟩), .ok (.chanData #[] 1 true) => true
        | _, _ => false)
      20 ⟨#[.exec chanCloseProg closeEnv .stop], closeSeed, 0⟩ {} = true := by
  decide +kernel

/-- The completion pin (the D1 pair's second half). -/
theorem chanCloseTerminatesNormallyC :
    TerminatesNormallyC closeEnv closeSeed chanCloseProg := by
  refine ⟨20, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool chanCloseAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Iris
