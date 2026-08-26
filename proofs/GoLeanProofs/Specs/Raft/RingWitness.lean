import GoLeanProofs.Specs.Raft.RingEquation
import GoLeanProofs.Frame.ShapeSpan
import GoLeanProofs.Specs.Raft.BpcResite

/-!
# A4-U21 (C2c): the sub-ring spans' WITNESS — the concrete run and
the `span_consume` composition at a non-identity placement

Witness-in-same-slice (the arc4b lane's convention, adopted
lane-wide): the witness is a fidelity instrument, not ceremony.
Three parts:

1. **The concrete run** (`ring_witness_run`): `ring_full_span`
   instantiated at the zero valuation over the pinned tables — a
   13,870-step machine fact consuming exactly the five canonical
   draws, landing on the endpoint literal whose payload facts are
   `RingEquation`'s kernel readouts (applied 1→2, storage ents +1
   with the appended (Index 2, Term 1) entry, HardState Commit 2
   persisted, unstable emptied at offset 3, net/live +MsgAppResp).
   The step count and draw count are the census's
   (`artifacts/probe/msgappring.out`) — the census cross-link.

2. **THE COMPOSITION WITNESS** (`rw_consume`,
   `rw_consume_and_resume`): the STORAGE-RESP span (`ring_w4_span`)
   consumed via `span_consume` at a concrete NON-IDENTITY placement
   (`ρT 7034 8` — the span's pre-state relocated with an 8-address
   gap, a frame cell at 7036 in the gap via `frameSimS_extend`),
   then the walk RESUMED with a nine-step literal suffix WRITING the
   frame cell — the C2a instrument doing on a sub-ring span exactly
   what `ShapeWitness.lean` demonstrated on a handler span. This is
   the composition seam a C2d round lemma will use to slot the ring
   chain into the full round at its real placement.

3. **The placement readout** (`rw_readout`): the storage-resp
   payload fact (applied = 2) read at the placement through
   `fieldReadU64_ren` — cell 1949 sits below the shift, so the
   address is preserved.

LINEAGE: Yang–O'Hearn locality (the C2a instrument's), consumed;
the witness pattern is `ShapeWitness.lean`'s, re-instantiated.
-/

namespace GoLean.RaftSeam.Ring

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame GoLean.Sym
open GoLean.Surface GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-! ## 1. The concrete run -/

/-- The zero valuation (the literals carry no atoms — the spans'
ρ-genericity is the value-domain frame rule; any ρ works). -/
def rwρ0 : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }

/-- The pinned-table carrier (heapless; `γS` supplies the heap). -/
def rwσT : ExecState := bfTB.toState

theorem rwAgrees : bfTB.Agrees rwσT := ⟨rfl, rfl, rfl, rfl⟩

/-- **The non-vacuity witness run**: every premise of the composed
span discharged on concrete data; 13,870 steps, five draws, ending
at the projection call with the storage-resp payload facts readable
(RingEquation's `ring_post_*` readouts hold at this exact state). -/
theorem ring_witness_run :
    stepFnIter 13870 (γS rwρ0 rwσT maS0) (γC rwρ0 maC0)
      [0, 0, 0, 0, 0]
      = .ok (γC rwρ0 maC5, γS rwρ0 rwσT maS5, []) :=
  ring_full_span rwρ0 rwσT rwAgrees []

/-! ## 2. The composition witness — `span_consume` on the
storage-resp span at a non-identity placement -/

/-- The storage-resp span's concrete pre-state (allocator 7034). -/
def rwσ3 : ExecState := γS rwρ0 rwσT maS3

/-- The span's concrete post-state. -/
def rwσ4 : ExecState := γS rwρ0 rwσT maS4

/-- The shift: identity below 7034 (= `maS3`'s allocator), +8 above —
an 8-address gap [7034, 7042) for frame cells. -/
def rwρ : Nat → Nat := ρT 7034 8

/-- The frame: one cell in the gap. -/
def rwFrX : Heap := [(.base ⟨7036⟩, ⟨some (.int .uint64), .int 42 .uint64⟩)]

/-- The pinned program's loc bound (kernel-computed; all bodies sit
far below the fixture region). -/
theorem rw_funcSup :
    GoCore.Machine.funcListSup rwσ3.functions.toList = 31 := by
  kernel_rfl

theorem rw_bodies : ∀ f ∈ rwσ3.functions.toList,
    renameStmt rwρ f.body = f.body := by
  have hid : ∀ x < 7034, rwρ x = x := fun x hx => ρT_lt hx
  exact renameBodies_id hid
    (show GoCore.Machine.funcListSup rwσ3.functions.toList ≤ 7034 by
      rw [rw_funcSup]; omega)

/-- The relocation seed at the gap shift. -/
theorem rw_reloc : FrameSimS rwρ 7034 7042 [] rwσ3 (renameState rwρ rwσ3) :=
  frameSimS_relocate (shiftSpec_ρT 7034 8)
    (Nat.le_of_eq (by kernel_rfl)) rw_bodies

theorem rwFrX_avoid : ∀ a : Nat,
    GoCore.Heap.lookup rwFrX (.base ⟨rwρ a⟩) = none := by
  intro a
  have hne : (Loc.base ⟨7036⟩ : Loc) ≠ .base ⟨rwρ a⟩ := by
    intro h
    have h36 : (7036 : Nat) = rwρ a := by
      have := congrArg (fun l : Loc => match l with
        | .base x => x.id
        | _ => 0) h
      simpa using this
    by_cases hlt : a < 7034
    · rw [show rwρ a = a from ρT_lt hlt] at h36
      omega
    · rw [show rwρ a = a + 8 from ρT_ge (Nat.le_of_not_lt hlt)] at h36
      omega
  simp [rwFrX, GoCore.Heap.lookup, hne]

theorem rw_gap_none :
    GoCore.Heap.lookup (renameState rwρ rwσ3).heap (.base ⟨7036⟩) = none := by
  kernel_rfl

theorem rwFrX_fresh : ∀ l : Loc, (GoCore.Heap.lookup rwFrX l).isSome →
    GoCore.Heap.lookup (renameState rwρ rwσ3).heap l = none := by
  intro l hl
  have hleq : l = .base ⟨7036⟩ := by
    by_cases hb : ((Loc.base ⟨7036⟩ : Loc) == l) = true
    · exact (eq_of_beq hb).symm
    · exact absurd hl (by simp [rwFrX, GoCore.Heap.lookup, hb])
  rw [hleq]
  exact rw_gap_none

/-- **The concrete placement**: relocation + frame extension. -/
theorem rwPlacement : FrameSimS rwρ 7034 7042 rwFrX rwσ3
    { renameState rwρ rwσ3 with
        heap := (renameState rwρ rwσ3).heap ++ rwFrX } := by
  have h := frameSimS_extend rw_reloc (by simp [renameState]) rwFrX_avoid
    rwFrX_fresh
  simpa using h

/-- **THE MID-WALK CONSUMPTION on a SUB-RING span**: `ring_w4_span`
(Advance + both nested storage-resp Steps, choice-free) consumed at
the placement — the framed run completes on the same (empty) stream
and hands back the post-state as the three-segment splice. -/
theorem rw_consume :
    ∃ pre post, rwσ4.heap = pre ++ post
      ∧ stepFnIter 3202
          { renameState rwρ rwσ3 with
              heap := (renameState rwρ rwσ3).heap ++ rwFrX }
          (renameConfig rwρ (γC rwρ0 maC3)) []
          = .ok (renameConfig rwρ (γC rwρ0 maC4),
              { rwσ4 with
                  heap := renameHeap rwρ pre ++ rwFrX ++ renameHeap rwρ post,
                  nextAddr := rwρ rwσ4.nextAddr }, [])
      ∧ FrameSimS rwρ 7034 7042 rwFrX rwσ4
          { rwσ4 with
              heap := renameHeap rwρ pre ++ rwFrX ++ renameHeap rwρ post,
              nextAddr := rwρ rwσ4.nextAddr } := by
  have hrun : stepFnIter 3202 rwσ3 (γC rwρ0 maC3) []
      = .ok (γC rwρ0 maC4, rwσ4, []) :=
    ring_w4_span rwρ0 rwσT rwAgrees []
  exact span_consume hrun rwPlacement

/-- The resume suffix: `*(&7036) = 9` — a write to the FRAME cell. -/
def rwCsuf : Config :=
  .exec (.assign (.addr (.locLit (.base ⟨7036⟩))) (.intLit 9 .uint64)) [] .stop

def rwC5 : Config :=
  .next (.storeK
    [Machine.TargetRef.chain (GoValue.addr (.base ⟨7036⟩)) [] []]
    [.int 9 .uint64] (.seqn #[]) [] .stop)

def rwC6 : Config := .next (.storeK [] [] (.seqn #[]) [] .stop)

/-- The literal-style resume from ANY state holding the frame cell
(in particular the handed-back post-state, via `frame_pres`). -/
theorem rw_resume {σF : ExecState}
    (h36 : GoCore.Heap.lookup σF.heap (.base ⟨7036⟩)
      = some ⟨some (.int .uint64), .int 42 .uint64⟩) :
    stepFnIter 9 σF rwCsuf []
      = .ok (.next .stop,
          { σF with heap := (GoCore.Heap.set σF.heap (.base ⟨7036⟩)
              ⟨some (.int .uint64), .int 9 .uint64⟩ : Heap) }, []) := by
  have h1 : stepFnIter 5 σF rwCsuf [] = .ok (rwC5, σF, []) := rfl
  have h2 : stepFn σF rwC5 [] = .ok (rwC6,
      { σF with heap := (GoCore.Heap.set σF.heap (.base ⟨7036⟩)
          ⟨some (.int .uint64), .int 9 .uint64⟩ : Heap) }, []) := by
    have hnorm : normalizeValueForTyFuel typeResolutionFuel σF
        (Ty.int .uint64) (.int 9 .uint64) = .ok (.int 9 .uint64) := rfl
    simp only [stepFn, rwC5, rwC6, storeTarget, resolveChain, valueAsLoc,
      storeLoc, h36, normalizeValueForTy, hnorm,
      Bind.bind, Except.bind, pure, Except.pure]
  have h3 : ∀ σx : ExecState, stepFnIter 3 σx rwC6 [] = .ok (.next .stop, σx, []) :=
    fun σx => rfl
  have h12 := Surface.stepFnIter_chain h1 (Surface.stepFnIter_one h2)
  have h123 := Surface.stepFnIter_chain h12 (h3 _)
  simpa using h123

/-- Consume, then RESUME writing the outer walk's own (frame) cell —
the end-to-end composition seam for the C2d round lemma. -/
theorem rw_consume_and_resume :
    ∃ pre post, rwσ4.heap = pre ++ post
      ∧ stepFnIter 9
          { rwσ4 with
              heap := renameHeap rwρ pre ++ rwFrX ++ renameHeap rwρ post,
              nextAddr := rwρ rwσ4.nextAddr } rwCsuf []
        = .ok (.next .stop,
            { rwσ4 with
                heap := (GoCore.Heap.set
                  (renameHeap rwρ pre ++ rwFrX ++ renameHeap rwρ post)
                  (.base ⟨7036⟩) ⟨some (.int .uint64), .int 9 .uint64⟩ : Heap),
                nextAddr := rwρ rwσ4.nextAddr }, []) := by
  obtain ⟨pre, post, hsplit, hrunF, hS⟩ := rw_consume
  refine ⟨pre, post, hsplit, ?_⟩
  have h36 := hS.toFrameSim.frame_pres (.base ⟨7036⟩)
    ⟨some (.int .uint64), .int 42 .uint64⟩ (by simp [rwFrX, GoCore.Heap.lookup])
  exact rw_resume h36

/-! ## 3. The placement readout -/

/-- The storage-resp span's payload fact at ITS endpoint (kernel
readout; #eval-checked first): applied = 2 already at `maS4` — the
MsgStorageApplyResp arm's `appliedTo` runs INSIDE W4. -/
theorem rw4_post_applied (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldReadU64 (γS ρ σ maS4) ⟨1949⟩ ⟨"raft.raftLog"⟩ "applied"
      = some 2 := by
  kernel_rfl

/-- **The readout at the placement**: any state the consumption hands
back reads applied = 2 at the UNMOVED address (1949 < 7034, identity
under the shift) — the storage-resp conclusion transported through
the placement. -/
theorem rw_readout :
    ∀ (σF : ExecState), FrameSimS rwρ 7034 7042 rwFrX rwσ4 σF →
      GoLean.Lens.fieldReadU64 σF ⟨1949⟩ ⟨"raft.raftLog"⟩ "applied"
        = some 2 := by
  intro σF hS
  have h := GoLean.Lens.fieldReadU64_ren hS.toFrameSim
    (a := ⟨1949⟩) (rw4_post_applied rwρ0 rwσT)
  have h1949 : rwρ (1949 : Nat) = 1949 := ρT_lt (by omega)
  rw [show (⟨rwρ (1949 : Nat)⟩ : Addr) = ⟨1949⟩ from by rw [h1949]] at h
  exact h

end GoLean.RaftSeam.Ring
