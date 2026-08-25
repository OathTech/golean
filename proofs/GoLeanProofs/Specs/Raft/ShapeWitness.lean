import GoLeanProofs.Frame.ShapeSpan
import GoLeanProofs.Specs.Raft.HhEquation
import GoLeanProofs.Specs.Raft.BpcResite

/-!
# The instrument's DISCHARGE WITNESS: a landed handler equation
consumed MID-WALK, with a literal-style resume writing a FRAME cell
(C2a's third deliverable; the U15 wall's blocked operation, executed)

The scenario the U15 verdict measured as impossible under the weak
relation: an outer walk holds a placement of a handler's canonical
pre-state; the landed handler span is consumed RELATIONALLY; the walk
must then CONTINUE — including writes to its own (frame) cells —
which requires the post-placement to be handed back in list-determined
form. Here, end to end, on the landed `handleHeartbeat` equation
(hhEquation — the sF-side heartbeat chain's handler; chosen per the
C2a dispatch: the cheapest landed consumer; the witness validates the
INSTRUMENT, not the arm — the heartbeat family's T1-vacuity is
recorded in the U18 log and takes nothing from this demonstration):

1. `swPlacement` — a CONCRETE non-identity placement (`ρT 55 8`, the
   canonical `hhS0` γ-image relocated with an 8-address gap) EXTENDED
   with a frame cell at 57 (`frameSimS_extend`, in the gap: off-image,
   off-heap — the constructor the U15 probe predicted).
2. `sw_consume` — the landed `hh_full_span` consumed at the placement
   via `span_relocateS`: the framed run completes at the same stream,
   and the post-state is handed back as the three-segment SPLICE of
   the canonical post-heap (`γS … hhS3` — concrete) with the frame.
3. `sw_resume` — the outer walk RESUMES: nine machine steps executing
   `*(&57) = 9` — a write to the FRAME cell — proved for the
   handed-back state (the store's one heap-dependent step discharged
   by the placement's `frame_pres`; every other step is a pure
   control step). Exactly the operation the weak relation blocked.
4. `sw_readout` — the consumed span's abstract conclusion at the
   placement (`absOutbox … = [specHeartbeatResp 1 2 0]`), through the
   inherited rename transport.

RESIDUAL (recorded, promotion ledger): the hand-back's split point is
existential in the statement (`∃ pre post`); readouts and frame
operations are split-independent (this file), and the full split
EXTRACTION (separator uniqueness at nonempty frames) is the named
cheap follow-up when a consumer needs the one true literal.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame GoLean.Sym
open GoLean.Surface

/-- The concrete canonical pre-state: the landed equation's §3.3
witness instantiation (valuation `hhρw`, stream head 3). -/
def swσ0 : ExecState := γS (hhρ' hhρw 3) wBase hhS0

/-- The canonical post-state (`hh_full_span`'s right-hand side). -/
def swσ3 : ExecState := γS (hhρ' hhρw 3) wBase hhS3

/-- The shift: identity below 55 (= `hhS0`'s allocator), +8 above —
an 8-address gap [55, 63) for frame cells. -/
def swρ : Nat → Nat := ρT 55 8

/-- The frame: one cell in the gap. -/
def swFrX : Heap := [(.base ⟨57⟩, ⟨some (.int .uint64), .int 42 .uint64⟩)]

theorem sw_bodies : ∀ f ∈ swσ0.functions.toList,
    renameStmt swρ f.body = f.body := by
  have hid : ∀ x < 55, swρ x = x := fun x hx => ρT_lt hx
  exact renameBodies_id hid
    (show funcListSup wBase.functions.toList ≤ 55 by
      rw [wBase_funcSup]; omega)

/-- The relocation seed at the gap shift. -/
theorem sw_reloc : FrameSimS swρ 55 63 [] swσ0 (renameState swρ swσ0) :=
  frameSimS_relocate (shiftSpec_ρT 55 8) (Nat.le_of_eq (by kernel_rfl)) sw_bodies

theorem swFrX_avoid : ∀ a : Nat,
    GoCore.Heap.lookup swFrX (.base ⟨swρ a⟩) = none := by
  intro a
  have hne : (Loc.base ⟨57⟩ : Loc) ≠ .base ⟨swρ a⟩ := by
    intro h
    have h57 : (57 : Nat) = swρ a := by
      have := congrArg (fun l : Loc => match l with
        | .base x => x.id
        | _ => 0) h
      simpa using this
    by_cases hlt : a < 55
    · rw [show swρ a = a from ρT_lt hlt] at h57
      omega
    · rw [show swρ a = a + 8 from ρT_ge (Nat.le_of_not_lt hlt)] at h57
      omega
  simp [swFrX, GoCore.Heap.lookup, hne]

theorem sw_gap_none :
    GoCore.Heap.lookup (renameState swρ swσ0).heap (.base ⟨57⟩) = none := by
  kernel_rfl

theorem swFrX_fresh : ∀ l : Loc, (GoCore.Heap.lookup swFrX l).isSome →
    GoCore.Heap.lookup (renameState swρ swσ0).heap l = none := by
  intro l hl
  have hleq : l = .base ⟨57⟩ := by
    by_cases hb : ((Loc.base ⟨57⟩ : Loc) == l) = true
    · exact (eq_of_beq hb).symm
    · exact absurd hl (by simp [swFrX, GoCore.Heap.lookup, hb])
  rw [hleq]
  exact sw_gap_none

/-- **The concrete placement**: relocation + frame extension. -/
theorem swPlacement : FrameSimS swρ 55 63 swFrX swσ0
    { renameState swρ swσ0 with
        heap := (renameState swρ swσ0).heap ++ swFrX } := by
  have h := frameSimS_extend sw_reloc (by simp [renameState]) swFrX_avoid
    swFrX_fresh
  simpa using h

/-- **THE MID-WALK CONSUMPTION, INSTANTIATED**: the landed span at the
placement — the framed run completes at the same stream and hands back
the post-state as the splice of the CONCRETE canonical post-heap. -/
theorem sw_consume :
    ∃ pre post, swσ3.heap = pre ++ post
      ∧ stepFnIter 1325
          { renameState swρ swσ0 with
              heap := (renameState swρ swσ0).heap ++ swFrX }
          (renameConfig swρ (γC (hhρ' hhρw 3) hhC0)) (3 :: [])
          = .ok (.next .stop,
              { swσ3 with
                  heap := renameHeap swρ pre ++ swFrX ++ renameHeap swρ post,
                  nextAddr := swρ swσ3.nextAddr }, [])
      ∧ FrameSimS swρ 55 63 swFrX swσ3
          { swσ3 with
              heap := renameHeap swρ pre ++ swFrX ++ renameHeap swρ post,
              nextAddr := swρ swσ3.nextAddr } := by
  have hrun : stepFnIter 1325 swσ0 (γC (hhρ' hhρw 3) hhC0) (3 :: [])
      = .ok (.next .stop, swσ3, []) :=
    hh_full_span hhρw wBase ⟨rfl, rfl, rfl, rfl⟩ 3 []
  exact span_relocateS hrun swPlacement

/-- The resume suffix: `*(&57) = 9` — a write to the FRAME cell. -/
def swCsuf : Config :=
  .exec (.assign (.addr (.locLit (.base ⟨57⟩))) (.intLit 9 .uint64)) [] .stop

/-- The storeK configuration five pure control steps into the suffix
(transcribed from the machine trace; every step to here is
state-generic). -/
def swC5 : Config :=
  .next (.storeK
    [Machine.TargetRef.chain (GoValue.addr (.base ⟨57⟩)) [] []]
    [.int 9 .uint64] (.seqn #[]) [] .stop)

def swC6 : Config := .next (.storeK [] [] (.seqn #[]) [] .stop)

/-- **THE LITERAL-STYLE RESUME** (the wall's blocked operation): from
ANY state holding the frame cell — in particular the handed-back
post-state, via `frame_pres` — the nine-step suffix executes and
stores to the frame cell. Every step but the store is a pure control
step (state-generic `rfl`); the store discharges on the lookup. -/
theorem sw_resume {σF : ExecState}
    (h57 : GoCore.Heap.lookup σF.heap (.base ⟨57⟩)
      = some ⟨some (.int .uint64), .int 42 .uint64⟩) :
    stepFnIter 9 σF swCsuf []
      = .ok (.next .stop,
          { σF with heap := (GoCore.Heap.set σF.heap (.base ⟨57⟩)
              ⟨some (.int .uint64), .int 9 .uint64⟩ : Heap) }, []) := by
  have h1 : stepFnIter 5 σF swCsuf [] = .ok (swC5, σF, []) := rfl
  have h2 : stepFn σF swC5 [] = .ok (swC6,
      { σF with heap := (GoCore.Heap.set σF.heap (.base ⟨57⟩)
          ⟨some (.int .uint64), .int 9 .uint64⟩ : Heap) }, []) := by
    have hnorm : normalizeValueForTyFuel typeResolutionFuel σF
        (Ty.int .uint64) (.int 9 .uint64) = .ok (.int 9 .uint64) := rfl
    simp only [stepFn, swC5, swC6, storeTarget, resolveChain, valueAsLoc,
      storeLoc, h57, normalizeValueForTy, hnorm,
      IntKind.normalize, Bind.bind, Except.bind, pure, Except.pure]
  have h3 : ∀ σx : ExecState, stepFnIter 3 σx swC6 [] = .ok (.next .stop, σx, []) :=
    fun σx => rfl
  have h12 := Surface.stepFnIter_chain h1 (GoLean.Surface.stepFnIter_one h2)
  have h123 := Surface.stepFnIter_chain h12 (h3 _)
  simpa using h123

/-- The resume APPLIED to the handed-back state (the end-to-end
composition: consume, then continue writing the outer walk's own
cells). -/
theorem sw_consume_and_resume :
    ∃ pre post, swσ3.heap = pre ++ post
      ∧ stepFnIter 9
          { swσ3 with
              heap := renameHeap swρ pre ++ swFrX ++ renameHeap swρ post,
              nextAddr := swρ swσ3.nextAddr } swCsuf []
        = .ok (.next .stop,
            { swσ3 with
                heap := (GoCore.Heap.set
                  (renameHeap swρ pre ++ swFrX ++ renameHeap swρ post)
                  (.base ⟨57⟩) ⟨some (.int .uint64), .int 9 .uint64⟩ : Heap),
                nextAddr := swρ swσ3.nextAddr }, []) := by
  obtain ⟨pre, post, hsplit, hrunF, hS⟩ := sw_consume
  refine ⟨pre, post, hsplit, ?_⟩
  have h57 := hS.toFrameSim.frame_pres (.base ⟨57⟩)
    ⟨some (.int .uint64), .int 42 .uint64⟩ (by simp [swFrX, GoCore.Heap.lookup])
  exact sw_resume h57

/-- The consumed span's abstract conclusion at the placement (the
readout, through the inherited rename transport; `ρT 55 8` is the
identity on the raft cell 31). -/
theorem sw_readout :
    ∀ (σF : ExecState), FrameSimS swρ 55 63 swFrX swσ3 σF →
      absOutbox σF ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0] := by
  intro σF hS
  have h := absOutbox_ren hS.toFrameSim
    (a := ⟨31⟩) (hh_post_absOutbox hhρw wBase 3)
  have h31 : swρ (31 : Nat) = 31 := ρT_lt (by omega)
  rw [show (⟨swρ (31 : Nat)⟩ : Addr) = ⟨31⟩ from by rw [h31]] at h
  exact h

end GoLean.RaftSeam
