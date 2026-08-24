import GoLeanProofs.Specs.Raft.BpcEquation
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.Threshold
import GoLeanProofs.Frame.RenameId

/-!
# A4-U5: the allocation-symbolic handler-equation layer

**LINEAGE (clever-tricks doctrine): separation-logic locality — the
frame rule + relocation lemma of O'Hearn–Reynolds–Yang local
reasoning — realized by the repo's executable frame theorem
(`Frame/`: `FrameSim`, `stepFnIter_sim`; design
`docs/2026-08-13_executable-frame-theorem.md`), composed with the
TableExt-transported spans. Design slice: the sym-extension design
note §7.**

The shipped handler equations hold at the γ-image of a PINNED fixture
— footprint cells at `Loc.base 0..k` in one construction order, the
campaign's flagged accidental-feature risk. This module re-bases the
smallest equation (`becomePreCandidate`, 1 window / 152 steps) on the
frame layer: the new form quantifies over the handler's footprint
PLACEMENT — an arbitrary conforming relocation `r` of the fixture
cells plus an arbitrary disjoint framed remainder `fr`, both carried
by the single `FrameSim` premise ("σF carries this ownership shape at
addresses `r(0..20)`, `fr` inert beside it"). The conclusion returns
the frame-rule shape: same step count, same choice stream, final
state `FrameSim`-related to the fixture's post-image (footprint
transformed, frame preserved), projection at `r 0` stepping by the
spec.

The concrete-fixture statement is re-derived as the corollary at the
identity seed (`becomePreCandidate_handler_eq_of_alloc`, statement
form identical to `becomePreCandidate_handler_eq`) — the
machine-checked proof that the symbolic form STRICTLY generalizes the
shipped one. The §3.3 witness discharges every premise (the
`FrameSim` included) at concrete values.

Honest boundary (design note §7.4): `r` relocates the footprint, it
never reshapes it (layout-shape symbolism is the §5 D-relative
lever); the handler's own fresh region is canonical-sequential from
`na` (`ShiftSpec` — allocator arbitrariness beyond that is exactly
`Frame/AllocIndep`'s quotient); a NON-identity concrete `FrameSim`
instance at this fixture awaits the `frameSim_relocate` builder
(promotion ledger; non-identity liveness of `FrameSim` itself is
kit-witnessed by `swapShift_spec` and the sort examples' rebase
chains).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame

set_option maxRecDepth 8000000

/-! ## Projection rename-invariance (one-time; serves every handler's
pre/post readout — `absRaftNode` is a chain of heap lookups + scalar
field reads, and every ingredient commutes with renaming) -/

/-- Scalar decode is loc-free: renaming never changes a `uint64` read.
(General-shaped helper; parked target-side per the unit's file
boundary — promotion candidate beside `structFieldsLookup_ren`.) -/
theorem asU64_ren (r : Nat → Nat) (v : GoValue) :
    asU64 (renameValue r v) = asU64 v := by
  cases v <;> simp [renameValue, asU64]

/-- `fieldU64` commutes with field-list renaming. -/
theorem fieldU64_ren (r : Nat → Nat) (fs : Array (String × GoValue))
    (name : String) :
    fieldU64 ((renameValueFields r fs.toList).toArray) name
      = fieldU64 fs name := by
  unfold fieldU64
  rw [structFieldsLookup_ren]
  cases StructFields.lookup fs name with
  | none => rfl
  | some v => simpa using asU64_ren r v

/-- **Projection rename-invariance**: under `FrameSim`, the raft-node
projection at the relocated address reads the SAME abstract state —
the footprint's scalar content is placement-independent. -/
theorem absRaftNode_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {n : AbsRaftState} (h : absRaftNode σ a = some n) :
    absRaftNode σF ⟨r a.id⟩ = some n := by
  unfold absRaftNode at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  cases hcell : Heap.lookup σ.heap (.base a) with
  | none => rw [hcell] at h; exact absurd h (by simp)
  | some cell =>
    rw [hcell] at h
    have hlkF : Heap.lookup σF.heap (.base ⟨r a.id⟩)
        = some (renameCell r cell) := hF.lookup_some (l := .base a) hcell
    rw [hlkF]
    simp only [Option.bind_some] at h ⊢
    have hvalF : (renameCell r cell).value = renameValue r cell.value := rfl
    rw [hvalF]
    split at h
    case _ fs heq =>
      rw [heq]
      simp only [renameValue]
      obtain ⟨term, hterm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vote, hvote, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨lead, hlead, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨state, hstate, h⟩ := Option.bind_eq_some_iff.mp h
      rw [fieldU64_ren, hterm, fieldU64_ren, hvote, fieldU64_ren, hlead,
        fieldU64_ren, hstate]
      simp only [Option.bind_some]
      rw [structFieldsLookup_ren]
      split at h
      case _ rl hrl =>
        rw [hrl]
        simp only [Option.map_some, renameValue]
        obtain ⟨rlCell, hrlCell, h⟩ := Option.bind_eq_some_iff.mp h
        have hrlF : Heap.lookup σF.heap (renameLoc r rl)
            = some (renameCell r rlCell) := hF.lookup_some hrlCell
        rw [hrlF]
        simp only [Option.bind_some]
        have hrlvalF : (renameCell r rlCell).value
            = renameValue r rlCell.value := rfl
        rw [hrlvalF]
        split at h
        case _ rfs heqrl =>
          rw [heqrl]
          simp only [renameValue]
          obtain ⟨committed, hcommitted, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨applied, happlied, h⟩ := Option.bind_eq_some_iff.mp h
          rw [fieldU64_ren, hcommitted, fieldU64_ren, happlied]
          simpa using h
        case _ => exact absurd h (by simp)
      case _ => exact absurd h (by simp)
    case _ => exact absurd h (by simp)

/-! ## The allocation-symbolic equation -/

/-- The drained `becomePreCandidate()` call configuration at receiver
address `a` — `bpcC0`'s γ-image with the address symbolic. -/
def bpcCallAt (a : Nat) : Machine.Config :=
  .retV (.addr (.base ⟨a⟩))
    (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)

/-- The renamed γ-image of the pinned call configuration IS the call
at the relocated receiver. -/
theorem bpcCallAt_ren (r : Nat → Nat) (ρ : Valuation) :
    renameConfig r (γC ρ bpcC0) = bpcCallAt (r 0) := by
  with_unfolding_all rfl

/-- The pre-state projection at the pinned placement (the concrete
equation's second conjunct, exposed as a lemma for the transfer). -/
theorem bpc_proj_pre (ρ : Valuation) (σ : ExecState) :
    absRaftNode (γS ρ σ bpcS0) ⟨0⟩
      = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ := by
  kernel_rfl

/-- The post-state projection at the pinned placement (the concrete
equation's third conjunct, exposed as a lemma for the transfer). -/
theorem bpc_proj_post (ρ : Valuation) (σ : ExecState)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1) :
    absRaftNode (γS ρ σ bpcS1) ⟨0⟩
      = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  have hproj : absRaftNode (γS ρ σ bpcS1) ⟨0⟩
      = some ⟨0, unrm 5 (ρ.ints 1), 0, 3, 1, 1⟩ := by
    kernel_rfl
  rw [hproj, unrm_id hvote 5]
  with_unfolding_all rfl

/-- **THE ALLOCATION-SYMBOLIC HANDLER EQUATION** (the U4 equation's
frame-rule generalization): from the drained `becomePreCandidate()`
call at ANY placement `σF` of the fixture's footprint — an arbitrary
conforming relocation `r` with an arbitrary disjoint frame `fr`,
carried by the `FrameSim` premise — over ANY choice stream, the run
returns in 152 steps with the stream untouched, the final state
carries the transformed footprint at the SAME placement with the
frame preserved (`FrameSim` to the fixture's post-image), and the
projection AT THE RELOCATED ADDRESS `r 0` steps by
`specBecomePreCandidate`. Side conditions as in the concrete form:
`hvote` is the surviving symbolic scalar's range fact. -/
theorem becomePreCandidate_handler_eq_alloc
    (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ bpcS0) σF) :
    ∃ σFfin,
      stepFnIter 152 σF (bpcCallAt (r 0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ bpcS1) σFfin
      ∧ absRaftNode σF ⟨r 0⟩ = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σFfin ⟨r 0⟩
          = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  have hspan := bpc_span ρ σ ch hag
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 152 hF (γC ρ bpcC0) ch
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hspan
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop) = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  rw [bpcCallAt_ren r ρ] at htF
  refine ⟨σFfin, htF, hs, ?_, ?_⟩
  · exact absRaftNode_ren hF (bpc_proj_pre ρ σ)
  · exact absRaftNode_ren hs (bpc_proj_post ρ σ hvote)

/-! ## The concrete equation as a corollary (strict generalization,
machine-checked) -/

/-- `ρT T 0` (the zero shift) fixes every statement — the generic
`hbodies` discharge for identity seeds. (General-shaped; belongs
beside `renameStmt_id` in `Frame/RenameId` — promotion ledger.) -/
theorem renameStmt_ρT_zero (T : Nat) (s : Stmt) :
    renameStmt (ρT T 0) s = s :=
  renameStmt_id (n := Stmt.locSup s) (fun x _ => ρT_zero_app T x) s
    (Nat.le_refl _)

/-- **The shipped concrete equation, re-derived from the symbolic
form at the identity seed** — statement form identical to
`becomePreCandidate_handler_eq` (BpcEquation.lean, untouched). This
theorem existing IS the proof that the allocation-symbolic form
strictly generalizes the pinned-fixture one. -/
theorem becomePreCandidate_handler_eq_of_alloc
    (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (ch : Choices) :
    ∃ σfin,
      stepFnIter 152 (γS ρ σ bpcS0) (γC ρ bpcC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ bpcS0) ⟨0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  have hF : FrameSim (ρT 21 0) 21 21 [] (γS ρ σ bpcS0) (γS ρ σ bpcS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 21 f.body)
  obtain ⟨σfin, hrun, _, hpre, hpost⟩ :=
    becomePreCandidate_handler_eq_alloc ρ σ hag hvote ch hF
  have hcall : bpcCallAt (ρT 21 0 0) = γC ρ bpcC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have haddr : (⟨ρT 21 0 0⟩ : Addr) = ⟨0⟩ := rfl
  rw [haddr] at hpre hpost
  exact ⟨σfin, hrun, hpre, hpost⟩

/-! ## Discharge witness (constitution §3.3): every premise of the
allocation-symbolic equation at concrete values — `wBase` tables,
Vote 7 / lead 2 / leadTransferee 5, the empty stream, and the
`FrameSim` premise at the identity seed. -/

theorem becomePreCandidate_handler_eq_alloc_witness :
    ∃ σfin,
      stepFnIter 152 (γS bpcρw wBase bpcS0) (γC bpcρw bpcC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode (γS bpcρw wBase bpcS0) ⟨0⟩ = some ⟨0, 7, 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomePreCandidate ⟨0, 7, 2, 0, 1, 1⟩) :=
  becomePreCandidate_handler_eq_of_alloc bpcρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) []

end GoLean.RaftSeam
