import GoLeanProofs.Specs.Raft.AllocEq
import GoLeanProofs.Specs.Raft.BcEquation
import GoLeanProofs.Specs.Raft.MsEquation

/-!
# A4-U6: the remaining four handler equations, allocation-symbolic

**LINEAGE: as `AllocEq.lean` (separation-logic locality via the
executable frame theorem; design note §7).** The U5 pattern applied
to becomeFollower, becomeCandidate, MemoryStorage.FirstIndex and
MemoryStorage.Term: each `_alloc` form quantifies the footprint
placement (`FrameSim` premise), each concrete predecessor is
re-derived VERBATIM as the identity-placement corollary
(`_of_alloc` — statements identical to the shipped equations, which
stay untouched in their modules), and each ships its §3.3 witness.

New one-time machinery (fixture-independent, survives any fixture
re-siting): `absStorageEnts_ren` — rename-invariance of the storage
projection (the recursive walk: slice base → backing array → per-entry
cells → pointer-scalar derefs) — and `lookup_value_ren` (loc-free
result-cell readouts transfer to the relocated placement).

DEGENERACY NOTE (the A4-U6 finding, recorded loudly in the arc log):
at the CURRENT 0-based fixtures these theorems' `r`-quantifier is
provably identity-only — the twin's function bodies reference every
static address 0..30 (`funcListSup = 31`, probe LocSupProbe2), the
fixtures sit at bases 0..23 ON that range, and `FrameSim.bodies_inv`
forces `r` to fix body-referenced addresses. The theorems are stated
in the placement-quantified FORM so they survive the fixture
re-siting unchanged in shape; the LIVE-relocation demonstration is
`BpcResite.lean` (the re-sited fixture, off the static range).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame

set_option maxRecDepth 8000000

/-! ## One-time transfer machinery (fixture-independent) -/

/-- A loc-free result-cell readout transfers to the relocated
placement. -/
theorem lookup_value_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {b : Addr} {v : GoValue}
    (h : (Heap.lookup σ.heap (.base b)).map (fun c => c.value) = some v)
    (hv : renameValue r v = v) :
    (Heap.lookup σF.heap (.base ⟨r b.id⟩)).map (fun c => c.value)
      = some v := by
  cases hc : Heap.lookup σ.heap (.base b) with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      have hcv : c.value = v := by simpa using h
      have hlk : Heap.lookup σF.heap (.base ⟨r b.id⟩)
          = some (renameCell r c) := hF.lookup_some (l := .base b) hc
      rw [hlk]
      show some ((renameCell r c).value) = some v
      rw [show (renameCell r c).value = renameValue r c.value from rfl,
        hcv, hv]

/-- Pointer-scalar dereference commutes with renaming. -/
theorem derefU64_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {i : Int} (h : derefU64 σ v = some i) :
    derefU64 σF (renameValue r v) = some i := by
  cases v with
  | nil => simpa [derefU64, renameValue] using h
  | addr l =>
      simp only [derefU64, renameValue]
      simp only [derefU64] at h
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          show asU64 (renameCell r c).value = some i
          rw [show (renameCell r c).value = renameValue r c.value from rfl,
            asU64_ren]
          simpa using h
  | _ => simp [derefU64] at h

/-- One `raftpb.Entry` projection commutes with renaming. -/
theorem absEntry_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {p : Int × Int} (h : absEntry σ v = some p) :
    absEntry σF (renameValue r v) = some p := by
  cases v with
  | addr l =>
      simp only [absEntry, renameValue, Option.bind_eq_bind] at h ⊢
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          simp only [Option.bind_some] at h ⊢
          rw [show (renameCell r c).value = renameValue r c.value from rfl]
          split at h
          case _ fs heq =>
            rw [heq]
            simp only [renameValue]
            obtain ⟨idx, hIdx, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨vi, hvi, hdi⟩ := Option.bind_eq_some_iff.mp hIdx
            obtain ⟨tm, hTm, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨vt, hvt, hdt⟩ := Option.bind_eq_some_iff.mp hTm
            simp only [structFieldsLookup_ren, hvi, hvt,
              Option.map_some, Option.bind_some,
              derefU64_ren hF hdi, derefU64_ren hF hdt]
            simpa using h
          case _ => exact absurd h (by simp)
  | _ => simp [absEntry] at h

/-- Renamed backing-array access. -/
theorem renArray_getElem?_ren (r : Nat → Nat) (vs : Array GoValue)
    (i : Nat) :
    ((renameValueList r vs.toList).toArray)[i]?
      = vs[i]?.map (renameValue r) := by
  rw [renameValueList_eq_map]
  simp

/-- The entries walk commutes with renaming (induction over the
window length). -/
theorem absEntsFrom_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    (vs : Array GoValue) :
    ∀ (n i : Nat) {ps : List (Int × Int)},
      absEntsFrom σ vs i n = some ps →
      absEntsFrom σF ((renameValueList r vs.toList).toArray) i n
        = some ps := by
  intro n
  induction n with
  | zero => intro i ps h; simpa [absEntsFrom] using h
  | succ m ih =>
      intro i ps h
      simp only [absEntsFrom, Option.bind_eq_bind] at h ⊢
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
      rw [renArray_getElem?_ren, hv]
      simp only [Option.map_some, Option.bind_some]
      rw [absEntry_ren hF hp]
      simp only [Option.bind_some]
      rw [ih (i + 1) hrest]
      simpa using h

/-- **Storage-projection rename-invariance**: under `FrameSim`, the
`MemoryStorage` entries projection at the relocated address reads the
SAME entry list. One-time; serves every storage-reading handler. -/
theorem absStorageEnts_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {es : List (Int × Int)}
    (h : absStorageEnts σ a = some es) :
    absStorageEnts σF ⟨r a.id⟩ = some es := by
  unfold absStorageEnts at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  cases hc : Heap.lookup σ.heap (.base a) with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      have hlk : Heap.lookup σF.heap (.base ⟨r a.id⟩)
          = some (renameCell r c) := hF.lookup_some (l := .base a) hc
      rw [hlk]
      simp only [Option.bind_some] at h ⊢
      rw [show (renameCell r c).value = renameValue r c.value from rfl]
      split at h
      case _ fs heq =>
        rw [heq]
        simp only [renameValue]
        rw [structFieldsLookup_ren]
        split at h
        case _ sv hsv =>
          rw [hsv]
          simp only [Option.map_some, renameValue]
          obtain ⟨base, hbase, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨arrCell, harr, h⟩ := Option.bind_eq_some_iff.mp h
          rw [hbase]
          simp only [Option.map_some, Option.bind_some]
          rw [hF.lookup_some harr]
          simp only [Option.bind_some]
          rw [show (renameCell r arrCell).value
            = renameValue r arrCell.value from rfl]
          split at h
          case _ vs heqa =>
            rw [heqa]
            simp only [renameValue]
            exact absEntsFrom_ren hF vs sv.len sv.offset h
          case _ => exact absurd h (by simp)
        case _ => exact absurd h (by simp)
      case _ => exact absurd h (by simp)

/-! ## becomeFollower, allocation-symbolic -/

/-- **THE ALLOCATION-SYMBOLIC becomeFollower EQUATION** (U3's
equation, placement-quantified): from the drained
`becomeFollower(0, x₉)` call at ANY placement σF of the populated
fixture, over EVERY consumed choice prefix, the run returns in 3,234
steps with the four choices consumed, the frame preserved, and the
projection at `r 0` stepping by `specBecomeFollower`. -/
theorem becomeFollower_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 9) = ρ.ints 9)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ uS0) σF) :
    ∃ σFfin,
      stepFnIter 3234 σF (renameConfig r (γC ρ uC0))
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (uρ' ρ c₁ c₂ c₃) σ uS13) σFfin
      ∧ absRaftNode σF ⟨r 0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩
      ∧ absRaftNode σFfin ⟨r 0⟩
          = some (specBecomeFollower
              ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩ 0 (ρ.ints 9)) := by
  have hpre : γS ρ σ uS0 = γS (uρ' ρ c₁ c₂ c₃) σ uS0 := by
    kernel_rfl
  have hpreC : γC ρ uC0 = γC (uρ' ρ c₁ c₂ c₃) uC0 := by
    kernel_rfl
  have hrun : stepFnIter 3234 (γS ρ σ uS0) (γC ρ uC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: ch)
      = .ok (.next .stop, γS (uρ' ρ c₁ c₂ c₃) σ uS13, ch) := by
    rw [hpre, hpreC]
    exact bf_full_span ρ σ hag c₁ c₂ c₃ c₄ ch
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 3234 hF
    (γC ρ uC0) (c₁ :: c₂ :: c₃ :: c₄ :: ch)
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  refine ⟨σFfin, htF, hs, ?_, ?_⟩
  · have hpre0 : absRaftNode (γS ρ σ uS0) ⟨0⟩
        = some ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩ := by kernel_rfl
    exact absRaftNode_ren hF hpre0
  · have hpost : absRaftNode (γS (uρ' ρ c₁ c₂ c₃) σ uS13) ⟨0⟩
        = some (specBecomeFollower
            ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩ 0 (ρ.ints 9)) := by
      have hproj : absRaftNode (γS (uρ' ρ c₁ c₂ c₃) σ uS13) ⟨0⟩
          = some ⟨0, unrm 13 (ρ.ints 1), unrm 3 (ρ.ints 9), 0, 1, 1⟩ := by
        kernel_rfl
      rw [hproj, unrm_id hvote 13, unrm_id hlead 3]
      with_unfolding_all rfl
    exact absRaftNode_ren hs hpost

/-- The shipped concrete becomeFollower equation, re-derived at the
identity placement (statement form identical to
`becomeFollower_handler_eq`; strict generalization certified). -/
theorem becomeFollower_handler_eq_of_alloc (ρ : Valuation)
    (σ : ExecState) (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 9) = ρ.ints 9)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 3234 (γS ρ σ uS0) (γC ρ uC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ uS0) ⟨0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeFollower
              ⟨0, ρ.ints 1, ρ.ints 2, ρ.ints 3, 1, 1⟩ 0 (ρ.ints 9)) := by
  have hF : FrameSim (ρT 21 0) 21 21 [] (γS ρ σ uS0) (γS ρ σ uS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 21 f.body)
  obtain ⟨σfin, hrun, _, hpre, hpost⟩ :=
    becomeFollower_handler_eq_alloc ρ σ hag hvote hlead c₁ c₂ c₃ c₄ ch hF
  have hcall : renameConfig (ρT 21 0) (γC ρ uC0) = γC ρ uC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have haddr : (⟨ρT 21 0 0⟩ : Addr) = ⟨0⟩ := rfl
  rw [haddr] at hpre hpost
  exact ⟨σfin, hrun, hpre, hpost⟩

theorem becomeFollower_handler_eq_alloc_witness :
    ∃ σfin,
      stepFnIter 3234 (γS uρw wBase uS0) (γC uρw uC0) [3, 1, 0, 0]
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode (γS uρw wBase uS0) ⟨0⟩ = some ⟨0, 7, 2, 1, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeFollower ⟨0, 7, 2, 1, 1, 1⟩ 0 4) :=
  becomeFollower_handler_eq_of_alloc uρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 1 0 0 []

/-! ## becomeCandidate, allocation-symbolic -/

/-- **THE ALLOCATION-SYMBOLIC becomeCandidate EQUATION** — no side
conditions (every pre-symbolic scalar is overwritten). -/
theorem becomeCandidate_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ bcS0) σF) :
    ∃ σFfin,
      stepFnIter 3282 σF (renameConfig r (γC ρ bcC0))
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (uρ' ρ c₁ c₂ c₃) σ bcS13) σFfin
      ∧ absRaftNode σF ⟨r 0⟩ = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σFfin ⟨r 0⟩
          = some (specBecomeCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ 1) := by
  have hpre : γS ρ σ bcS0 = γS (uρ' ρ c₁ c₂ c₃) σ bcS0 := by
    kernel_rfl
  have hpreC : γC ρ bcC0 = γC (uρ' ρ c₁ c₂ c₃) bcC0 := by
    kernel_rfl
  have hrun : stepFnIter 3282 (γS ρ σ bcS0) (γC ρ bcC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: ch)
      = .ok (.next .stop, γS (uρ' ρ c₁ c₂ c₃) σ bcS13, ch) := by
    rw [hpre, hpreC]
    exact bc_full_span ρ σ hag c₁ c₂ c₃ c₄ ch
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 3282 hF
    (γC ρ bcC0) (c₁ :: c₂ :: c₃ :: c₄ :: ch)
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  refine ⟨σFfin, htF, hs, ?_, ?_⟩
  · have hpre0 : absRaftNode (γS ρ σ bcS0) ⟨0⟩
        = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ := by kernel_rfl
    exact absRaftNode_ren hF hpre0
  · have hpost : absRaftNode (γS (uρ' ρ c₁ c₂ c₃) σ bcS13) ⟨0⟩
        = some (specBecomeCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ 1) := by
      kernel_rfl
    exact absRaftNode_ren hs hpost

/-- The shipped concrete becomeCandidate equation at the identity
placement (statement form identical to `becomeCandidate_handler_eq`). -/
theorem becomeCandidate_handler_eq_of_alloc (ρ : Valuation)
    (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 3282 (γS ρ σ bcS0) (γC ρ bcC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ bcS0) ⟨0⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeCandidate
              ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ 1) := by
  have hF : FrameSim (ρT 21 0) 21 21 [] (γS ρ σ bcS0) (γS ρ σ bcS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 21 f.body)
  obtain ⟨σfin, hrun, _, hpre, hpost⟩ :=
    becomeCandidate_handler_eq_alloc ρ σ hag c₁ c₂ c₃ c₄ ch hF
  have hcall : renameConfig (ρT 21 0) (γC ρ bcC0) = γC ρ bcC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have haddr : (⟨ρT 21 0 0⟩ : Addr) = ⟨0⟩ := rfl
  rw [haddr] at hpre hpost
  exact ⟨σfin, hrun, hpre, hpost⟩

theorem becomeCandidate_handler_eq_alloc_witness :
    ∃ σfin,
      stepFnIter 3282 (γS bcρw wBase bcS0) (γC bcρw bcC0) [3, 1, 0, 0]
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode (γS bcρw wBase bcS0) ⟨0⟩ = some ⟨0, 7, 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨0⟩
          = some (specBecomeCandidate ⟨0, 7, 2, 0, 1, 1⟩ 1) :=
  becomeCandidate_handler_eq_of_alloc bcρw wBase ⟨rfl, rfl, rfl, rfl⟩
    3 1 0 0 []

/-! ## MemoryStorage.FirstIndex, allocation-symbolic -/

/-- **THE ALLOCATION-SYMBOLIC FirstIndex EQUATION**: result-returning
form — the `fi`/`er` result cells and the storage abstraction are all
read AT THE PLACEMENT (`r 21`/`r 22`/`r 6`). -/
theorem msFirstIndex_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ msS0) σF) :
    ∃ σFfin,
      stepFnIter 178 σF (renameConfig r (γC ρ msFiC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ msFiS1) σFfin
      ∧ absStorageEnts σF ⟨r 6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 21⟩)).map (fun c => c.value)
          = ((absStorageEnts σF ⟨r 6⟩).bind specFirstIndex).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σFfin ⟨r 6⟩ = absStorageEnts σF ⟨r 6⟩ := by
  have hrun := msFi_span ρ σ ch hag
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 178 hF
    (γC ρ msFiC0) ch
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  have habs : absStorageEnts σF ⟨r 6⟩ = some [(1, 1)] :=
    absStorageEnts_ren hF (msFi_absPre ρ σ)
  refine ⟨σFfin, htF, hs, habs, ?_, ?_, ?_⟩
  · rw [habs, lookup_value_ren hs (msFi_result ρ σ) rfl]
    with_unfolding_all rfl
  · exact lookup_value_ren hs (msFi_err ρ σ) rfl
  · rw [absStorageEnts_ren hs (msFi_preserve ρ σ), habs]

/-- The shipped concrete FirstIndex equation at the identity
placement (statement form identical to `msFirstIndex_handler_eq`). -/
theorem msFirstIndex_handler_eq_of_alloc (ρ : Valuation)
    (σ : ExecState) (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 178 (γS ρ σ msS0) (γC ρ msFiC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absStorageEnts (γS ρ σ msS0) ⟨6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨21⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS ρ σ msS0) ⟨6⟩).bind specFirstIndex).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨6⟩ = absStorageEnts (γS ρ σ msS0) ⟨6⟩ := by
  have hF : FrameSim (ρT 24 0) 24 24 [] (γS ρ σ msS0) (γS ρ σ msS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 24 f.body)
  obtain ⟨σfin, hrun, _, habs, hres, herr, hpres⟩ :=
    msFirstIndex_handler_eq_alloc ρ σ hag ch hF
  have hcall : renameConfig (ρT 24 0) (γC ρ msFiC0) = γC ρ msFiC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h6 : (⟨ρT 24 0 6⟩ : Addr) = ⟨6⟩ := rfl
  have h21 : (⟨ρT 24 0 21⟩ : Addr) = ⟨21⟩ := rfl
  have h22 : (⟨ρT 24 0 22⟩ : Addr) = ⟨22⟩ := rfl
  rw [h6] at habs hres hpres
  rw [h21] at hres
  rw [h22] at herr
  exact ⟨σfin, hrun, habs, hres, herr, hpres⟩

theorem msFirstIndex_handler_eq_alloc_witness :
    ∃ σfin,
      stepFnIter 178 (γS bcρw wBase msS0) (γC bcρw msFiC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase msS0) ⟨6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨21⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS bcρw wBase msS0) ⟨6⟩).bind
              specFirstIndex).map (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨6⟩ = absStorageEnts (γS bcρw wBase msS0) ⟨6⟩ :=
  msFirstIndex_handler_eq_of_alloc bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

/-! ## MemoryStorage.Term, allocation-symbolic -/

/-- **THE ALLOCATION-SYMBOLIC Term EQUATION** (index 1). -/
theorem msTerm_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ msS0) σF) :
    ∃ σFfin,
      stepFnIter 246 σF (renameConfig r (γC ρ msTmC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ msTmS1) σFfin
      ∧ absStorageEnts σF ⟨r 6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 21⟩)).map (fun c => c.value)
          = ((absStorageEnts σF ⟨r 6⟩).bind
              (fun es => specTermAt es 1)).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σFfin ⟨r 6⟩ = absStorageEnts σF ⟨r 6⟩ := by
  have hrun := msTm_span ρ σ ch hag
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 246 hF
    (γC ρ msTmC0) ch
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  have habs : absStorageEnts σF ⟨r 6⟩ = some [(1, 1)] :=
    absStorageEnts_ren hF (msFi_absPre ρ σ)
  refine ⟨σFfin, htF, hs, habs, ?_, ?_, ?_⟩
  · rw [habs, lookup_value_ren hs (msTm_result ρ σ) rfl]
    with_unfolding_all rfl
  · exact lookup_value_ren hs (msTm_err ρ σ) rfl
  · rw [absStorageEnts_ren hs (msTm_preserve ρ σ), habs]

/-- The shipped concrete Term equation at the identity placement
(statement form identical to `msTerm_handler_eq`). -/
theorem msTerm_handler_eq_of_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 246 (γS ρ σ msS0) (γC ρ msTmC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absStorageEnts (γS ρ σ msS0) ⟨6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨21⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS ρ σ msS0) ⟨6⟩).bind
              (fun es => specTermAt es 1)).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨6⟩ = absStorageEnts (γS ρ σ msS0) ⟨6⟩ := by
  have hF : FrameSim (ρT 24 0) 24 24 [] (γS ρ σ msS0) (γS ρ σ msS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 24 f.body)
  obtain ⟨σfin, hrun, _, habs, hres, herr, hpres⟩ :=
    msTerm_handler_eq_alloc ρ σ hag ch hF
  have hcall : renameConfig (ρT 24 0) (γC ρ msTmC0) = γC ρ msTmC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h6 : (⟨ρT 24 0 6⟩ : Addr) = ⟨6⟩ := rfl
  have h21 : (⟨ρT 24 0 21⟩ : Addr) = ⟨21⟩ := rfl
  have h22 : (⟨ρT 24 0 22⟩ : Addr) = ⟨22⟩ := rfl
  rw [h6] at habs hres hpres
  rw [h21] at hres
  rw [h22] at herr
  exact ⟨σfin, hrun, habs, hres, herr, hpres⟩

theorem msTerm_handler_eq_alloc_witness :
    ∃ σfin,
      stepFnIter 246 (γS bcρw wBase msS0) (γC bcρw msTmC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase msS0) ⟨6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨21⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS bcρw wBase msS0) ⟨6⟩).bind
              (fun es => specTermAt es 1)).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨6⟩ = absStorageEnts (γS bcρw wBase msS0) ⟨6⟩ :=
  msTerm_handler_eq_of_alloc bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

end GoLean.RaftSeam
