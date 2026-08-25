import GoLeanProofs.Specs.Raft.MsResite
import GoLeanProofs.Specs.Raft.StaticCells

/-!
# A4-U13: THE MemoryStorage.Term ERROR-BRANCH EQUATIONS — the U4
residual closed, and THE STATIC-CELL COMPLEMENT's SECOND CONSUMER
(the generality claim validated on a path DISJOINT from log-append)

The U4 record: "the Term ERROR branches (the lowered error path loads
package-level error vars at static twin addresses the leaf fixture
does not carry)". With `StaticCells.lean` (U12) in the fixture, both
branches run choice-free, single-window, mirror end-to-end clean
(probe `MsErrProbe`, census before any theorem):

- `Term(0)` → **ErrCompacted** (static cell 23, payload 83): 159
  steps — the `i < offset` branch.
- `Term(5)` → **ErrUnavailable** (static cell 25, payload 91): 180
  steps — the past-lastIndex branch (the SAME cell whose absence
  stuck the U11 log-append census).

THE CONCLUSION SHAPE: the spec side (`specTermAt`) answers **`none`**
at both indexes — the spec's out-of-range arm — and the machine
returns `(0, err)` where **the error is IDENTICALLY the package-level
var** (the er result cell and the static root cell hold the SAME
interface value, stated as two lookups; under relocation both rename
together). Fail-closed correspondence: the spec does not distinguish
WHICH error; the machine-level identity conclusions carry that
distinction — recorded, not blurred.

Fixture = `ms31SymHeap` (the U8 re-sited Ms fixture, UNCHANGED) ++
`staticComplementSym`, `nextAddr₀ = staticComplementNa = 98` — the
complement composes with a landed fixture by APPEND alone, the
generality claim's design test.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-- The U8 Ms fixture ++ the static-cell complement (append-only
composition; consumers start at `staticComplementNa`). -/
def mseS0 : SymState :=
  { heap := ms31SymHeap ++ staticComplementSym,
    nextAddr := staticComplementNa }

def errCompactedV : GoValue :=
  .interface (.pointer (.defined ⟨"raft.goleanShimErrorString"⟩))
    (.addr (.base ⟨83⟩))
def errUnavailableV : GoValue :=
  .interface (.pointer (.defined ⟨"raft.goleanShimErrorString"⟩))
    (.addr (.base ⟨91⟩))

/-- `lookup_value_ren` without the loc-free premise: the framed
lookup answers the RENAMED value (the error interfaces carry their
payload addr). Local sibling of `AllocEqWave1.lookup_value_ren`
(promotion note: second consumer would lift it beside the original). -/
theorem lookup_value_renV {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {b : Addr} {v : GoValue}
    (h : (Heap.lookup σ.heap (.base b)).map (fun c => c.value) = some v) :
    (Heap.lookup σF.heap (.base ⟨r b.id⟩)).map (fun c => c.value)
      = some (renameValue r v) := by
  cases hc : Heap.lookup σ.heap (.base b) with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      have hcv : c.value = v := by simpa using h
      have hlk : Heap.lookup σF.heap (.base ⟨r b.id⟩)
          = some (renameCell r c) := hF.lookup_some (l := .base b) hc
      rw [hlk]
      show some ((renameCell r c).value) = some (renameValue r v)
      rw [show (renameCell r c).value = renameValue r c.value from rfl, hcv]

/-! ## Term(0) → ErrCompacted (window 159, choice-free). -/

def mseErrCompactedC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩
    #[Expr.var "ms", Expr.intLit 0 .uint64]) ms31Env .stop

def mseErrCompactedS1 : SymState := (symEvalWindowTB bfTB 159 mseS0 mseErrCompactedC0).2.1

theorem mseErrCompactedW_n : (symEvalWindowTB bfTB 159 mseS0 mseErrCompactedC0).1 = 159 := by
  kernel_rfl

theorem mseErrCompactedC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 159 mseS0 mseErrCompactedC0).2.2 = .next .stop := by
  kernel_rfl

theorem mseErrCompacted_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 159 (γS ρ σ mseS0) (γC ρ mseErrCompactedC0) ch
      = .ok (.next .stop, γS ρ σ mseErrCompactedS1, ch) := by
  have h := symEvalWindowTB_refines' mseErrCompactedW_n ρ σ ch hag
  rw [mseErrCompactedC1_stop ρ] at h
  exact h

theorem mseErrCompacted_absPre (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ mseS0) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

/-- The spec's `none` arm: index 0 is outside the storage range. -/
theorem mseErrCompacted_spec_none : specTermAt [(1, 1)] 0 = none := by decide

theorem mseErrCompacted_result (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ mseErrCompactedS1).heap (.base ⟨52⟩)).map (fun c => c.value)
      = some (.int 0 .uint64) := by
  kernel_rfl

theorem mseErrCompacted_err (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ mseErrCompactedS1).heap (.base ⟨53⟩)).map (fun c => c.value)
      = some errCompactedV := by
  kernel_rfl

/-- The returned error IS the package-level var: the er result equals
the static cell 23's stored value, post-state. -/
theorem mseErrCompacted_errIsStatic (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ mseErrCompactedS1).heap (.base ⟨23⟩)).map (fun c => c.value)
      = some errCompactedV := by
  kernel_rfl

theorem mseErrCompacted_preserve (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ mseErrCompactedS1) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

/-- **THE Term-ErrCompacted ERROR-BRANCH EQUATION** (allocation-symbolic
PRIMARY): the run completes choice-free in 159 steps; the spec's
`specTermAt` answers `none` at index 0, and the machine returns
`(0, ErrCompacted)` with the error IDENTICALLY the package-level var (the
er result and the static cell 23 hold the same interface
value); the storage is untouched. -/
theorem msTerm_ErrCompacted_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ mseS0) σF) :
    ∃ σFfin,
      stepFnIter 159 σF (renameConfig r (γC ρ mseErrCompactedC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ mseErrCompactedS1) σFfin
      ∧ absStorageEnts σF ⟨r 37⟩ = some [(1, 1)]
      ∧ ((absStorageEnts σF ⟨r 37⟩).bind
          (fun es => specTermAt es 0)) = none
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 52⟩)).map (fun c => c.value)
          = some (.int 0 .uint64)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 53⟩)).map (fun c => c.value)
          = some (renameValue r errCompactedV)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 23⟩)).map (fun c => c.value)
          = some (renameValue r errCompactedV)
      ∧ absStorageEnts σFfin ⟨r 37⟩ = absStorageEnts σF ⟨r 37⟩ := by
  have hrun := mseErrCompacted_span ρ σ ch hag
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  have habs : absStorageEnts σF ⟨r 37⟩ = some [(1, 1)] :=
    absStorageEnts_ren hF (mseErrCompacted_absPre ρ σ)
  refine ⟨σFfin, htF, hs, habs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [habs]
    with_unfolding_all rfl
  · exact lookup_value_ren hs (mseErrCompacted_result ρ σ) rfl
  · exact lookup_value_renV hs (mseErrCompacted_err ρ σ)
  · exact lookup_value_renV hs (mseErrCompacted_errIsStatic ρ σ)
  · rw [absStorageEnts_ren hs (mseErrCompacted_preserve ρ σ), habs]

/-- The identity-placement corollary. -/
theorem msTerm_ErrCompacted_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 159 (γS ρ σ mseS0) (γC ρ mseErrCompactedC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absStorageEnts (γS ρ σ mseS0) ⟨37⟩ = some [(1, 1)]
      ∧ ((absStorageEnts (γS ρ σ mseS0) ⟨37⟩).bind
          (fun es => specTermAt es 0)) = none
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = some (.int 0 .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some errCompactedV
      ∧ (Heap.lookup σfin.heap (.base ⟨23⟩)).map (fun c => c.value)
          = some errCompactedV
      ∧ absStorageEnts σfin ⟨37⟩ = absStorageEnts (γS ρ σ mseS0) ⟨37⟩ := by
  have hF : FrameSim (ρT 98 0) 98 98 [] (γS ρ σ mseS0) (γS ρ σ mseS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 98 f.body)
  obtain ⟨σfin, hrun, _, habs, hspec, hres, herr, hid, hpres⟩ :=
    msTerm_ErrCompacted_eq_alloc ρ σ hag ch hF
  have hcall : renameConfig (ρT 98 0) (γC ρ mseErrCompactedC0) = γC ρ mseErrCompactedC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h37 : (⟨ρT 98 0 37⟩ : Addr) = ⟨37⟩ := rfl
  have h52 : (⟨ρT 98 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h53 : (⟨ρT 98 0 53⟩ : Addr) = ⟨53⟩ := rfl
  have hec : (⟨ρT 98 0 23⟩ : Addr) = ⟨23⟩ := rfl
  have hrv : renameValue (ρT 98 0) errCompactedV = errCompactedV := by
    with_unfolding_all rfl
  rw [h37] at habs hspec hpres
  rw [h52] at hres
  rw [h53, hrv] at herr
  rw [hec, hrv] at hid
  exact ⟨σfin, hrun, habs, hspec, hres, herr, hid, hpres⟩

/-- Discharge witness (§3.3). -/
theorem msTerm_ErrCompacted_eq_witness :
    ∃ σfin,
      stepFnIter 159 (γS bcρw wBase mseS0) (γC bcρw mseErrCompactedC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase mseS0) ⟨37⟩ = some [(1, 1)]
      ∧ ((absStorageEnts (γS bcρw wBase mseS0) ⟨37⟩).bind
          (fun es => specTermAt es 0)) = none
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = some (.int 0 .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some errCompactedV
      ∧ (Heap.lookup σfin.heap (.base ⟨23⟩)).map (fun c => c.value)
          = some errCompactedV
      ∧ absStorageEnts σfin ⟨37⟩
          = absStorageEnts (γS bcρw wBase mseS0) ⟨37⟩ :=
  msTerm_ErrCompacted_eq bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

/-! ## Term(5) → ErrUnavailable (window 180, choice-free). -/

def mseErrUnavailableC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩
    #[Expr.var "ms", Expr.intLit 5 .uint64]) ms31Env .stop

def mseErrUnavailableS1 : SymState := (symEvalWindowTB bfTB 180 mseS0 mseErrUnavailableC0).2.1

theorem mseErrUnavailableW_n : (symEvalWindowTB bfTB 180 mseS0 mseErrUnavailableC0).1 = 180 := by
  kernel_rfl

theorem mseErrUnavailableC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 180 mseS0 mseErrUnavailableC0).2.2 = .next .stop := by
  kernel_rfl

theorem mseErrUnavailable_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 180 (γS ρ σ mseS0) (γC ρ mseErrUnavailableC0) ch
      = .ok (.next .stop, γS ρ σ mseErrUnavailableS1, ch) := by
  have h := symEvalWindowTB_refines' mseErrUnavailableW_n ρ σ ch hag
  rw [mseErrUnavailableC1_stop ρ] at h
  exact h

theorem mseErrUnavailable_absPre (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ mseS0) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

/-- The spec's `none` arm: index 5 is outside the storage range. -/
theorem mseErrUnavailable_spec_none : specTermAt [(1, 1)] 5 = none := by decide

theorem mseErrUnavailable_result (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ mseErrUnavailableS1).heap (.base ⟨52⟩)).map (fun c => c.value)
      = some (.int 0 .uint64) := by
  kernel_rfl

theorem mseErrUnavailable_err (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ mseErrUnavailableS1).heap (.base ⟨53⟩)).map (fun c => c.value)
      = some errUnavailableV := by
  kernel_rfl

/-- The returned error IS the package-level var: the er result equals
the static cell 25's stored value, post-state. -/
theorem mseErrUnavailable_errIsStatic (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ mseErrUnavailableS1).heap (.base ⟨25⟩)).map (fun c => c.value)
      = some errUnavailableV := by
  kernel_rfl

theorem mseErrUnavailable_preserve (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ mseErrUnavailableS1) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

/-- **THE Term-ErrUnavailable ERROR-BRANCH EQUATION** (allocation-symbolic
PRIMARY): the run completes choice-free in 180 steps; the spec's
`specTermAt` answers `none` at index 5, and the machine returns
`(0, ErrUnavailable)` with the error IDENTICALLY the package-level var (the
er result and the static cell 25 hold the same interface
value); the storage is untouched. -/
theorem msTerm_ErrUnavailable_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ mseS0) σF) :
    ∃ σFfin,
      stepFnIter 180 σF (renameConfig r (γC ρ mseErrUnavailableC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ mseErrUnavailableS1) σFfin
      ∧ absStorageEnts σF ⟨r 37⟩ = some [(1, 1)]
      ∧ ((absStorageEnts σF ⟨r 37⟩).bind
          (fun es => specTermAt es 5)) = none
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 52⟩)).map (fun c => c.value)
          = some (.int 0 .uint64)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 53⟩)).map (fun c => c.value)
          = some (renameValue r errUnavailableV)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 25⟩)).map (fun c => c.value)
          = some (renameValue r errUnavailableV)
      ∧ absStorageEnts σFfin ⟨r 37⟩ = absStorageEnts σF ⟨r 37⟩ := by
  have hrun := mseErrUnavailable_span ρ σ ch hag
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  have habs : absStorageEnts σF ⟨r 37⟩ = some [(1, 1)] :=
    absStorageEnts_ren hF (mseErrUnavailable_absPre ρ σ)
  refine ⟨σFfin, htF, hs, habs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [habs]
    with_unfolding_all rfl
  · exact lookup_value_ren hs (mseErrUnavailable_result ρ σ) rfl
  · exact lookup_value_renV hs (mseErrUnavailable_err ρ σ)
  · exact lookup_value_renV hs (mseErrUnavailable_errIsStatic ρ σ)
  · rw [absStorageEnts_ren hs (mseErrUnavailable_preserve ρ σ), habs]

/-- The identity-placement corollary. -/
theorem msTerm_ErrUnavailable_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 180 (γS ρ σ mseS0) (γC ρ mseErrUnavailableC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absStorageEnts (γS ρ σ mseS0) ⟨37⟩ = some [(1, 1)]
      ∧ ((absStorageEnts (γS ρ σ mseS0) ⟨37⟩).bind
          (fun es => specTermAt es 5)) = none
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = some (.int 0 .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some errUnavailableV
      ∧ (Heap.lookup σfin.heap (.base ⟨25⟩)).map (fun c => c.value)
          = some errUnavailableV
      ∧ absStorageEnts σfin ⟨37⟩ = absStorageEnts (γS ρ σ mseS0) ⟨37⟩ := by
  have hF : FrameSim (ρT 98 0) 98 98 [] (γS ρ σ mseS0) (γS ρ σ mseS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 98 f.body)
  obtain ⟨σfin, hrun, _, habs, hspec, hres, herr, hid, hpres⟩ :=
    msTerm_ErrUnavailable_eq_alloc ρ σ hag ch hF
  have hcall : renameConfig (ρT 98 0) (γC ρ mseErrUnavailableC0) = γC ρ mseErrUnavailableC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h37 : (⟨ρT 98 0 37⟩ : Addr) = ⟨37⟩ := rfl
  have h52 : (⟨ρT 98 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h53 : (⟨ρT 98 0 53⟩ : Addr) = ⟨53⟩ := rfl
  have hec : (⟨ρT 98 0 25⟩ : Addr) = ⟨25⟩ := rfl
  have hrv : renameValue (ρT 98 0) errUnavailableV = errUnavailableV := by
    with_unfolding_all rfl
  rw [h37] at habs hspec hpres
  rw [h52] at hres
  rw [h53, hrv] at herr
  rw [hec, hrv] at hid
  exact ⟨σfin, hrun, habs, hspec, hres, herr, hid, hpres⟩

/-- Discharge witness (§3.3). -/
theorem msTerm_ErrUnavailable_eq_witness :
    ∃ σfin,
      stepFnIter 180 (γS bcρw wBase mseS0) (γC bcρw mseErrUnavailableC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase mseS0) ⟨37⟩ = some [(1, 1)]
      ∧ ((absStorageEnts (γS bcρw wBase mseS0) ⟨37⟩).bind
          (fun es => specTermAt es 5)) = none
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = some (.int 0 .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some errUnavailableV
      ∧ (Heap.lookup σfin.heap (.base ⟨25⟩)).map (fun c => c.value)
          = some errUnavailableV
      ∧ absStorageEnts σfin ⟨37⟩
          = absStorageEnts (γS bcρw wBase mseS0) ⟨37⟩ :=
  msTerm_ErrUnavailable_eq bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

end GoLean.RaftSeam
