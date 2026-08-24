import GoLeanProofs.Specs.Raft.BpcResite

/-!
# A4-U8 part 2a: the re-sited MemoryStorage leaf fixture (FirstIndex/Term)

**LINEAGE: as `BpcResite.lean` (separation-logic locality; the
renaming lemma) — the U6 re-siting pattern at the RESULT-RETURNING
equation form.**

The U6 charter's consolidation residual, Ms half: the U4 leaf fixture
sits at bases 0..23 ON the static locLit range, so its `_alloc`
equations' placement quantifier is provably identity-only (the U6
finding). Re-sited here: every cell `+31` (the Ms happy path reads NO
static cell — probe `Ms31Probe`: FirstIndex 178 / Term 246 steps at
the shifted fixture, `.next .stop`, stream untouched, γ-image ==
machine heap, all projections exact at the shifted addresses), result
cells at 52/53, receiver pointer cell at 54 → MemoryStorage at 37,
allocator 55. The `_alloc` forms below are PRIMARY (wave-2 charter
item 1: symbolic-from-birth); the identity corollaries are their
concrete readouts. The shipped 0-based `MsEquation`/`AllocEqWave1`
statements are UNTOUCHED.

The Term ERROR branches stay the U4 recorded residual (the lowered
error path loads package-level error vars at static twin addresses —
NOTE: at a re-sited fixture those statics are genuinely absent, so
the residual is now cleanly separable: an error-branch fixture would
add the true static error cells at their `[0,31)` addresses, which
re-siting leaves free — recorded, not attempted).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000

/-! ## The re-sited fixture -/

def ms31SymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (msHeapExt 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (renameLoc sh31 l, .mk c.declaredTy bpc31SymRaft)
    else (renameLoc sh31 l,
      .mk c.declaredTy (embedGo (renameValue sh31 c.value))))

def ms31S0 : SymState := { heap := ms31SymHeap, nextAddr := 55 }

def ms31Env : LocalEnv :=
  [[("fi", .base ⟨52⟩), ("er", .base ⟨53⟩), ("ms", .base ⟨54⟩)]]

def ms31FiC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.FirstIndex"⟩
    #[Expr.var "ms"]) ms31Env .stop

def ms31TmC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩
    #[Expr.var "ms", Expr.intLit 1 .uint64]) ms31Env .stop

def ms31FiS1 : SymState := (symEvalWindowTB bfTB 178 ms31S0 ms31FiC0).2.1
def ms31TmS1 : SymState := (symEvalWindowTB bfTB 246 ms31S0 ms31TmC0).2.1

/-! ## FirstIndex: window + per-conjunct facts (each its own decl —
the U4 kernel-budget lesson) -/

theorem ms31FiW_n : (symEvalWindowTB bfTB 178 ms31S0 ms31FiC0).1 = 178 := by
  kernel_rfl

theorem ms31FiC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 178 ms31S0 ms31FiC0).2.2 = .next .stop := by
  kernel_rfl

theorem ms31Fi_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 178 (γS ρ σ ms31S0) (γC ρ ms31FiC0) ch
      = .ok (.next .stop, γS ρ σ ms31FiS1, ch) := by
  have h := symEvalWindowTB_refines' ms31FiW_n ρ σ ch hag
  rw [ms31FiC1_stop ρ] at h
  exact h

theorem ms31Fi_absPre (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ ms31S0) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

theorem ms31Fi_result (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ ms31FiS1).heap (.base ⟨52⟩)).map (fun c => c.value)
      = some (.int 2 .uint64) := by
  kernel_rfl

theorem ms31Fi_err (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ ms31FiS1).heap (.base ⟨53⟩)).map (fun c => c.value)
      = some .nil := by
  kernel_rfl

theorem ms31Fi_preserve (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ ms31FiS1) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

/-- **THE RE-SITED ALLOCATION-SYMBOLIC FirstIndex EQUATION** (primary
form; the placement quantifier is LIVE — any `r` fixing the statics
`[0,31)` may move the whole footprint, `wBase_bodies_inv` is the
generic discharge). -/
theorem msFirstIndex_handler_eq_alloc31 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ ms31S0) σF) :
    ∃ σFfin,
      stepFnIter 178 σF (renameConfig r (γC ρ ms31FiC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ ms31FiS1) σFfin
      ∧ absStorageEnts σF ⟨r 37⟩ = some [(1, 1)]
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 52⟩)).map (fun c => c.value)
          = ((absStorageEnts σF ⟨r 37⟩).bind specFirstIndex).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 53⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σFfin ⟨r 37⟩ = absStorageEnts σF ⟨r 37⟩ := by
  have hrun := ms31Fi_span ρ σ ch hag
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 178 hF
    (γC ρ ms31FiC0) ch
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  have habs : absStorageEnts σF ⟨r 37⟩ = some [(1, 1)] :=
    absStorageEnts_ren hF (ms31Fi_absPre ρ σ)
  refine ⟨σFfin, htF, hs, habs, ?_, ?_, ?_⟩
  · rw [habs, lookup_value_ren hs (ms31Fi_result ρ σ) rfl]
    with_unfolding_all rfl
  · exact lookup_value_ren hs (ms31Fi_err ρ σ) rfl
  · rw [absStorageEnts_ren hs (ms31Fi_preserve ρ σ), habs]

/-- The identity-placement corollary (the re-sited fixture's concrete
form). -/
theorem msFirstIndex_handler_eq_alloc31_id (ρ : Valuation)
    (σ : ExecState) (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 178 (γS ρ σ ms31S0) (γC ρ ms31FiC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absStorageEnts (γS ρ σ ms31S0) ⟨37⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS ρ σ ms31S0) ⟨37⟩).bind specFirstIndex).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨37⟩ = absStorageEnts (γS ρ σ ms31S0) ⟨37⟩ := by
  have hF : FrameSim (ρT 55 0) 55 55 [] (γS ρ σ ms31S0) (γS ρ σ ms31S0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 55 f.body)
  obtain ⟨σfin, hrun, _, habs, hres, herr, hpres⟩ :=
    msFirstIndex_handler_eq_alloc31 ρ σ hag ch hF
  have hcall : renameConfig (ρT 55 0) (γC ρ ms31FiC0) = γC ρ ms31FiC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h37 : (⟨ρT 55 0 37⟩ : Addr) = ⟨37⟩ := rfl
  have h52 : (⟨ρT 55 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h53 : (⟨ρT 55 0 53⟩ : Addr) = ⟨53⟩ := rfl
  rw [h37] at habs hres hpres
  rw [h52] at hres
  rw [h53] at herr
  exact ⟨σfin, hrun, habs, hres, herr, hpres⟩

theorem msFirstIndex_handler_eq_alloc31_witness :
    ∃ σfin,
      stepFnIter 178 (γS bcρw wBase ms31S0) (γC bcρw ms31FiC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩).bind
              specFirstIndex).map (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨37⟩
          = absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩ :=
  msFirstIndex_handler_eq_alloc31_id bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

/-! ## Term (index 1; error branches the recorded residual) -/

theorem ms31TmW_n : (symEvalWindowTB bfTB 246 ms31S0 ms31TmC0).1 = 246 := by
  kernel_rfl

theorem ms31TmC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 246 ms31S0 ms31TmC0).2.2 = .next .stop := by
  kernel_rfl

theorem ms31Tm_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 246 (γS ρ σ ms31S0) (γC ρ ms31TmC0) ch
      = .ok (.next .stop, γS ρ σ ms31TmS1, ch) := by
  have h := symEvalWindowTB_refines' ms31TmW_n ρ σ ch hag
  rw [ms31TmC1_stop ρ] at h
  exact h

theorem ms31Tm_result (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ ms31TmS1).heap (.base ⟨52⟩)).map (fun c => c.value)
      = some (.int 1 .uint64) := by
  kernel_rfl

theorem ms31Tm_err (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ ms31TmS1).heap (.base ⟨53⟩)).map (fun c => c.value)
      = some .nil := by
  kernel_rfl

theorem ms31Tm_preserve (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ ms31TmS1) ⟨37⟩ = some [(1, 1)] := by
  kernel_rfl

/-- **THE RE-SITED ALLOCATION-SYMBOLIC Term EQUATION** (index 1). -/
theorem msTerm_handler_eq_alloc31 (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ ms31S0) σF) :
    ∃ σFfin,
      stepFnIter 246 σF (renameConfig r (γC ρ ms31TmC0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ ms31TmS1) σFfin
      ∧ absStorageEnts σF ⟨r 37⟩ = some [(1, 1)]
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 52⟩)).map (fun c => c.value)
          = ((absStorageEnts σF ⟨r 37⟩).bind
              (fun es => specTermAt es 1)).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σFfin.heap (.base ⟨r 53⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σFfin ⟨r 37⟩ = absStorageEnts σF ⟨r 37⟩ := by
  have hrun := ms31Tm_span ρ σ ch hag
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 246 hF
    (γC ρ ms31TmC0) ch
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  have habs : absStorageEnts σF ⟨r 37⟩ = some [(1, 1)] :=
    absStorageEnts_ren hF (ms31Fi_absPre ρ σ)
  refine ⟨σFfin, htF, hs, habs, ?_, ?_, ?_⟩
  · rw [habs, lookup_value_ren hs (ms31Tm_result ρ σ) rfl]
    with_unfolding_all rfl
  · exact lookup_value_ren hs (ms31Tm_err ρ σ) rfl
  · rw [absStorageEnts_ren hs (ms31Tm_preserve ρ σ), habs]

/-- The identity-placement corollary. -/
theorem msTerm_handler_eq_alloc31_id (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ σfin,
      stepFnIter 246 (γS ρ σ ms31S0) (γC ρ ms31TmC0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absStorageEnts (γS ρ σ ms31S0) ⟨37⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS ρ σ ms31S0) ⟨37⟩).bind
              (fun es => specTermAt es 1)).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨37⟩ = absStorageEnts (γS ρ σ ms31S0) ⟨37⟩ := by
  have hF : FrameSim (ρT 55 0) 55 55 [] (γS ρ σ ms31S0) (γS ρ σ ms31S0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 55 f.body)
  obtain ⟨σfin, hrun, _, habs, hres, herr, hpres⟩ :=
    msTerm_handler_eq_alloc31 ρ σ hag ch hF
  have hcall : renameConfig (ρT 55 0) (γC ρ ms31TmC0) = γC ρ ms31TmC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h37 : (⟨ρT 55 0 37⟩ : Addr) = ⟨37⟩ := rfl
  have h52 : (⟨ρT 55 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h53 : (⟨ρT 55 0 53⟩ : Addr) = ⟨53⟩ := rfl
  rw [h37] at habs hres hpres
  rw [h52] at hres
  rw [h53] at herr
  exact ⟨σfin, hrun, habs, hres, herr, hpres⟩

theorem msTerm_handler_eq_alloc31_witness :
    ∃ σfin,
      stepFnIter 246 (γS bcρw wBase ms31S0) (γC bcρw ms31TmC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨52⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩).bind
              (fun es => specTermAt es 1)).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨53⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨37⟩
          = absStorageEnts (γS bcρw wBase ms31S0) ⟨37⟩ :=
  msTerm_handler_eq_alloc31_id bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

end GoLean.RaftSeam
