import GoLeanProofs.Specs.Raft.BcEquation

/-!
# A4-U4 wave 1: the MemoryStorage leaf equations — `FirstIndex`, `Term`

The wave table's LastIndex-shaped storage leaves: window-only, NO
choice sites, called through a CALLER-SHAPED `Stmt.call` with two
`var` targets (`fi`, `er`) — the first RESULT-returning handler
equations, so the correspondence reads the RESULT CELLS against the
spec function applied to the PRE state's storage abstraction
(`absStorageEnts`, the wave-1 additive AbsState extension closing
GAP-V1-1a).

Probe provenance (`artifacts/probe/MsProbe2.lean`): FirstIndex runs
178 steps → fi = 2 (= ents[0].Index + 1), er = nil; Term(1) runs 246
steps → fi = 1, er = nil; both mirror windows land `.next .stop` with
γ-image == machine heap. The ERROR branches (Term below the offset →
`ErrCompacted`) are a RECORDED RESIDUAL, not covered: the lowered
error path loads package-level error vars at static twin addresses
this leaf fixture does not carry (the probe's Term(0) run showed the
address collision loudly).

Scope note, logged: `MemoryStorage.Entries` is NOT attempted in this
slice — its result passes through `limitSize`/`entryEncodingSize`
(a size-accounting walk), whose spec-side re-grounding is a design
task of its own; scoped out with this reason rather than modeled
loosely (fail closed over guessed spec).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000

/-! ## The leaf fixture: the populated heap + three caller cells —
fi (result 1, uint64), er (result 2), ms (the receiver pointer). -/

def msHeapExt (vote lead state ldT : Int) : GoCore.Heap :=
  uHeap vote lead state ldT ++
  [(.base ⟨21⟩, ⟨some (.int .uint64), .int 0 .uint64⟩),
   (.base ⟨22⟩, ⟨none, .nil⟩),
   (.base ⟨23⟩, ⟨none, .addr (.base ⟨6⟩)⟩)]

def msEnv : LocalEnv := [[("fi", .base ⟨21⟩), ("er", .base ⟨22⟩), ("ms", .base ⟨23⟩)]]

def msSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (msHeapExt 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (l, .mk c.declaredTy bcSymRaft)
    else (l, .mk c.declaredTy (embedGo c.value)))

def msS0 : SymState := { heap := msSymHeap, nextAddr := 24 }

def msFiC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.FirstIndex"⟩
    #[Expr.var "ms"]) msEnv .stop

def msTmC0 : SymConfig :=
  .exec (.call #[.var "fi", .var "er"] ⟨"raft.MemoryStorage.Term"⟩
    #[Expr.var "ms", Expr.intLit 1 .uint64]) msEnv .stop

def msFiS1 : SymState := (symEvalWindowTB bfTB 178 msS0 msFiC0).2.1
def msTmS1 : SymState := (symEvalWindowTB bfTB 246 msS0 msTmC0).2.1

/-! ## FirstIndex -/

theorem msFiW_n : (symEvalWindowTB bfTB 178 msS0 msFiC0).1 = 178 := by
  kernel_rfl

theorem msFiC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 178 msS0 msFiC0).2.2 = .next .stop := by
  kernel_rfl

theorem msFi_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 178 (γS ρ σ msS0) (γC ρ msFiC0) ch
      = .ok (.next .stop, γS ρ σ msFiS1, ch) := by
  have h := symEvalWindowTB_refines' msFiW_n ρ σ ch hag
  rw [msFiC1_stop ρ] at h
  exact h

/-! Per-conjunct facts, each its OWN declaration (one kernel window
re-evaluation each; bundling all four into one `addDecl` measurably
blows the kernel budget — the check does not share reduction work
across conjuncts of a single declaration). -/

theorem msFi_absPre (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ msS0) ⟨6⟩ = some [(1, 1)] := by
  kernel_rfl

theorem msFi_result (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ msFiS1).heap (.base ⟨21⟩)).map (fun c => c.value)
      = some (.int 2 .uint64) := by
  kernel_rfl

theorem msFi_err (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ msFiS1).heap (.base ⟨22⟩)).map (fun c => c.value)
      = some .nil := by
  kernel_rfl

theorem msFi_preserve (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ msFiS1) ⟨6⟩ = some [(1, 1)] := by
  kernel_rfl

/-- **THE FirstIndex EQUATION**: the run completes in 178 steps with
no choice consumed; the `fi` result cell holds the spec value applied
to the PRE state's storage abstraction; the error result is nil; and
the storage abstraction is PRESERVED (the `callStats` increment is a
real heap effect that the abstraction deliberately does not read). -/
theorem msFirstIndex_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
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
  refine ⟨γS ρ σ msFiS1, msFi_span ρ σ ch hag, msFi_absPre ρ σ, ?_, msFi_err ρ σ, ?_⟩
  · rw [msFi_absPre ρ σ, msFi_result ρ σ]
    with_unfolding_all rfl
  · rw [msFi_absPre ρ σ, msFi_preserve ρ σ]

/-! ## Term (at index 1 — the in-range instance; error branches are
the recorded residual above) -/

theorem msTmW_n : (symEvalWindowTB bfTB 246 msS0 msTmC0).1 = 246 := by
  kernel_rfl

theorem msTmC1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 246 msS0 msTmC0).2.2 = .next .stop := by
  kernel_rfl

theorem msTm_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 246 (γS ρ σ msS0) (γC ρ msTmC0) ch
      = .ok (.next .stop, γS ρ σ msTmS1, ch) := by
  have h := symEvalWindowTB_refines' msTmW_n ρ σ ch hag
  rw [msTmC1_stop ρ] at h
  exact h

theorem msTm_result (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ msTmS1).heap (.base ⟨21⟩)).map (fun c => c.value)
      = some (.int 1 .uint64) := by
  kernel_rfl

theorem msTm_err (ρ : Valuation) (σ : ExecState) :
    (Heap.lookup (γS ρ σ msTmS1).heap (.base ⟨22⟩)).map (fun c => c.value)
      = some .nil := by
  kernel_rfl

theorem msTm_preserve (ρ : Valuation) (σ : ExecState) :
    absStorageEnts (γS ρ σ msTmS1) ⟨6⟩ = some [(1, 1)] := by
  kernel_rfl

/-- **THE Term EQUATION** (index 1): same form — the `fi` result cell
holds `specTermAt` of the pre abstraction at index 1; error nil;
abstraction preserved. -/
theorem msTerm_handler_eq (ρ : Valuation) (σ : ExecState)
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
  refine ⟨γS ρ σ msTmS1, msTm_span ρ σ ch hag, msFi_absPre ρ σ, ?_, msTm_err ρ σ, ?_⟩
  · rw [msFi_absPre ρ σ, msTm_result ρ σ]
    with_unfolding_all rfl
  · rw [msFi_absPre ρ σ, msTm_preserve ρ σ]

/-! ## Discharge witnesses (constitution §3.3): concrete valuation,
`wBase` tables, empty stream. -/

theorem msFirstIndex_handler_eq_witness :
    ∃ σfin,
      stepFnIter 178 (γS bcρw wBase msS0) (γC bcρw msFiC0) []
        = .ok (.next .stop, σfin, [])
      ∧ absStorageEnts (γS bcρw wBase msS0) ⟨6⟩ = some [(1, 1)]
      ∧ (Heap.lookup σfin.heap (.base ⟨21⟩)).map (fun c => c.value)
          = ((absStorageEnts (γS bcρw wBase msS0) ⟨6⟩).bind specFirstIndex).map
              (fun v => GoValue.int v .uint64)
      ∧ (Heap.lookup σfin.heap (.base ⟨22⟩)).map (fun c => c.value)
          = some .nil
      ∧ absStorageEnts σfin ⟨6⟩ = absStorageEnts (γS bcρw wBase msS0) ⟨6⟩ :=
  msFirstIndex_handler_eq bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

theorem msTerm_handler_eq_witness :
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
  msTerm_handler_eq bcρw wBase ⟨rfl, rfl, rfl, rfl⟩ []

end GoLean.RaftSeam
