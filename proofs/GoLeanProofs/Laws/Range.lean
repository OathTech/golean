import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.HeapBridge
import GoLeanProofs.Laws.Eval

/-!
# Map-range laws — THE FIRST NONDETERMINISTIC WP LAW (quorum pilot
phase 4, 2026-07-31)

`Step.mapIterNext` chooses ANY index of the remaining snapshot and
allocates the iteration variable — the machine's first genuinely
nondeterministic rule to get a WP law (the D2/D3 "bites at the first
nondet feature" moment, `TODO.md`). The law's premise supplies the
continuation for ALL (index, allocated address) pairs; safety needs one
witness successor (index 0). Everything the deterministic laws pinned
via `step_det` becomes a per-successor case analysis here.

v1 scope: the KEY-ONLY form (`for id := range c` — the quorum shape);
key/value iteration gets its law when a walk needs it.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- `bindIterVars` computation, key-only: one normalized alloc, the key
variable declared in a pushed scope. -/
theorem bindIterVars_key_only {env : LocalEnv} {σ : ExecState}
    {kid : String} {keyTy valTy : Ty} {key value kv : GoValue}
    (hnorm : normalizeValueForTy σ keyTy key = .ok kv) :
    bindIterVars env.pushScope σ (some kid) none keyTy valTy key value
      = .ok (env.pushScope.declare kid (.base ⟨σ.nextAddr⟩),
          { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some keyTy, kv⟩,
                   nextAddr := σ.nextAddr + 1 }) := by
  unfold bindIterVars
  simp [hnorm, Bind.bind, Except.bind, ExecState.alloc, ExecState.freshLoc]

/-- `wp_pure_det` with DIRECT determinism instead of `Config.choiceFree`
(which conservatively marks every `mapIterK` continuation as a choice
point, including the empty snapshot — where `mapIterNext` cannot fire
and the step is in fact unique). -/
private theorem wp_pure_det' {c₀ c₁ : Config}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hstep : ∀ σ : ExecState, Step c₀ σ c₁ σ)
    (hdet : ∀ (σ : ExecState) c' σ', Step c₀ σ c' σ' → c' = c₁ ∧ σ' = σ) :
    (|={E}[E]▷=> £ 1 -∗ WP c₁ @ s ; E {{ Φ }}) ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := c₁)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], c₁, σ, [], GoPrimStep.step (hstep σ)⟩
      · exact hnv)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        obtain ⟨he, hs⟩ := hdet σ _ _ st
        exact ⟨rfl, hs, he, rfl⟩))
  iexact H

/-- Deterministic despite the conservative `choiceFree`: an exhausted
snapshot pops the iteration context (`mapIterNext` needs an index below
zero to fire here). -/
theorem wp_map_iter_done {kid : Option String} {vv : Option String}
    {keyTy valTy : Ty} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.mapIterK kid vv keyTy valTy body #[] env k))
        @ s ; E {{ Φ }} :=
  wp_pure_det' rfl (fun _ => Step.mapIterDone)
    (fun σ c' σ' hst => by
      cases hst with
      | mapIterDone => exact ⟨rfl, rfl⟩
      | mapIterNext hidx _ => exact absurd hidx (by simp))

/-- Dispatch a map range: evaluate the map expression. -/
theorem wp_map_range_start {keyVar valVar : Option String}
    {mapExpr : Expr} {keyTy valTy : Ty} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE mapExpr env
        (.mapRangeK keyVar valVar keyTy valTy body env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k)
        @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.mapRange)

/-- **THE NONDETERMINISTIC STEP, key-only form**: from a NONEMPTY
snapshot, the machine picks ANY index `i` and allocates the key cell at
a machine-chosen address. The premise supplies the continuation for
EVERY such choice (`∀ i pa`); safety is witnessed at `i = 0`. `hnorm`
asks the keys to normalize to themselves at the range key type
(state-independently) — true of the already-normalized values a map
snapshot holds, dischargeable by `simp`/`decide` per concrete walk. -/
theorem wp_map_iter_next_key {kid : String} {keyTy valTy : Ty}
    {body : Stmt} {remaining : Array (GoValue × GoValue)} {env k}
    (hne : 0 < remaining.size)
    (hnorm : ∀ (σ : ExecState) (i : Nat) (h : i < remaining.size),
      normalizeValueForTy σ keyTy ((remaining[i]'h).1) = .ok ((remaining[i]'h).1)) :
    iprop(∀ (i : Nat) (h : i < remaining.size) (pa : Addr),
        pa.id ↦ (⟨some keyTy, (remaining[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none keyTy valTy body
                (remaining.eraseIdx i h) env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body remaining env k))
          @ s ; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, hwf⟩ := Hinv
  have hbind : ∀ (i : Nat) (h : i < remaining.size),
      bindIterVars env.pushScope σ₁ (some kid) none keyTy valTy
        ((remaining[i]'h).1) ((remaining[i]'h).2)
      = .ok (env.pushScope.declare kid (.base ⟨σ₁.nextAddr⟩),
          { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩)
                      ⟨some keyTy, (remaining[i]'h).1⟩,
                    nextAddr := σ₁.nextAddr + 1 }) :=
    fun i h => bindIterVars_key_only (hnorm σ₁ i h)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [],
        GoPrimStep.step (Step.mapIterNext (idx := 0) hne (hbind 0 hne))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    cases st with
    | mapIterDone => exact absurd hne (by simp)
    | @mapIterNext _ _ _ _ _ _ idx _ env' _ _ s' hidx hbindStep =>
      rw [hbind idx hidx] at hbindStep
      injection hbindStep with h1
      obtain ⟨henv, hst⟩ := Prod.mk.inj h1
      subst henv
      subst hst
      imod (genHeap_alloc
        (v := (⟨some keyTy, (remaining[idx]'hidx).1⟩ : HeapCell))
        hwf.fresh_get?) $$ Hσ with ⟨Hσ, Hpt, Htok⟩
      imod Hclose
      imodintro
      simp only [Algebra.BigOpL.bigOpL_nil]
      isplitl [Hσ]
      · isplitl [Hσ]
        · iapply (genHeapInterp_eqv
            (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
        · ipureintro
          exact ⟨hfns, hmeths, hwf.alloc⟩
      · isplitl [Hpt Hcont]
        · iapply Hcont $$ %idx %hidx %(⟨σ₁.nextAddr⟩ : Addr) Hpt
        · itrivial

end

end GoLean.Iris
