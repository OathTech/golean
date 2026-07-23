import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Iris.Instances.Lib.Invariants
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.Rel
import GoLeanProofs.Ghost

/-!
# GoCore-specific lifting cores
The reusable one-step-plus-ghost-update engines behind every store-family law
(internal machinery: consumed by `Laws/*`, not user-facing).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **Shared core: a deterministic single-step store over the owned cell.** Given
that the statement `Step`s (deterministically) from any state holding
`a.id ↦ oldcell` to `.next k` with that cell updated to `newcell`, own-and-update
the gen_heap cell across the step. This is the reusable gen_heap machinery behind
every assign-family WP law (var-assign, deref-store, …); each front-end law
proves its `hred` from its own resolution facts and calls this. The `hred`
premise — unsatisfiable in the pre-CEK layer for *any* real assign — is now
routinely dischargeable because the assignee resolves against the control `env`
(fixed in the goal), not the quantified state. -/
theorem wp_store_step {a : Addr} {oldcell newcell : HeapCell}
    {c₀ : Config} {k}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step c₀ σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step c₀ σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell })) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some oldcell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some oldcell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], Config.next k, _, [], GoPrimStep.step (hred σ₁ hlook).1⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := (hred σ₁ hlook).2 _ _ st
    imod (genHeap_update (v₂ := newcell)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap a newcell kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.set_existing hlook⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ Hpt
      · itrivial

/-- **Two-cell store core** (arc `slice-l5-pure` item 3): like `wp_store_step`,
but the reduction facts may additionally depend on a second owned cell
`pa.id ↦ pcell` that the step only *reads* (e.g. `p`'s own cell when storing
through the pointer `*p` — the address to store at is `pcell`'s value). The
read cell rides through unchanged; the target cell updates. Owning both `↦` at
full fraction implies `pa ≠ a` semantically, so no aliasing side-condition is
needed. This is the first multi-`↦` (genuinely separation-logic) core. -/
theorem wp_store_step₂ {pa a : Addr} {pcell oldcell newcell : HeapCell}
    {c₀ : Config} {k}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base pa) = some pcell →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step c₀ σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step c₀ σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell })) :
    pa.id ↦ pcell ∗ a.id ↦ oldcell
      ∗ (pa.id ↦ pcell ∗ a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro ⟨Hppt, Hpt, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some oldcell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  ihave %Hmapp : ⌜get? (heapToMap σ₁.heap) pa.id = some pcell⌝ $$ [Hσ Hppt]
  · icases genHeap_valid $$ [$Hσ $Hppt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some oldcell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hlookp : Heap.lookup σ₁.heap (.base pa) = some pcell := by
    rw [get?_heapToMap] at Hmapp; simpa using Hmapp
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], Config.next k, _, [], GoPrimStep.step (hred σ₁ hlookp hlook).1⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := (hred σ₁ hlookp hlook).2 _ _ st
    imod (genHeap_update (v₂ := newcell)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap a newcell kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.set_existing hlook⟩
    · isplitl [Hppt Hpt Hcont]
      · iapply Hcont $$ [$Hppt $Hpt]
      · itrivial

/-- **Invariant-opening two-cell store core** (arc `invariant-readout`,
design note §2/§6): like `wp_store_step₂`, but the *written* cell is not
owned — it lives in an **Iris invariant** with content `Icnt`, opened
around the single step (`hopen` exposes some `S`-cell at `a`) and closed
with the new cell (`hclose` re-establishes `Icnt` from it — the
preservation obligation). This is the per-atomic-step preservation
discipline that makes the invariance readout true: the cell may be WRITTEN
(an invariant is not a frame), but only `S`-to-`S`.

Mechanically this is why no `wp_atomic` is needed: our `Config`s are
whole-machine states that never step to values mid-program, so the
HeapLang open-around-atomic-subexpression route is unavailable — instead
the invariant is opened inside the lifting's own `={E,∅}` slots, its `▷`
absorbed by the step goal's later (plus a timeless strip for the
reducibility side). The read cell `pa` stays owned, as in
`wp_store_step₂`. -/
theorem wp_store_step₂_inv {pa a : Addr} {pcell : HeapCell}
    {S : HeapCell → Prop} {newcell : HeapCell} {Icnt : IProp GF}
    {c₀ : Config} {k} {N : Namespace}
    (hN : ↑N ⊆ E)
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hopen : Icnt ⊢ iprop(∃ cell, ⌜S cell⌝ ∗ a.id ↦ cell))
    (hclose : (iprop(a.id ↦ newcell) : IProp GF) ⊢ Icnt)
    (hred : ∀ (σ₁ : ExecState) (oldcell : HeapCell), S oldcell →
      Heap.lookup σ₁.heap (.base pa) = some pcell →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step c₀ σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step c₀ σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell })) :
    Iris.inv N Icnt
      ∗ pa.id ↦ pcell
      ∗ (pa.id ↦ pcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro ⟨HinvT, Hppt, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  imod (inv_acc hN) $$ HinvT with ⟨HI, HcloseI⟩
  ihave HI' : iprop(▷ ∃ cell, ⌜S cell⌝ ∗ a.id ↦ cell) $$ [HI]
  · iapply BI.later_mono hopen $$ HI
  imod HI' with ⟨%oldcell, %HSold, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some oldcell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  ihave %Hmapp : ⌜get? (heapToMap σ₁.heap) pa.id = some pcell⌝ $$ [Hσ Hppt]
  · icases genHeap_valid $$ [$Hσ $Hppt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some oldcell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hlookp : Heap.lookup σ₁.heap (.base pa) = some pcell := by
    rw [get?_heapToMap] at Hmapp; simpa using Hmapp
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], Config.next k, _, [],
        GoPrimStep.step (hred σ₁ oldcell HSold hlookp hlook).1⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := (hred σ₁ oldcell HSold hlookp hlook).2 _ _ st
    imod (genHeap_update (v₂ := newcell)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    ihave HcloseArg : iprop(▷ Icnt) $$ [Hpt]
    · inext
      iapply hclose $$ Hpt
    imod HcloseI $$ HcloseArg
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap a newcell kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.set_existing hlook⟩
    · isplitl [Hppt Hcont]
      · iapply Hcont $$ Hppt
      · itrivial

end

end GoLean.Iris
