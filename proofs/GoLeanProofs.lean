import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.Rel

/-!
# GoCore ⊳ Iris — the proof layer

Instantiates iris-lean's bare `Language` (no evaluation contexts) on GoCore's
**real** reshaped relation: `Config` (state-free control, the Iris `Expr` after
Reshape A) with `ExecState` as the Iris `State`, and `Step` as the primitive
reduction. This is the port of the validated toy spike
(`docs/2026-07-18_iris-spike-result.md`) onto the real semantics.

`IrisGS_gen` + gen_heap over the real heap and the `wp_store`/`wp_load` laws
follow in the next step (they need gen_heap wired over `ExecState.heap`).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

/-- Iris `Val` is unit; the terminal control configuration is `.next .stop`
(a GoCore statement run produces no value — results are written to caller heap
locations, so the content lives in the `State`). -/
instance : ToVal Config Unit where
  toVal c := match c with | .next .stop => some () | _ => none
  ofVal _ := .next .stop
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

/-- The Iris primitive step: GoCore's small-step `Step`, with no observations
and no forked threads (the sequential relation forks nothing). -/
inductive GoPrimStep :
    Config × ExecState → List Unit → Config × ExecState × List Config → Prop where
  | step {c s c' s'} : Step c s c' s' → GoPrimStep (c, s) [] (c', s', [])

instance : PrimStep Config ExecState (List Unit) where
  primStep := GoPrimStep

/-- The bare `Language` instance: a CK machine seats on iris-lean directly, with
no `EctxLanguage`. `val_stuck` holds because no `Step` rule has `.next .stop` as
its source — the terminal control is irreducible. -/
instance : Language Config ExecState Unit Unit where
  val_stuck h := by
    cases h with
    | step st => cases st <;> rfl

instance : Inhabited ExecState := ⟨{}⟩

/-! ## Step 3b — gen_heap over GoCore's real heap

Wire iris-lean's gen_heap to GoCore's actual heap, keyed by the base address
`Nat` (heap cells live only at `.base ⟨n⟩` locs; `Nat` has the lawful compare
`ExtTreeMap`/gen_heap require, sidestepping a compare for the recursive `Loc`).
This gives the `↦` connective over GoCore's heap and the `StateInterp`/`IrisGS`
that WP laws — pure (`wp_seqn`) and heap-touching (`wp_assign`) — run against. -/

/-- gen_heap's finite-map functor, keyed by the base-address `Nat`. -/
abbrev GoHeapF : Type → Type := fun V => Std.ExtTreeMap Nat V compare

/-- Project GoCore's association-list heap into gen_heap's finite map, keyed by
the base address. A **right** fold: the list head is inserted last, so the head
wins on a key clash — exactly matching `Heap.lookup`'s first-match walk. This
makes the projection faithful *unconditionally* (no heap-key-uniqueness
invariant), since both `heapToMap` and `Heap.lookup` return the frontmost entry
for a key and skip non-`base` locs identically. -/
def heapToMap (h : Heap) : GoHeapF HeapCell :=
  h.foldr (fun (p : Loc × HeapCell) m =>
    match p.1 with
    | .base a => insert m a.id p.2
    | _ => m) ∅

@[simp] theorem heapToMap_nil : heapToMap [] = (∅ : GoHeapF HeapCell) := rfl
@[simp] theorem heapToMap_cons_base (a : Addr) (cell : HeapCell) (rest : Heap) :
    heapToMap ((Loc.base a, cell) :: rest) = insert (heapToMap rest) a.id cell := rfl
@[simp] theorem heapToMap_cons_field (b : Loc) (t : TypeId) (f : String)
    (cell : HeapCell) (rest : Heap) :
    heapToMap ((Loc.field b t f, cell) :: rest) = heapToMap rest := rfl
@[simp] theorem heapToMap_cons_index (b : Loc) (i : Int)
    (cell : HeapCell) (rest : Heap) :
    heapToMap ((Loc.index b i, cell) :: rest) = heapToMap rest := rfl

-- The derived `BEq Loc`/`BEq Addr` reduce structurally on constructors.
@[simp] theorem base_base_beq (a b : Addr) :
    (Loc.base a == Loc.base b) = (a.id == b.id) := rfl
@[simp] theorem field_base_beq (b : Loc) (t : TypeId) (f : String) (c : Addr) :
    (Loc.field b t f == Loc.base c) = false := rfl
@[simp] theorem index_base_beq (b : Loc) (i : Int) (c : Addr) :
    (Loc.index b i == Loc.base c) = false := rfl

/-- **Bridge A** (read): `heapToMap`'s `get?` at a base address `k` agrees with
GoCore's `Heap.lookup` at `.base ⟨k⟩`. Unconditional — the foldr's head-wins
insertion mirrors `Heap.lookup`'s first-match, and both skip non-`base` entries.
This turns gen_heap's `genHeap_valid` fact into the operational lookup
`storeLoc`/`loadLoc` consume. -/
theorem get?_heapToMap (h : Heap) (k : Nat) :
    get? (heapToMap h) k = Heap.lookup h (.base ⟨k⟩) := by
  induction h with
  | nil => simp [Heap.lookup, get?_empty]
  | cons p rest ih =>
    obtain ⟨loc, cell⟩ := p
    cases loc with
    | base a =>
      simp only [heapToMap_cons_base, Heap.lookup, base_base_beq]
      by_cases hk : a.id = k
      · rw [get?_insert_eq hk]; simp [hk]
      · rw [get?_insert_ne hk, ih]; simp [hk]
    | field b t f => simp only [heapToMap_cons_field, Heap.lookup]; simp [ih]
    | index b i => simp only [heapToMap_cons_index, Heap.lookup]; simp [ih]

/-- **Bridge B** (write): projecting after a base store equals inserting into the
projection. Unconditional, via Bridge A on both sides reducing to a pure
`Heap.set`/`Heap.lookup` fact. This is what lets `genHeap_update` service a
GoCore `storeLoc`. -/
theorem heapToMap_set_base (h : Heap) (a : Addr) (cell : HeapCell) :
    heapToMap (Heap.set h (.base a) cell) ≡ₘ insert (heapToMap h) a.id cell := by
  intro k
  rw [get?_heapToMap, LawfulPartialMap.get?_insert, get?_heapToMap]
  induction h with
  | nil =>
    simp only [Heap.set, Heap.lookup, base_base_beq]
    by_cases hk : a.id = k <;> simp [hk]
  | cons p rest ih =>
    obtain ⟨loc, old⟩ := p
    cases loc with
    | base b =>
      by_cases hab : b.id = a.id
      · have hba : (Loc.base b == Loc.base a) = true := by simp [hab]
        by_cases hk : a.id = k <;>
          simp [Heap.set, Heap.lookup, hba, hab, hk]
      · have hba : (Loc.base b == Loc.base a) = false := by simp [hab]
        by_cases hbk : b.id = k
        · have : ¬ a.id = k := fun h => hab (by omega)
          simp [Heap.set, Heap.lookup, hba, hbk, this]
        · simp [Heap.set, Heap.lookup, hba, hbk, ih]
    | field b t f =>
      simp [Heap.set, Heap.lookup, ih]
    | index b i =>
      simp [Heap.set, Heap.lookup, ih]

/-- The GoCore ghost state: invariant+credit cameras plus gen_heap over the
base-address heap. WP laws *assume* it, exactly as HeapLang's laws assume
`[HeapLangGS]`; constructing it is adequacy's job. -/
class GoCoreGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends
    InvGS_gen hlc GF where
  heap : genHeapGS Nat HeapCell GF GoHeapF
attribute [reducible, instance] GoCoreGS.heap

section HeapWP
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- State interpretation: gen_heap over the projected heap. -/
instance : StateInterp ExecState Unit GF where
  stateInterp σ _ _ _ := genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ.heap)

instance : IrisGS_gen hlc Config GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- `seqn` is a pure, deterministic control step: `.exec (.seqn ss) k` reduces
only to `.next (.seq ss.toList k)` with the state unchanged. A genuine
weakest-precondition law over GoCore's actual `Step` relation (holds under the
real gen_heap state interpretation, since the step is pure). -/
theorem wp_seqn {ss k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next (.seq ss.toList k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.seqn ss) k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (.seq ss.toList k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next (.seq ss.toList k), σ, [], GoPrimStep.step Step.seqn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- **The heap store law** over GoCore's real `Step.assign`.

The genuine heap Hoare law: to run `x = e` (an `assign`) then continue as `k`,
it suffices to own the target cell `a.id ↦ oldcell` and be able to continue once
it holds the written value `a.id ↦ newcell`. Proved via `wp_lift_step` (the
successor `.next k` is a *non-value* control config, unlike HeapLang's store
which reduces to `()`), consuming and re-producing the gen_heap points-to through
`genHeap_valid`/`genHeap_update` and the `heapToMap` bridge lemmas.

`hred` is the operational side condition: at a state whose target base cell holds
`oldcell`, the assign steps deterministically to `.next k` writing `newcell` into
that one cell. It is discharged per-call from the concrete `lhs`/`rhs` (e.g. a
variable LHS + pure RHS, where `AssigneeR`/`ExprR` are deterministic and
non-panicking and `storeLoc` hits the base cell). Modelling `ExecState.locals` in
the state interpretation would let this be derived rather than assumed; that is a
future reshape, tracked — for now the heap-camera core is what is proven. -/
theorem wp_assign {a : Addr} {oldcell newcell : HeapCell} {lhs rhs k}
    (hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign lhs rhs) k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign lhs rhs) k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell })) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign lhs rhs) k) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
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
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap a newcell kk).symm)) $$ Hσ
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ Hpt
      · itrivial

end HeapWP

end GoLean.Iris
