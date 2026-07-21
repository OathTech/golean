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

/-- Pure interpreter fact: at a base loc whose cell is `cell`, `loadLoc` returns
its value. The operational half of the read law. -/
theorem loadLoc_base_of_lookup {σ : ExecState} {a : Addr} {cell : HeapCell}
    (h : Heap.lookup σ.heap (.base a) = some cell) :
    loadLoc σ (.base a) = .ok cell.value := by
  unfold loadLoc; rw [h]; rfl

/-- Heap well-formedness: every base address at or above `nextAddr` is
unmapped, so `ExecState.alloc`'s fresh location is genuinely fresh (the
gen_heap allocation side-condition; `docs/2026-07-20_call-law-design.md`).
Carried in the state interpretation and preserved by every step. -/
def HeapWf (σ : ExecState) : Prop :=
  ∀ n : Nat, σ.nextAddr ≤ n → Heap.lookup σ.heap (.base ⟨n⟩) = none

/-- Setting one base cell leaves lookups at every other base address unchanged
(via the `heapToMap` bridges — no `BEq Loc` lawfulness needed). -/
theorem heap_lookup_set_base_ne {h : Heap} {n : Nat} {b : Addr} {c : HeapCell}
    (hne : b.id ≠ n) :
    Heap.lookup (Heap.set h (.base b) c) (.base ⟨n⟩) = Heap.lookup h (.base ⟨n⟩) := by
  rw [← get?_heapToMap, ← get?_heapToMap, (heapToMap_set_base h b c) n,
    get?_insert_ne hne]

/-- A mapped base address is below `nextAddr` in a well-formed heap. -/
theorem HeapWf.lt_of_lookup {σ : ExecState} {a : Addr} {c : HeapCell}
    (hwf : HeapWf σ) (h : Heap.lookup σ.heap (.base a) = some c) :
    a.id < σ.nextAddr := by
  rcases Nat.lt_or_ge a.id σ.nextAddr with hlt | hge
  · exact hlt
  · have hnone : Heap.lookup σ.heap (.base ⟨a.id⟩) = none := hwf a.id hge
    rw [h] at hnone
    cases hnone

/-- Storing at a mapped base cell preserves heap well-formedness (the key set
and `nextAddr` are unchanged). -/
theorem HeapWf.set_existing {σ : ExecState} {a : Addr} {c₀ c : HeapCell}
    (hwf : HeapWf σ) (hex : Heap.lookup σ.heap (.base a) = some c₀) :
    HeapWf { σ with heap := Heap.set σ.heap (.base a) c } := by
  intro n hn
  have hn' : σ.nextAddr ≤ n := hn
  have hne : a.id ≠ n := by
    have := hwf.lt_of_lookup hex
    omega
  show Heap.lookup (Heap.set σ.heap (.base a) c) (.base ⟨n⟩) = none
  rw [heap_lookup_set_base_ne hne]
  exact hwf n hn'

/-- In a well-formed state the next address is absent from the projected map —
the gen_heap allocation side-condition. -/
theorem HeapWf.fresh_get? {σ : ExecState} (hwf : HeapWf σ) :
    get? (heapToMap σ.heap) σ.nextAddr = none := by
  rw [get?_heapToMap]
  exact hwf σ.nextAddr (Nat.le_refl _)

/-- `ExecState.alloc` computes to a fresh base location and the heap/counter
update — pinned as an equation so both step-construction and inversion can
rewrite with it. -/
theorem ExecState.alloc_eq (σ : ExecState) (v : GoValue) (ty : Option Ty) :
    σ.alloc v ty = (.base ⟨σ.nextAddr⟩,
      { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨ty, v⟩,
               nextAddr := σ.nextAddr + 1 }) := rfl

/-- Allocation preserves well-formedness: the new cell sits at the old
`nextAddr`, below the bumped counter. -/
theorem HeapWf.alloc {σ : ExecState} (hwf : HeapWf σ) {c : HeapCell} :
    HeapWf { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) c,
                    nextAddr := σ.nextAddr + 1 } := by
  intro n hn
  have hn' : σ.nextAddr + 1 ≤ n := hn
  show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) c) (.base ⟨n⟩) = none
  rw [heap_lookup_set_base_ne (show (⟨σ.nextAddr⟩ : Addr).id ≠ n by
    show σ.nextAddr ≠ n; omega)]
  exact hwf n (by omega)

/-- `IntKind.normalize` is idempotent. The fact behind discharging the store
witnesses' `hstore` to zero hypotheses: a store of an already-normalized int at
a `.int kind`-typed cell re-normalizes to the same value. -/
theorem intKind_normalize_idem (kind : IntKind) (v : Int) :
    kind.normalize (kind.normalize v) = kind.normalize v := by
  cases kind <;> simp [IntKind.normalize, IntKind.bits?, IntKind.signed] <;>
    (repeat' split) <;> omega

/-- Pure interpreter fact closing the witnesses' `hstore` premise: storing a
normalized int into an int-typed cell succeeds and yields exactly the updated
cell (the store's `normalizeValueForTy` re-normalization collapses by
`intKind_normalize_idem`). -/
theorem storeLoc_int_cell {σ : ExecState} {a : Addr} {kind : IntKind}
    {w : GoValue}
    (h : Heap.lookup σ.heap (.base a) = some ⟨some (.int kind), w⟩)
    (n : Int) :
    storeLoc σ (.base a) (.int (kind.normalize n) kind)
      = .ok { σ with heap := Heap.set σ.heap (.base a) ⟨some (.int kind), .int (kind.normalize n) kind⟩ } := by
  unfold storeLoc
  rw [h]
  simp only [normalizeValueForTy, normalizeValueForTyFuel, intKind_normalize_idem]
  rfl

/-- The GoCore ghost state: invariant+credit cameras plus gen_heap over the
base-address heap, and the **fixed program** `prog` the state interpretation
pins `σ.functions` to (functions are Step-invariant; pinning them is what
lets `wp_call` take a pure `findFunctionIn? prog … = some func` premise
instead of an unsatisfiable `∀σ` one — `docs/2026-07-20_call-law-design.md`).
WP laws *assume* it, exactly as HeapLang's laws assume `[HeapLangGS]`;
constructing it is adequacy's job. -/
class GoCoreGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends
    InvGS_gen hlc GF where
  heap : genHeapGS Nat HeapCell GF GoHeapF
  prog : Array Func
attribute [reducible, instance] GoCoreGS.heap

section HeapWP
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- State interpretation: gen_heap over the projected heap, plus the two pure
step-invariants — `σ.functions` pinned to the fixed program and heap
well-formedness (`docs/2026-07-20_call-law-design.md`). -/
instance : StateInterp ExecState Unit GF where
  stateInterp σ _ _ _ :=
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ.heap)
      ∗ ⌜σ.functions = GoCoreGS.prog GF ∧ HeapWf σ⌝)

instance : IrisGS_gen hlc Config GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- `seqn` is a pure, deterministic control step: `.exec (.seqn ss) env k`
reduces only to `.next (.seq ss.toList env k)` with the state unchanged. A
genuine weakest-precondition law over GoCore's actual `Step` relation (holds
under the real gen_heap state interpretation, since the step is pure). The
control environment `env` rides through unchanged — sequencing reads no
variables. -/
theorem wp_seqn {ss env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next (.seq ss.toList env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.seqn ss) env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (.seq ss.toList env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next (.seq ss.toList env k), σ, [], GoPrimStep.step Step.seqn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- **The heap read law**. Owning the target cell pins what the interpreter/
relation reads from it: `a.id ↦ cell` forces `loadLoc σ (.base a) = .ok
cell.value`. Unlike the store, this is *not* a standalone WP law — GoCore's CK
machine has no bare deref `Step` (reads are `ExprR` premises inside statement
steps like `assign`/`if`), so the read side is exposed as this ownership⟹value
lemma, which discharges a deref-RHS inside a `wp_assign`'s `hred`. -/
theorem pointsTo_loadLoc {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
    {σ : ExecState} {a : Addr} {cell : HeapCell} :
    genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ.heap) ∗ a.id ↦ cell
      ⊢ |==> ⌜loadLoc σ (.base a) = .ok cell.value⌝ := by
  iintro ⟨Hσ, Hpt⟩
  imod genHeap_valid $$ [$Hσ $Hpt] with %Hmap
  imodintro; ipureintro
  apply loadLoc_base_of_lookup
  rw [get?_heapToMap] at Hmap; simpa using Hmap

/-- **Shared core: a deterministic single-step store over the owned cell.** Given
that the statement `Step`s (deterministically) from any state holding
`a.id ↦ oldcell` to `.next k` with that cell updated to `newcell`, own-and-update
the gen_heap cell across the step. This is the reusable gen_heap machinery behind
every assign-family WP law (var-assign, deref-store, …); each front-end law
proves its `hred` from its own resolution facts and calls this. The `hred`
premise — unsatisfiable in the pre-CEK layer for *any* real assign — is now
routinely dischargeable because the assignee resolves against the control `env`
(fixed in the goal), not the quantified state. -/
private theorem wp_store_step {a : Addr} {oldcell newcell : HeapCell}
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
private theorem wp_store_step₂ {pa a : Addr} {pcell oldcell newcell : HeapCell}
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

/-- **The heap store law over `Step.assign` — now a usable Hoare law** (CEK
reshape, `docs/2026-07-19_cek-reshape-plan.md`; closes the pre-merge audit
finding D2-4/D2-5).

The earlier version's `hred` was unsatisfiable: it quantified `∀ σ₁`
constrained only on `σ₁.heap`, yet a variable LHS `x = e` needs
`AssigneeR σ₁ (.var id) …` resolved from `σ₁.locals` — an `ExecState` field
`hred` never pinned, so an empty-locals `σ₁` met the antecedent while admitting
no step. Relocating locals into the control `env` (CEK) fixes exactly this: the
target `x` now resolves against `env`, which is **fixed in the WP goal** (it
rides in the `Config`, not the quantified state `σ₁`). So resolution becomes the
pure, dischargeable premise `hres : LocalEnv.lookup env id = some (.base a)` — no
state camera, no `∀σ₁`. The heap core is the spike's `wp_store`.

The remaining premises are the operational facts about the right-hand side and
the store, all legitimately dischargeable for a concrete assign (none has the
old locals problem):
- `hrhs` — `rhs` evaluates to `v` without changing the state (its existence);
- `hrhs_det` — `rhs` evaluates *only* to `v` (determinism), which rules out the
  panic step-rules during inversion;
- `hstore` — storing `v` at the owned cell yields the heap update to `newcell`.

Owning `a.id ↦ oldcell`, the assign steps deterministically to `.next k` with the
cell updated to `newcell`; the continuation runs owning `a.id ↦ newcell`. See
`wp_assign_lit` for the payoff: every premise discharged for a concrete
`x = intLit n`. -/
theorem wp_assign {a : Addr} {oldcell newcell : HeapCell} {v : GoValue}
    {id rhs env k}
    (hres : LocalEnv.lookup env id = some (.base a))
    (hrhs : ∀ σ₁ : ExecState, ExprR env σ₁ rhs (.value v σ₁))
    (hrhs_det : ∀ σ₁ (out : ExprOut), ExprR env σ₁ rhs out → out = .value v σ₁)
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) v
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var id) rhs) env k) @ s ; E {{ Φ }} := by
  -- The reduction facts the old proof took as `hred`, now *derived* from the
  -- pure resolution premise plus the rhs/store operational facts.
  have hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign (.var id) rhs) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.var id) rhs) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) := by
    intro σ₁ hlook
    refine ⟨Step.assign (AssigneeR.var hres) (hrhs σ₁) (hstore σ₁ hlook), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | var hl =>
        -- target location is `.base a` (hl + hres); rhs value/state are `v`/σ₁
        rw [hres] at hl; injection hl with hloc
        have hd := hrhs_det σ₁ _ hr; injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlook] at hs; injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass => cases hass
    | assignValuePanic _ hr =>
      exact ExprOut.noConfusion (hrhs_det _ _ hr)
    | assignStorePanic hass hr hs =>
      cases hass with
      | var hl =>
        rw [hres] at hl; injection hl with hloc
        have hd := hrhs_det σ₁ _ hr; injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlook] at hs
        simp at hs
  exact wp_store_step rfl hred

/-- **A store-through-address law `*aexpr = e`.** The assignee is `.addr aexpr`
(store at the address that `aexpr` evaluates to), resolved through
`AssigneeR.addr`; shares the gen_heap core (`wp_store_step`) with `wp_assign` —
only the assignee resolution differs.

**Scope — read this before using it** (corrected per the 2026-07-19 directional
audit; the prior docstring overclaimed):

The `hres`/`hres_det` premises are `∀σ₁` — they require `aexpr` to evaluate to
the target address `.base a` *in every state*. That holds only for a
**heap-independent** address expression, i.e. one resolved purely from the
control `env`: `aexpr = .ref x` (`&x`) via `ExprR.ref`, or a resolved location.
`wp_deref_store_ref` is the discharge witness proving the law is genuinely
non-vacuous for that case.

It does **not** yet cover the frontend's real `*p` where `p` is a pointer
*variable*: there the address is the *value* of `p`'s cell, so `hres`'s `∀σ₁` is
unsatisfiable (an `σ₁` where `p`'s cell holds a different address meets nothing).
That read-through case needs the `hres`/`hrhs` premises **conditioned on the
owned cell(s)** plus multi-`↦` ownership (own `p`'s cell *and* the target) — the
tracked next increment (`docs/2026-07-19_vertical-slice-plan.md`, L5), not this
law. So `inc`'s body `*p = *p + 1` is not yet provable by this law alone.

Premises:
- `hres`/`hres_det` — `aexpr` evaluates only to `.addr (.base a)`, state
  unchanged (heap-independent; see scope). Determinism additionally rules out the
  `addrNil`/`addr` panic steps during inversion.
- `hrhs`/`hrhs_det` — `e` evaluates only to `v`, state unchanged.
- `hstore` — storing `v` at the owned cell yields the update to `newcell`. -/
theorem wp_deref_store {a : Addr} {oldcell newcell : HeapCell} {v : GoValue}
    {aexpr rhs env k}
    (hres : ∀ σ₁ : ExecState, ExprR env σ₁ aexpr (.value (.addr (.base a)) σ₁))
    (hres_det : ∀ σ₁ (out : ExprOut),
        ExprR env σ₁ aexpr out → out = .value (.addr (.base a)) σ₁)
    (hrhs : ∀ σ₁ : ExecState, ExprR env σ₁ rhs (.value v σ₁))
    (hrhs_det : ∀ σ₁ (out : ExprOut), ExprR env σ₁ rhs out → out = .value v σ₁)
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) v
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr aexpr) rhs) env k) @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign (.addr aexpr) rhs) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.addr aexpr) rhs) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) := by
    intro σ₁ hlook
    refine ⟨Step.assign (AssigneeR.addr (hres σ₁)) (hrhs σ₁) (hstore σ₁ hlook), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | addr haddr =>
        -- addr expr resolves to `.base a`, state unchanged (hres_det)
        have hd := hres_det σ₁ _ haddr; injection hd with hav has1
        injection hav with hloc
        have hd2 := hrhs_det σ₁ _ (has1 ▸ hr); injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hlook] at hs; injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass =>
      cases hass with
      | addrNil haddr => have hd := hres_det σ₁ _ haddr; simp at hd
      | addrPanic haddr => exact ExprOut.noConfusion (hres_det σ₁ _ haddr)
    | assignValuePanic _ hr =>
      exact ExprOut.noConfusion (hrhs_det _ _ hr)
    | assignStorePanic hass hr hs =>
      cases hass with
      | addr haddr =>
        have hd := hres_det σ₁ _ haddr; injection hd with hav has1
        injection hav with hloc
        have hd2 := hrhs_det σ₁ _ (has1 ▸ hr); injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hlook] at hs
        simp at hs
  exact wp_store_step rfl hred

/-- **Deref-load as an `ExprR` fact.** If `aexpr` resolves to `.addr (.base a)`
(state unchanged) and the cell at `a` holds `cell`, then `*aexpr` evaluates to
`cell.value`. This is the expression-level building block for a non-literal
right-hand side such as `*p` (and, composed with `ExprR.addInt`, `*p + 1`). Pure
relational fact — no separation logic here; heap *ownership* enters only where
this feeds a WP premise, via `pointsTo_loadLoc` turning `↦` into the `hcell`
hypothesis. -/
theorem exprR_deref_load {env : LocalEnv} {σ : ExecState} {aexpr : Expr} {ty : Ty}
    {a : Addr} {cell : HeapCell}
    (haddr : ExprR env σ aexpr (.value (.addr (.base a)) σ))
    (hcell : Heap.lookup σ.heap (.base a) = some cell) :
    ExprR env σ (.deref aexpr ty) (.value cell.value σ) :=
  ExprR.deref haddr (loadLoc_base_of_lookup hcell)

/-- Inversion of `ExprR` on an integer literal: it evaluates only to its
normalized value, leaving the state unchanged. The `binPanic*` rules carry a
function-valued `mk` index, so plain `cases` punts (higher-order unification) —
`generalize` the literal to a variable first, then each spurious case is refuted
by `Expr.noConfusion` (after fixing `mk` from its disjunction). -/
private theorem exprR_intLit_det {env : LocalEnv} {σ : ExecState} {n : Int}
    {kind : IntKind} {out : ExprOut}
    (h : ExprR env σ (.intLit n kind) out) :
    out = ExprOut.value (.int (kind.normalize n) kind) σ := by
  generalize he : Expr.intLit n kind = e at h
  cases h with
  | intLit => injection he with e1 e2; subst e1; subst e2; rfl
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- Inversion of `ExprR` on `.ref id` (address-of a variable): it evaluates only
to the address of `id`'s location (state unchanged). Same `generalize`-past-the
function-valued `binPanic*` indices shape as `exprR_intLit_det`. -/
private theorem exprR_ref_det {env : LocalEnv} {σ : ExecState} {id : String}
    {loc : Loc} {out : ExprOut} (hlk : LocalEnv.lookup env id = some loc)
    (h : ExprR env σ (.ref id) out) :
    out = ExprOut.value (.addr loc) σ := by
  generalize he : Expr.ref id = e at h
  cases h with
  | ref hl =>
      injection he with hid; subst hid
      rw [hlk] at hl; injection hl with hl'; subst hl'; rfl
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- **Payoff: `wp_assign` is genuinely instantiable — with ZERO hypotheses.**
This is what task #23 was blocked on — the old law's `hred` was unsatisfiable
for *every* real assign (`docs/2026-07-19_premerge-audit-results.md`,
D2-4/D2-5). Every premise is discharged: resolution by `simp` against the
concrete control environment binding `x ↦ .base a`; the rhs premises outright
for an integer literal (`ExprR.intLit` / `exprR_intLit_det`); and the store
side-condition by `storeLoc_int_cell` (the cell is int-typed, so the store's
re-normalization collapses by `intKind_normalize_idem`). The owned cell's prior
value `w` is arbitrary — this is the general "assign a literal over anything in
an int cell" spec, closed. (Arc `slice-l5-pure` item 1: `hstore` was previously
an open `∀σ` hypothesis; the Audit ledger's `◌` is now `✓`.) -/
theorem wp_assign_lit {a : Addr} {w : GoValue} {n : Int}
    {kind : IntKind} {rest : LocalEnv} {k} :
    a.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var "x") (.intLit n kind))
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_assign (id := "x") (v := .int (kind.normalize n) kind)
    (by simp [LocalEnv.lookup, Scope.lookup])
    (fun _ => ExprR.intLit)
    (fun _ _ h => exprR_intLit_det h)
    (fun _ hlook => storeLoc_int_cell hlook n)

/-- **Non-vacuity witness for `wp_deref_store` — ZERO hypotheses.** Discharges
the heap-independent address case the law genuinely covers: `*(&x) = n` —
assignee `.addr (.ref "x")`, whose address resolves purely from `env`
(`x ↦ .base a`) via `ExprR.ref`, so the `∀σ₁` `hres`/`hres_det` premises hold.
`hrhs`/`hrhs_det` discharge for the integer literal, and the store side-condition
by `storeLoc_int_cell` (arbitrary prior value `w` in an int-typed cell). This
proves `wp_deref_store` is a real (non-scaffold) law — contrast the read-through
`*p` case, whose address comes from a pointer variable's cell and therefore needs
cell-conditioned premises + multi-`↦` ownership (arc item 3, not this witness). -/
theorem wp_deref_store_ref {a : Addr} {w : GoValue} {n : Int}
    {kind : IntKind} {rest : LocalEnv} {k} :
    a.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr (.ref "x")) (.intLit n kind))
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_deref_store (a := a) (v := .int (kind.normalize n) kind)
    (fun _ => ExprR.ref (by simp [LocalEnv.lookup, Scope.lookup]))
    (fun _ _ h => exprR_ref_det (by simp [LocalEnv.lookup, Scope.lookup]) h)
    (fun _ => ExprR.intLit)
    (fun _ _ h => exprR_intLit_det h)
    (fun _ hlook => storeLoc_int_cell hlook n)

/-! ## Arc `slice-l5-pure` item 3 — the read-through pointer store `*p = …`

The case `wp_deref_store` cannot cover: the target address is the *value of
`p`'s cell*, so resolution is heap-dependent. The premises here are
**conditioned on the owned cells** (this is what the `∀σ₁`-unsatisfiability of
the state-independent premises forces), and the law consumes the two-cell core
`wp_store_step₂`: own `p`'s cell (read) and the target cell (written). -/

/-- Inversion of `ExprR` on `.var p`, conditioned on the resolution and load
facts: it evaluates only to the loaded value, state unchanged. -/
private theorem exprR_var_det {env : LocalEnv} {σ : ExecState} {p : String}
    {loc : Loc} {val : GoValue} {out : ExprOut}
    (hl : LocalEnv.lookup env p = some loc)
    (hv : loadLoc σ loc = .ok val)
    (h : ExprR env σ (.var p) out) : out = .value val σ := by
  generalize he : Expr.var p = e at h
  cases h with
  | var hl' hv' =>
      injection he with hp; subst hp
      rw [hl] at hl'; injection hl' with hloc; subst hloc
      rw [hv] at hv'; injection hv' with hval; subst hval; rfl
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- Inversion of `ExprR` on `*p` (deref of a variable), conditioned on `p`'s
resolution and both cells: it evaluates only to the target cell's value. -/
private theorem exprR_deref_var_det {env : LocalEnv} {σ : ExecState} {p : String}
    {ty : Ty} {pa a : Addr} {pcell acell : HeapCell} {out : ExprOut}
    (hl : LocalEnv.lookup env p = some (.base pa))
    (hp : Heap.lookup σ.heap (.base pa) = some pcell)
    (hpv : pcell.value = .addr (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some acell)
    (h : ExprR env σ (.deref (.var p) ty) out) : out = .value acell.value σ := by
  have hloadp : loadLoc σ (.base pa) = .ok (.addr (.base a)) := by
    rw [loadLoc_base_of_lookup hp, hpv]
  generalize he : Expr.deref (.var p) ty = e at h
  cases h with
  | deref haddr hload =>
      injection he with h1 h2; subst h1; subst h2
      have hd := exprR_var_det hl hloadp haddr
      injection hd with hav hs1
      injection hav with hloc
      subst hs1; subst hloc
      rw [loadLoc_base_of_lookup ha] at hload
      injection hload with hval; subst hval
      rfl
  | derefNil haddr =>
      injection he with h1 h2; subst h1
      have hd := exprR_var_det hl hloadp haddr
      injection hd with hav _
      exact GoValue.noConfusion hav
  | binPanicLeft mk hmk _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | binPanicRight mk hmk _ _ =>
      rcases hmk with rfl | rfl | rfl | rfl <;> exact Expr.noConfusion he
  | _ => exact Expr.noConfusion he

/-- `k == k` for the derived `BEq IntKind` (constant constructors by `decide`;
`unbounded` reduces to `String` beq-reflexivity). -/
private theorem intKind_beq_self (k : IntKind) : (k == k) = true := by
  cases k
  case unbounded name => exact beq_self_eq_true (a := name)
  all_goals decide

/-- `compatibleResult` on equal kinds is that kind. -/
private theorem intKind_compatibleResult_self (k : IntKind) :
    IntKind.compatibleResult k k = some k := by
  simp [IntKind.compatibleResult, intKind_beq_self]

/-- Inversion of `ExprR` on `*p + lit`, conditioned on the cells: it evaluates
only to the normalized sum. The composite determinism fact behind the
`*p = *p + 1` witness. -/
private theorem exprR_inc_det {env : LocalEnv} {σ : ExecState} {p : String}
    {ty : Ty} {pa a : Addr} {pcell : HeapCell} {kind : IntKind} {m lit : Int}
    {out : ExprOut}
    (hl : LocalEnv.lookup env p = some (.base pa))
    (hp : Heap.lookup σ.heap (.base pa) = some pcell)
    (hpv : pcell.value = .addr (.base a))
    (ha : Heap.lookup σ.heap (.base a) = some ⟨some (.int kind), .int m kind⟩)
    (h : ExprR env σ (.add (.deref (.var p) ty) (.intLit lit kind)) out) :
    out = .value (.int (kind.normalize (m + kind.normalize lit)) kind) σ := by
  generalize he : Expr.add (.deref (.var p) ty) (.intLit lit kind) = e at h
  cases h with
  | addInt hle hre hk =>
      injection he with h1 h2; subst h1; subst h2
      have hld := exprR_deref_var_det hl hp hpv ha hle
      injection hld with hlv hs1
      injection hlv with hm hkl
      have hrd := exprR_intLit_det (hs1 ▸ hre)
      injection hrd with hrv hs2
      injection hrv with hn hkr
      subst hkl; subst hkr
      rw [intKind_compatibleResult_self] at hk
      injection hk with hkk
      subst hkk; subst hm; subst hn; subst hs2
      rfl
  | binPanicLeft mk hmk hpanic =>
      rcases hmk with rfl | rfl | rfl | rfl <;> try exact Expr.noConfusion he
      injection he with h1 h2; subst h1
      exact ExprOut.noConfusion (exprR_deref_var_det hl hp hpv ha hpanic)
  | binPanicRight mk hmk hval hpanic =>
      rcases hmk with rfl | rfl | rfl | rfl <;> try exact Expr.noConfusion he
      injection he with h1 h2; subst h1; subst h2
      have hd := exprR_deref_var_det hl hp hpv ha hval
      injection hd with _ hs1
      exact ExprOut.noConfusion (exprR_intLit_det (hs1 ▸ hpanic))
  | _ => exact Expr.noConfusion he

/-- **The read-through pointer store law `*p = e`** — `p` is a pointer
*variable*; the target address is the value of `p`'s cell. Premises are
conditioned on the two owned cells (that conditioning is exactly what the
audit-established unsatisfiability of state-independent premises requires):
- `hres` — `p` resolves in `env` to its own cell `pa`;
- `hpval` — `p`'s cell holds the target address `.addr (.base a)`;
- `hrhs`/`hrhs_det` — under both cell facts, `rhs` evaluates only to `v`;
- `hstore` — storing `v` at the owned target yields the update.
Consumes the two-cell core; the continuation regains both cells, target
updated. Witness: `wp_inc_via_ptr` (`*p = *p + 1`, zero hypotheses). -/
theorem wp_store_via_ptr {pa a : Addr} {pcell oldcell newcell : HeapCell}
    {v : GoValue} {p : String} {rhs env k}
    (hres : LocalEnv.lookup env p = some (.base pa))
    (hpval : pcell.value = .addr (.base a))
    (hrhs : ∀ σ₁ : ExecState,
        Heap.lookup σ₁.heap (.base pa) = some pcell →
        Heap.lookup σ₁.heap (.base a) = some oldcell →
        ExprR env σ₁ rhs (.value v σ₁))
    (hrhs_det : ∀ σ₁ (out : ExprOut),
        Heap.lookup σ₁.heap (.base pa) = some pcell →
        Heap.lookup σ₁.heap (.base a) = some oldcell →
        ExprR env σ₁ rhs out → out = .value v σ₁)
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) v
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    pa.id ↦ pcell ∗ a.id ↦ oldcell
      ∗ (pa.id ↦ pcell ∗ a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr (.var p)) rhs) env k) @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base pa) = some pcell →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign (.addr (.var p)) rhs) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.addr (.var p)) rhs) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) := by
    intro σ₁ hlp hla
    have hloadp : loadLoc σ₁ (.base pa) = .ok (.addr (.base a)) := by
      rw [loadLoc_base_of_lookup hlp, hpval]
    refine ⟨Step.assign (AssigneeR.addr (ExprR.var hres hloadp))
      (hrhs σ₁ hlp hla) (hstore σ₁ hla), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | addr haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with hav hs1
        injection hav with hloc
        rw [hs1] at hr
        have hd2 := hrhs_det σ₁ _ hlp hla hr
        injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hla] at hs
        injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass =>
      cases hass with
      | addrNil haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with hav _
        exact GoValue.noConfusion hav
      | addrPanic haddr =>
        exact ExprOut.noConfusion (exprR_var_det hres hloadp haddr)
    | assignValuePanic hass hr =>
      cases hass with
      | addr haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with _ hs1
        exact ExprOut.noConfusion (hrhs_det σ₁ _ (hs1 ▸ hlp) (hs1 ▸ hla) (hs1 ▸ hr))
    | assignStorePanic hass hr hs =>
      cases hass with
      | addr haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with hav hs1
        injection hav with hloc
        rw [hs1] at hr
        have hd2 := hrhs_det σ₁ _ hlp hla hr
        injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hla] at hs
        simp at hs
  exact wp_store_step₂ rfl hred

/-- **Zero-hypothesis witness: `*p = *p + lit` (∀-general over `m` AND `lit`;
`inc`'s body is the `lit = 1` instance).** Own `p`'s cell
(holding a pointer to `a`) and the target int cell (holding `m`); after the
statement the target holds the normalized `m + 1` and `p`'s cell is unchanged.
Every premise of `wp_store_via_ptr` is discharged: resolution by `simp`
against the concrete env, the conditioned rhs evaluation by
`ExprR.addInt`/`ExprR.deref`/`ExprR.var`, its determinism by `exprR_inc_det`,
and the store by `storeLoc_int_cell`. The first multi-`↦` closed spec — the
`{p ↦ –, a ↦ m} *p = *p+1 {p ↦ –, a ↦ m+1}` shape the slice's `inc` needs
(∀ m: general, not specialized to an example value). -/
theorem wp_inc_via_ptr {pa a : Addr} {pdecl : Option Ty} {ty : Ty}
    {kind : IntKind} {m lit : Int} {rest : LocalEnv} {k} :
    pa.id ↦ (⟨pdecl, .addr (.base a)⟩ : HeapCell)
      ∗ a.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ (pa.id ↦ (⟨pdecl, .addr (.base a)⟩ : HeapCell)
          ∗ a.id ↦ (⟨some (.int kind), .int (kind.normalize (m + kind.normalize lit)) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
              (.assign (.addr (.var "p"))
                (.add (.deref (.var "p") ty) (.intLit lit kind)))
              ([("p", Loc.base pa)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_store_via_ptr (pa := pa) (a := a)
    (v := .int (kind.normalize (m + kind.normalize lit)) kind)
    (by simp [LocalEnv.lookup, Scope.lookup])
    rfl
    (fun σ₁ hlp hla =>
      ExprR.addInt
        (ExprR.deref (ExprR.var (loc := .base pa)
            (by simp [LocalEnv.lookup, Scope.lookup])
            (by rw [loadLoc_base_of_lookup hlp]))
          (by rw [loadLoc_base_of_lookup hla]))
        ExprR.intLit
        (intKind_compatibleResult_self kind))
    (fun σ₁ out hlp hla h =>
      exprR_inc_det (by simp [LocalEnv.lookup, Scope.lookup]) hlp rfl hla h)
    (fun σ₁ hla => storeLoc_int_cell hla (m + kind.normalize lit))

/-! ## Arc `slice-call-frame` item 4b — the call law

`Step.call` enters a fresh frame, ALLOCATING the parameter cell. The law's
continuation therefore receives a **fresh** `↦` for an address chosen by the
machine (`∀ pa` on the Iris side), and the function is resolved against the
state-interp-pinned program (`GoCoreGS.prog`) — a pure premise, not a `∀σ` one
(`docs/2026-07-20_call-law-design.md`). -/

/-- **The unary void call law.** General over the function, argument
expression, and continuation; arity-specialized to the slice's shape (one
parameter, no results — `inc`). Premises: the function is in the pinned
program; the argument evaluates (state-independently, e.g. `&x`) to `v`, which
normalizes at the parameter type to `v'`. The continuation runs the body in
the fresh one-binding frame env, owning the freshly allocated parameter cell,
under the `.frame` continuation. Arity-generality (parameter *lists*) is a
tracked widening, not a semantic limitation. -/
theorem wp_call_unary {funcId : FuncId} {func : Func} {pid : String} {pty : Ty}
    {body : Stmt} {argExpr : Expr} {v v' : GoValue} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) funcId = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hbody : func.body = body)
    (harg : ∀ σ₁ : ExecState, ExprR env σ₁ argExpr (.value v σ₁))
    (harg_det : ∀ σ₁ (out : ExprOut), ExprR env σ₁ argExpr out → out = .value v σ₁)
    (hnorm : ∀ σ₁ : ExecState, normalizeValueForTy σ₁ pty v = .ok v') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v'⟩ : HeapCell) -∗
        WP (Config.exec body [[(pid, Loc.base pa)]]
              (.frame [] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[] funcId #[argExpr]) env k) @ s ; E {{ Φ }} := by
  obtain ⟨fid, fargs, fres, fbody⟩ := func
  simp only at hargs hres hbody
  subst hargs; subst hres; subst hbody
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  have hstep : Step (.exec (.call #[] funcId #[argExpr]) env k) σ₁
      (.exec fbody [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]] (.frame [] [] k))
      { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩,
                nextAddr := σ₁.nextAddr + 1 } :=
    Step.call AssigneesR.nil (ArgsR.cons (harg σ₁) ArgsR.nil)
      (by rw [hfns]; exact hfind)
      (BindParamsR.cons (hnorm σ₁) (ExecState.alloc_eq σ₁ v' (some pty))
        BindParamsR.nil)
      DeclsR.nil
  have hdet : ∀ c' s',
      Step (.exec (.call #[] funcId #[argExpr]) env k) σ₁ c' s' →
      c' = Config.exec fbody [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]] (.frame [] [] k) ∧
      s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩,
                     nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    cases hst with
    | call hass hargsR hfindR hbind hdecls =>
      cases hass
      cases hargsR with
      | cons hE hrest =>
        have hd := harg_det σ₁ _ hE
        injection hd with hv hs0
        rw [hs0] at hrest
        cases hrest
        rw [hfns, hfind] at hfindR
        injection hfindR with hfunc
        subst hfunc
        rw [hv] at hbind
        cases hbind with
        | cons hn' ha' hrest' =>
          rw [hnorm σ₁] at hn'
          injection hn' with hv'
          rw [← hv', ExecState.alloc_eq] at ha'
          injection ha' with hloc hst'
          rw [← hloc, ← hst'] at hrest'
          cases hrest'
          cases hdecls
          exact ⟨rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], GoPrimStep.step hstep⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ st
    imod (genHeap_alloc (v := (⟨some pty, v'⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- Pure, deterministic frame pop: normal completion of a function body
resumes the caller (`Step.frameFall`; stores no results — void frames). -/
theorem wp_frame_fall {targets results k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.frame targets results k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step Step.frameFall⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic step: advance a sequence to its next statement
(`Step.seqNext`). -/
theorem wp_seq_next {t : Stmt} {rest : List Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.exec t env (.seq rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.seq (t :: rest) env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.exec t env (.seq rest env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.seqNext⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic step: `return` starts unwinding, carrying the current
env into `.returning` (so the frame can read named results). -/
theorem wp_return {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec .returnStmt env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning env k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.returnStmt⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- **The declaration law `x := default`** (`Stmt.initialization`, the CEK
inline-declaration step): allocates a fresh cell at the parameter type's
default value and extends the *rest of the enclosing sequence*'s env with the
new binding. Like the call law, the continuation receives the freshly
allocated cell at a machine-chosen address (`∀ pa`). `hdef` is the pure
default-value fact (state-independent for scalar types). Witness:
`wp_init_int`. -/
theorem wp_init {pid : String} {pty : Ty} {v : GoValue} {rest : List Stmt}
    {env k}
    (hdef : ∀ σ₁ : ExecState, defaultValue σ₁ pty = .ok v) :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare pid (.base pa)) k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k))
          @ s ; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hwf⟩ := Hinv
  have hstep : Step (.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k)) σ₁
      (.next (.seq rest (env.declare pid (.base ⟨σ₁.nextAddr⟩)) k))
      { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v⟩,
                nextAddr := σ₁.nextAddr + 1 } :=
    Step.initialization (hdef σ₁) (ExecState.alloc_eq σ₁ v (some pty))
  have hdet : ∀ c' s',
      Step (.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k)) σ₁ c' s' →
      c' = Config.next (.seq rest (env.declare pid (.base ⟨σ₁.nextAddr⟩)) k) ∧
      s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v⟩,
                     nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    cases hst with
    | initialization hd ha =>
      rw [hdef σ₁] at hd
      injection hd with hv
      rw [← hv, ExecState.alloc_eq] at ha
      injection ha with hloc hst'
      rw [← hloc, ← hst']
      exact ⟨rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], GoPrimStep.step hstep⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ st
    imod (genHeap_alloc (v := (⟨some pty, v⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- Witness for `wp_init`: `x := 0` at an int kind — the slice's `x := 0`.
Zero hypotheses (the int default is `0`, state-independently). -/
theorem wp_init_int {pid : String} {kind : IntKind} {rest : List Stmt} {env k} :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some (.int kind), .int 0 kind⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare pid (.base pa)) k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.initialization ⟨pid, .int kind⟩) env (.seq rest env k))
          @ s ; E {{ Φ }} :=
  wp_init (fun _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]
    rfl)

/-- **Var-to-var assignment `tgt = src`** (the lowering of `return x`'s
result-local write): read the source cell, write the target cell — the
two-cell core again, both resolutions fixed-env facts. Witness:
`wp_assign_var_int`. -/
theorem wp_assign_var {sa ta : Addr} {scell tcell newtcell : HeapCell}
    {tgt src : String} {env k}
    (hres_t : LocalEnv.lookup env tgt = some (.base ta))
    (hres_s : LocalEnv.lookup env src = some (.base sa))
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base ta) = some tcell →
        storeLoc σ₁ (.base ta) scell.value
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) :
    sa.id ↦ scell ∗ ta.id ↦ tcell
      ∗ (sa.id ↦ scell ∗ ta.id ↦ newtcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var tgt) (.var src)) env k) @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base sa) = some scell →
      Heap.lookup σ₁.heap (.base ta) = some tcell →
      Step (Config.exec (.assign (.var tgt) (.var src)) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.var tgt) (.var src)) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) := by
    intro σ₁ hls hlt
    have hloads : loadLoc σ₁ (.base sa) = .ok scell.value :=
      loadLoc_base_of_lookup hls
    refine ⟨Step.assign (AssigneeR.var hres_t) (ExprR.var hres_s hloads)
      (hstore σ₁ hlt), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | var hl =>
        rw [hres_t] at hl
        injection hl with hloc
        have hd := exprR_var_det hres_s hloads hr
        injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlt] at hs
        injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass => cases hass
    | assignValuePanic hass hr =>
      cases hass with
      | var _ => exact ExprOut.noConfusion (exprR_var_det hres_s hloads hr)
    | assignStorePanic hass hr hs =>
      cases hass with
      | var hl =>
        rw [hres_t] at hl
        injection hl with hloc
        have hd := exprR_var_det hres_s hloads hr
        injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlt] at hs
        simp at hs
  exact wp_store_step₂ rfl hred

/-- Witness for `wp_assign_var`: copy an int variable into an int target cell
(∀-general over the copied value). -/
theorem wp_assign_var_int {sa ta : Addr} {kind : IntKind} {n : Int}
    {w : GoValue} {tgt src : String} {env k}
    (hres_t : LocalEnv.lookup env tgt = some (.base ta))
    (hres_s : LocalEnv.lookup env src = some (.base sa)) :
    sa.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (sa.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var tgt) (.var src)) env k) @ s ; E {{ Φ }} :=
  wp_assign_var hres_t hres_s (fun σ₁ hlt => storeLoc_int_cell hlt n)

/-- **The value-returning frame exit.** `return` reaches the frame with the
callee env carried by `.returning`; the named result local (allocated at frame
entry since the results-allocation fix) is read from its owned cell and stored
to the caller's target cell. Premises conditioned on the two owned cells, via
the two-cell core (result cell read, target written). Arity-specialized to one
result/one target, like `wp_call_unary`. Witness: `wp_frame_return_int`. -/
theorem wp_frame_return {ra ta : Addr} {rcell tcell newtcell : HeapCell}
    {rname : String} {rty : Ty} {calleeEnv : LocalEnv} {k}
    (hres : LocalEnv.lookup calleeEnv rname = some (.base ra))
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base ta) = some tcell →
        storeLoc σ₁ (.base ta) rcell.value
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) :
    ra.id ↦ rcell ∗ ta.id ↦ tcell
      ∗ (ra.id ↦ rcell ∗ ta.id ↦ newtcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning calleeEnv (.frame [.base ta] [⟨rname, rty⟩] k))
          @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base ra) = some rcell →
      Heap.lookup σ₁.heap (.base ta) = some tcell →
      Step (Config.returning calleeEnv (.frame [.base ta] [⟨rname, rty⟩] k)) σ₁
        (.next k) { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell } ∧
      (∀ c' s',
        Step (Config.returning calleeEnv (.frame [.base ta] [⟨rname, rty⟩] k)) σ₁ c' s' →
        c' = Config.next k ∧
        s' = { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) := by
    intro σ₁ hlr hlt
    refine ⟨Step.frameReturn
      (ResultsR.cons hres (loadLoc_base_of_lookup hlr) ResultsR.nil)
      (StoreManyR.cons (hstore σ₁ hlt) StoreManyR.nil), ?_⟩
    intro c' s' hst
    cases hst with
    | frameReturn hresR hstoreR =>
      cases hresR with
      | cons hl hload hrest =>
        rw [hres] at hl
        injection hl with hloc
        rw [← hloc, loadLoc_base_of_lookup hlr] at hload
        injection hload with hval
        cases hrest
        rw [← hval] at hstoreR
        cases hstoreR with
        | cons hst1 hrest2 =>
          rw [hstore σ₁ hlt] at hst1
          injection hst1 with hs1
          rw [← hs1] at hrest2
          cases hrest2
          exact ⟨rfl, rfl⟩
  exact wp_store_step₂ rfl hred

/-- Witness for `wp_frame_return`: an int result local (holding a normalized
`n`, ∀-general) returned into an int target cell (any prior value `w`). Sole
premise: the result local resolves in the callee env — the fact the caller of
this law always has from `wp_call`-style entry. -/
theorem wp_frame_return_int {ra ta : Addr} {kind : IntKind} {n : Int}
    {w : GoValue} {rname : String} {rty : Ty} {calleeEnv : LocalEnv} {k}
    (hres : LocalEnv.lookup calleeEnv rname = some (.base ra)) :
    ra.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning calleeEnv (.frame [.base ta] [⟨rname, rty⟩] k))
          @ s ; E {{ Φ }} :=
  wp_frame_return hres (fun σ₁ hlt => storeLoc_int_cell hlt n)

/-- **Zero-hypothesis-modulo-program witness: the full `inc(&x)` call.**
`{x ↦ m} inc(&x) {x ↦ norm(m + lit)}` where `inc` is the one-pointer-param,
no-results function with body `*p = *p + lit` — the slice's `inc`, ∀-general
over `m` and `lit`. Composes `wp_call_unary` (frame entry, fresh param cell)
→ `wp_inc_via_ptr` (the body's multi-`↦` store) → `wp_frame_fall` (frame
exit); the parameter cell is dropped at return (affine). The only premise is
program membership (`hfind`) — genuinely external: *which* program we run. -/
theorem wp_inc_call {a : Addr} {kind : IntKind} {m lit : Int} {ty : Ty}
    {fid incId : FuncId} {rest : LocalEnv} {k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) incId = some
      ⟨fid, #[⟨"p", .pointer (.int kind)⟩], #[],
        .assign (.addr (.var "p"))
          (.add (.deref (.var "p") ty) (.intLit lit kind))⟩) :
    a.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize (m + kind.normalize lit)) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[] incId #[.ref "x"])
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} := by
  iintro ⟨Ha, Hcont⟩
  iapply (wp_call_unary (pid := "p") (pty := .pointer (.int kind))
    (v := .addr (.base a)) (v' := .addr (.base a)) hfind rfl rfl rfl
    (fun _ => ExprR.ref (by simp [LocalEnv.lookup, Scope.lookup]))
    (fun _ _ h => exprR_ref_det (by simp [LocalEnv.lookup, Scope.lookup]) h)
    (fun _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]
      rfl))
  iintro %pa Hp
  iapply (wp_inc_via_ptr (pa := pa) (a := a)
    (pdecl := some ((Ty.int kind).pointer)) (ty := ty) (kind := kind)
    (m := m) (lit := lit) (rest := []) (k := .frame [] [] k))
  isplitl [Hp]
  · iexact Hp
  isplitl [Ha]
  · iexact Ha
  iintro ⟨Hp', Ha'⟩
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred
  iapply Hcont $$ Ha'

end HeapWP

/-! ## Step 3b.3 — adequacy: end-to-end soundness of the WP layer

Mirrors HeapLang's `heap_adequacy`. From an initial `σ`, allocate the GoCore
ghost state (gen_heap heap-view + meta names over `heapToMap σ.heap`) and derive
`adequate .NotStuck`: a `WP c {{ v, ⌜φ v⌝ }}` provable under *any* allocated
ghost state entails the real machine started at `(c, σ)` never gets stuck and
every terminal value satisfies `φ`. This closes the chain **real relation →
`Language` → WP laws → adequacy** on GoCore's actual `Step`. -/

/-- The GoCore *pre* ghost state: the functors are present but names are not yet
allocated (allocation is adequacy's job). -/
class GoCoreGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends
    InvGpreS GF where
  heap_pre : genHeapPreS Nat HeapCell GF GoHeapF
attribute [reducible, instance] GoCoreGpreS.heap_pre

/-- A concrete functor bundle realizing `GoCoreGpreS`: the invariant + credit
cameras (functors 0–3) plus the gen_heap heap-view / meta-view / meta-token
functors (4–6) over `Nat`/`HeapCell`/`GoHeapF`. Mirrors HeapLang's `HeapLangS`
with GoCore's key/value types. -/
def GoCoreS : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (LeibnizO HeapCell)) GoHeapF), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (LeibnizO GName)) GoHeapF), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instGoCoreGpreS : GoCoreGpreS HasLC.hasLC GoCoreS where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6

/-- **Adequacy** for GoCore's real relation, over `NotStuck` — but note the
scope. (Pre-merge audit 2026-07-19, finding D1-1, confirmed.) `adequate
.NotStuck` requires every reachable config to be a value or reducible. In the
current Iris layer `.panicked msg` has `toVal = none` and **no** outgoing `Step`
(no rule sources it), so it counts as *stuck* — even though `Rel.lean` treats a
panic as legitimate terminal *behavior* (`Config.terminal`). So this theorem's
guarantee covers only runs that never reach `.panicked`; a Go panic (bounds,
nil-deref, divide-by-zero) makes `Hwp` unprovable rather than being a permitted
terminal. Modelling panics as values/observations in the Iris layer (so
adequacy admits panicking terminals) is deferred — until then read the guarantee
as "`φ`-correct, never-stuck execution *among non-panicking runs*". -/
theorem go_adequacy [GoCoreGpreS .hasLC GF] (c : Config) (σ : ExecState)
    (φ : Unit → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], ⊢@{IProp GF} (WP c {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck c σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck c σ φ ?_
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem (K := Nat) (V := HeapCell) (H := GoHeapF))
    (HeapView.Auth (H := GoHeapF) (.own 1)
      (Std.PartialMap.map (fun v : HeapCell => toAgree (LeibnizO.mk v))
        (heapToMap σ.heap)))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem (K := Nat) (V := GName) (H := GoHeapF))
    (HeapView.Auth (H := GoHeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (LeibnizO.mk g))
        (∅ : GoHeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions⟩
  imodintro
  iexists (fun σ' _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ HeapWf σ'⌝))
  iexists (fun _ => iprop(True))
  isplitl [Hh Hm]
  · isplitl [Hh Hm]
    · simp only [genHeapInterp]
      iexists (∅ : GoHeapF GName)
      isplitr
      · ipureintro
        intro k hk
        simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk
      unfold ghost_map_auth
      iframe Hh Hm
    · ipureintro
      exact ⟨rfl, hσwf⟩
  · exact Hwp

/-! ## Arc `slice-l5-pure` item 2 — the end-to-end adequacy witness

The one artifact that demonstrates the WP→adequacy chain *composes*: a concrete
program, its WP built from the shipped laws, fed through `go_adequacy`, yielding
a **closed** `adequate` theorem with zero hypotheses. This is the first
demonstration that Iris dissolves (`docs/2026-07-20_end-state-theorem.md`): the
conclusion `adequate .NotStuck …` is a pure operational statement over
`Step`/`Config`/`ExecState`; every Iris construct lives only in the proof. -/

section EndToEnd
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Pure, deterministic control step: an exhausted sequence pops to its
continuation (discarding that scope's env — CEK scope exit). Mirror of
`wp_seqn` for `Step.seqDone`. -/
theorem wp_seq_done {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.seq [] env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step Step.seqDone⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

end EndToEnd

/-- **The chain composes — a closed `adequate` theorem.** For any
**well-formed** initial state (`HeapWf` — heap keys below `nextAddr`, the one
side-condition the state interpretation carries; every state the semantics
can construct satisfies it) and any environment, the empty-sequence program
provably runs to termination without ever getting stuck: `WP` is assembled
from `wp_seqn` + `wp_seq_done` + `wp_value'`, discharged through
`go_adequacy` with the concrete functor bundle `GoCoreS`. The statement
mentions no Iris — it is `adequate .NotStuck` over the operational
semantics, full stop. -/
theorem adequate_seqn_nil (σ : ExecState) (env : LocalEnv) (hwf : HeapWf σ) :
    adequate .NotStuck (Config.exec (.seqn #[]) env .stop) σ (fun _ _ => True) :=
  go_adequacy (GF := GoCoreS) _ _ _ hwf (by
    intro _
    iapply wp_seqn
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred
    iapply wp_seq_done
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred2
    iapply (wp_value' (v := ()))
    ipureintro
    trivial)

end GoLean.Iris
