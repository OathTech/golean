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
private theorem wp_store_step {a : Addr} {oldcell newcell : HeapCell} {stmt env k}
    (hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec stmt env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec stmt env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell })) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec stmt env k) @ s ; E {{ Φ }} := by
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
  exact wp_store_step hred

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
  exact wp_store_step hred

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

/-- **Payoff: `wp_assign` is genuinely instantiable.** This is what task #23 was
blocked on — the old law's `hred` was unsatisfiable for *every* real assign
(`docs/2026-07-19_premerge-audit-results.md`, D2-4/D2-5). Here the resolution
premise discharges by `simp`/`rfl` against a concrete control environment that
binds `x ↦ .base a`, and the right-hand-side premises are discharged outright for
an integer literal (`hrhs` by `ExprR.intLit`; `hrhs_det` by one `cases`). Only
`hstore` — the ordinary "storing a well-typed value at the owned cell succeeds"
side-condition — is left as a hypothesis; it is about the store's value
normalization, wholly independent of the locals-resolution fix this reshape
delivered. Contrast the old law, where *no* premise set was dischargeable at
all. -/
theorem wp_assign_lit {a : Addr} {oldcell newcell : HeapCell} {n : Int}
    {kind : IntKind} {rest : LocalEnv} {k}
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) (.int (kind.normalize n) kind)
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var "x") (.intLit n kind))
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_assign (id := "x") (v := .int (kind.normalize n) kind)
    (by simp [LocalEnv.lookup, Scope.lookup])
    (fun _ => ExprR.intLit)
    (fun _ _ h => exprR_intLit_det h)
    hstore

/-- **Non-vacuity witness for `wp_deref_store`.** Discharges the heap-independent
address case the law genuinely covers: `*(&x) = n` — assignee `.addr (.ref "x")`,
whose address resolves purely from `env` (`x ↦ .base a`) via `ExprR.ref`, so the
`∀σ₁` `hres`/`hres_det` premises hold. `hrhs`/`hrhs_det` discharge for the integer
literal; only the store-typing `hstore` remains. This proves `wp_deref_store` is a
real (non-scaffold) law — contrast the read-through `*p` case, whose address comes
from a pointer variable's cell and therefore needs cell-conditioned premises +
multi-`↦` ownership (the tracked next increment, not this witness). -/
theorem wp_deref_store_ref {a : Addr} {oldcell newcell : HeapCell} {n : Int}
    {kind : IntKind} {rest : LocalEnv} {k}
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) (.int (kind.normalize n) kind)
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr (.ref "x")) (.intLit n kind))
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_deref_store (a := a) (v := .int (kind.normalize n) kind)
    (fun _ => ExprR.ref (by simp [LocalEnv.lookup, Scope.lookup]))
    (fun _ _ h => exprR_ref_det (by simp [LocalEnv.lookup, Scope.lookup]) h)
    (fun _ => ExprR.intLit)
    (fun _ _ h => exprR_intLit_det h)
    hstore

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
    (φ : Unit → Prop)
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
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩⟩
  imodintro
  iexists (fun σ _ => genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ.heap))
  iexists (fun _ => iprop(True))
  isplitl [Hh Hm]
  · simp only [genHeapInterp]
    iexists (∅ : GoHeapF GName)
    isplitr
    · ipureintro
      intro k hk
      simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk
    unfold ghost_map_auth
    iframe Hh Hm
  · exact Hwp

end GoLean.Iris
