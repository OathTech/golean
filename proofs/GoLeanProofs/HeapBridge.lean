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
import GoLeanProofs.Lang

/-!
# The heap model bridge
`heapToMap` and its faithfulness bridges, `HeapWf`, allocation equations, and
the pure store facts behind the zero-hypothesis witnesses.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

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

end GoLean.Iris
