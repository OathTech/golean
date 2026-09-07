import GoLean.GoCore.RecoveryTypingCore
import GoLean.GoCore.BooleanStore

/-! Structural mixed storage for the recovery profile. The explicit schema
types addresses independently of cell contents; the heap invariant then
connects every schema entry to an actual cell. A root-reference value must
name a Boolean schema entry, so pointer-slot typing alone is insufficient.
These definitions contain no evaluator success or future-safety premise. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

abbrev World := Array ValueSort

def AddressTyped (world : World) (sort : ValueSort) (loc : Loc) : Prop :=
  ∃ a : Nat, loc = .base ⟨a⟩ ∧ world[a]? = some sort

inductive ValueTyped (world : World) : ValueSort → GoValue → Prop
  | boolean (b : Bool) : ValueTyped world .boolean (.bool b)
  | root {a : Nat} : world[a]? = some .boolean →
      ValueTyped world .root (.addr (.base ⟨a⟩))
  | nil : ValueTyped world .payload .nil
  | boxed (bytes : GoString) :
      ValueTyped world .payload (.interface .string (.string bytes))
  | string (bytes : GoString) : ValueTyped world .string (.string bytes)

structure HeapTyped (world : World) (s : ExecState) : Prop where
  size : world.size = s.heap.size
  cells : ∀ (a : Nat) (sort : ValueSort), world[a]? = some sort →
    ∃ ty v, s.heap[a]? = some (.value ty v) ∧ TypeClass ty sort ∧ ValueTyped world sort v

/-- A world extension preserves the type of every existing address. It says
nothing about the value currently stored at that address. -/
def Extends (world next : World) : Prop :=
  ∀ (a : Nat) (sort : ValueSort), world[a]? = some sort → next[a]? = some sort

theorem Extends.refl (world : World) : Extends world world := fun _ _ h => h
theorem Extends.trans {w₀ w₁ w₂} (h₁ : Extends w₀ w₁) (h₂ : Extends w₁ w₂) :
    Extends w₀ w₂ := fun a sort h => h₂ a sort (h₁ a sort h)

theorem Extends.push (world : World) (sort : ValueSort) : Extends world (world.push sort) := by
  intro a old h
  have ha := (Array.getElem?_eq_some_iff.mp h).1
  simpa [Array.getElem?_push, Nat.ne_of_lt ha] using h

theorem AddressTyped.mono {world next sort loc} (h : AddressTyped world sort loc)
    (ext : Extends world next) : AddressTyped next sort loc := by
  obtain ⟨a, hl, ha⟩ := h
  exact ⟨a, hl, ext a sort ha⟩

theorem ValueTyped.mono {world next sort v} (h : ValueTyped world sort v)
    (ext : Extends world next) : ValueTyped next sort v := by
  cases h with
  | boolean b => exact .boolean b
  | root ha => exact .root (ext _ _ ha)
  | nil => exact .nil
  | boxed bytes => exact .boxed bytes
  | string bytes => exact .string bytes

theorem HeapTyped.empty {s : ExecState} (h : s.heap = #[]) : HeapTyped #[] s := by
  refine ⟨by simp [h], ?_⟩
  intro a sort ha
  simp at ha

theorem HeapTyped.address_bound {world s sort loc} (h : HeapTyped world s)
    (hl : AddressTyped world sort loc) :
    ∃ a : Nat, loc = .base ⟨a⟩ ∧ a < s.heap.size := by
  obtain ⟨a, he, ha⟩ := hl
  exact ⟨a, he, h.size ▸ (Array.getElem?_eq_some_iff.mp ha).1⟩

theorem HeapTyped.load {world s sort loc} (h : HeapTyped world s)
    (hl : AddressTyped world sort loc) :
    ∃ v, loadLoc s loc = .ok v ∧ ValueTyped world sort v := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨ty, v, hc, _, hv⟩ := h.cells a sort ha
  exact ⟨v, by simp [loadLoc, Heap.lookup, hc]; rfl, hv⟩

theorem HeapTyped.boolean_root {world s loc} (h : HeapTyped world s)
    (hl : AddressTyped world .boolean loc) : BooleanRuntime.BoolRoot s loc := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨ty, v, hc, ht, hv⟩ := h.cells a .boolean ha
  cases ht
  cases hv with
  | boolean b => exact ⟨a, b, rfl, hc⟩

theorem HeapTyped.live_reference {world s v} (h : HeapTyped world s)
    (hv : ValueTyped world .root v) :
    ∃ loc, v = .addr loc ∧ BooleanRuntime.BoolRoot s loc := by
  cases hv with
  | @root a ha => exact ⟨.base ⟨a⟩, rfl, h.boolean_root ⟨a, rfl, ha⟩⟩

theorem HeapTyped.alloc {world s sort ty v} (h : HeapTyped world s)
    (ht : TypeClass ty sort) (hv : ValueTyped world sort v) :
    HeapTyped (world.push sort) (s.alloc v ty).2 := by
  refine ⟨by simpa [ExecState.alloc, ExecState.allocCell] using h.size, ?_⟩
  intro a kind ha
  by_cases he : a = world.size
  · subst a
    have hk : kind = sort := by simpa using ha.symm
    subst kind
    exact ⟨ty, v, by simp [ExecState.alloc, ExecState.allocCell, h.size],
      ht, hv.mono (Extends.push world sort)⟩
  · have hold : world[a]? = some kind := by
      simpa [Array.getElem?_push, he] using ha
    obtain ⟨oldTy, oldV, hc, hty, hv⟩ := h.cells a kind hold
    exact ⟨oldTy, oldV, by
      simpa [ExecState.alloc, ExecState.allocCell, Array.getElem?_push, ← h.size, he] using hc,
      hty, hv.mono (Extends.push world sort)⟩

theorem HeapTyped.allocated_address {world s sort ty v} (h : HeapTyped world s) :
    AddressTyped (world.push sort) sort (s.alloc v ty).1 := by
  exact ⟨world.size, by simp [ExecState.alloc, ExecState.allocCell, h.size], by simp⟩

/-- Normalization is the actual store path. Its identity behavior alone is
not a typing theorem; typed writes separately require `ValueTyped`. -/
theorem normalize_typed {ty sort} (ht : TypeClass ty sort) (s : ExecState) (v : GoValue) :
    normalizeValueForTy s ty v = .ok v := by
  cases ht <;> rfl

theorem typeClass_unique {ty left right} (hl : TypeClass ty left)
    (hr : TypeClass ty right) : left = right := by
  cases hl <;> cases hr <;> rfl

theorem HeapTyped.set {world s sort ty v a} (h : HeapTyped world s)
    (ha : world[a]? = some sort) (ht : TypeClass ty sort)
    (hv : ValueTyped world sort v) (bound : a < s.heap.size) :
    HeapTyped world {s with heap := s.heap.set a (.value ty v) bound} := by
  refine ⟨by simpa using h.size, ?_⟩
  intro i kind hi
  by_cases he : a = i
  · subst i
    have hk : kind = sort := Option.some.inj (hi.symm.trans ha)
    subst kind
    exact ⟨ty, v, by simp, ht, hv⟩
  · obtain ⟨oldTy, oldV, hc, hty, hval⟩ := h.cells i kind hi
    exact ⟨oldTy, oldV, by simpa [Array.getElem?_set, he] using hc, hty, hval⟩

/-- Every correctly sorted write succeeds on the real typed-cell path and
preserves the address schema, including all existing captured aliases. -/
theorem HeapTyped.store {world s sort loc v} (h : HeapTyped world s)
    (hl : AddressTyped world sort loc) (hv : ValueTyped world sort v) :
    ∃ s', storeLoc s loc v = .ok s' ∧ HeapTyped world s' ∧
      BooleanRuntime.SameContext s s' ∧ s'.heap.size = s.heap.size := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨ty, old, hc, ht, _⟩ := h.cells a sort ha
  have bound := (Array.getElem?_eq_some_iff.mp hc).1
  have cell := (Array.getElem?_eq_some_iff.mp hc).2
  refine ⟨{s with heap := s.heap.set a (.value ty v) bound}, ?_,
    h.set ha ht hv bound, ?_, by simp⟩
  · simp [storeLoc, ExecState.updateCell, bound, cell, normalize_typed ht]
    rfl
  · rfl

def AddressAt (world : World) (ty : Ty) (loc : Loc) : Prop :=
  ∃ sort, TypeClass ty sort ∧ AddressTyped world sort loc

def ValueAt (world : World) (ty : Ty) (v : GoValue) : Prop :=
  ∃ sort, TypeClass ty sort ∧ ValueTyped world sort v

theorem AddressAt.mono {world next ty loc} (h : AddressAt world ty loc)
    (ext : Extends world next) : AddressAt next ty loc := by
  obtain ⟨sort, ht, hl⟩ := h
  exact ⟨sort, ht, hl.mono ext⟩

theorem AddressAt.sorted {world ty sort loc} (h : AddressAt world ty loc)
    (ht : TypeClass ty sort) : AddressTyped world sort loc := by
  obtain ⟨kind, hk, hl⟩ := h
  cases typeClass_unique hk ht
  exact hl

theorem ValueAt.mono {world next ty v} (h : ValueAt world ty v)
    (ext : Extends world next) : ValueAt next ty v := by
  obtain ⟨sort, ht, hv⟩ := h
  exact ⟨sort, ht, hv.mono ext⟩

theorem ValueAt.sorted {world ty sort v} (h : ValueAt world ty v)
    (ht : TypeClass ty sort) : ValueTyped world sort v := by
  obtain ⟨kind, hk, hv⟩ := h
  cases typeClass_unique hk ht
  exact hv

end GoLean.GoCore.RecoveryRuntime
