import GoLean.GoCore.RelationalMemory
import GoLean.GoCore.RelationalUnseqGraph

namespace GoLean.GoCore.Relational.Unseq
open Machine

/-- A sweep's fresh binder interval; all other cells are stable. The initial
store here is the actual post-allocation store, with allocator bound retained. -/
structure HeapDomain where
  initial : Store
  base : Nat
  cells : List Param
  zero : Nat → GoValue
  value : Nat → GoValue
  allocated : base + cells.length ≤ initial.heap.size
  initial_cells : ∀ i (hi : i < cells.length),
    initial.heap[base + i]? = some (.value cells[i].typ (zero i))

def HeapDomain.At (h : HeapDomain) (st : List UnseqStatus) (s : Store) : Prop :=
  s.heap.size = h.initial.heap.size ∧
  (∀ i (hi : i < h.cells.length), s.heap[h.base + i]? =
    some (.value h.cells[i].typ (if st[i]? = some .done then h.value i else h.zero i))) ∧
  ∀ a, (¬ ∃ i, i < h.cells.length ∧ a = h.base + i) →
    s.heap[a]? = h.initial.heap[a]?

theorem HeapDomain.at_initial (h : HeapDomain) :
    h.At (List.replicate h.cells.length .active) h.initial := by
  refine ⟨rfl, ?_, fun _ _ => rfl⟩
  intro i hi
  simpa [hi] using h.initial_cells i hi

theorem HeapDomain.At.read {ctx : ProgramCtx} {h : HeapDomain}
    {st : List UnseqStatus} {s : Store} (hs : h.At st s)
    (i : Nat) (hi : i < h.cells.length) (done : st[i]? = some .done) :
    loadRoot ctx s (.base ⟨h.base + i⟩) = .ok (h.value i) := by
  apply read_root (ty := h.cells[i].typ)
  simpa [Heap.lookup, done] using hs.2.1 i hi

theorem HeapDomain.At.read_old {ctx : ProgramCtx} {h : HeapDomain}
    {st : List UnseqStatus} {s : Store} (hs : h.At st s) {a : Nat} {ty v}
    (old : a < h.base) (cell : h.initial.heap[a]? = some (.value ty v)) :
    loadRoot ctx s (.base ⟨a⟩) = .ok v := by
  apply read_root (ty := ty)
  change s.heap[a]? = some (.value ty v)
  rw [hs.2.2 a (by rintro ⟨i, _, hi⟩; omega)]
  exact cell

theorem HeapDomain.At.unique {h : HeapDomain} {st : List UnseqStatus} {s t : Store}
    (hs : h.At st s) (ht : h.At st t) : s = t := by
  have heaps : s.heap = t.heap := by
    apply Array.ext_getElem?
    intro a
    by_cases owned : ∃ i, i < h.cells.length ∧ a = h.base + i
    · obtain ⟨i, hi, rfl⟩ := owned
      rw [hs.2.1 i hi, ht.2.1 i hi]
    · rw [hs.2.2 a owned, ht.2.2 a owned]
  cases s; cases t; cases heaps; rfl

theorem HeapDomain.At.unique_done {h : HeapDomain} {st su : List UnseqStatus} {s t : Store}
    (hs : h.At st s) (ht : h.At su t)
    (sd : ∀ i, i < h.cells.length → st[i]? = some .done)
    (td : ∀ i, i < h.cells.length → su[i]? = some .done) : s = t := by
  apply hs.unique
  refine ⟨ht.1, ?_, ht.2.2⟩
  intro i hi
  simpa [sd i hi, td i hi] using ht.2.1 i hi

/-- The real allocation operation initializes the interval invariant. No
equation identifying fresh locations across different old bounds is used. -/
def HeapDomain.ofAllocation {ctx : ProgramCtx} (before : Store)
    (env env' : LocalEnv) (after : Store) (cells : List Param)
    (zero value : Nat → GoValue)
    (allocation : allocDecls ctx env before cells = .ok (env', after))
    (defaults : ∀ i (hi : i < cells.length), defaultValue ctx cells[i].typ = .ok (zero i))
    (normal : ∀ i (hi : i < cells.length),
      normalizeValueForTy ctx cells[i].typ (zero i) = .ok (zero i)) : HeapDomain where
  initial := after
  base := before.heap.size
  cells := cells
  zero := zero
  value := value
  allocated := by rw [allocDecls_heap_size _ _ _ allocation]; exact Nat.le_refl _
  initial_cells := by
    intro i hi
    obtain ⟨v0, v, hd, hn, hh⟩ := allocDecls_zero _ _ _ allocation i hi
    rw [defaults i hi] at hd
    cases hd
    rw [normal i hi] at hn
    cases hn
    exact hh

theorem HeapDomain.At.write {ctx : ProgramCtx} {h : HeapDomain}
    {st : List UnseqStatus} {s : Store} (hs : h.At st s)
    (length : st.length = h.cells.length)
    (i : Nat) (hi : i < h.cells.length)
    (normal : normalizeValueForTy ctx h.cells[i].typ (h.value i) = .ok (h.value i)) :
    ∃ t, storeLoc ctx s (.base ⟨h.base + i⟩) (h.value i) = .ok t ∧
      h.At (st.set i .done) t := by
  have cell := hs.2.1 i hi
  have lookup : Heap.lookup s.heap (.base ⟨h.base + i⟩) =
      some (.value h.cells[i].typ (if st[i]? = some .done then h.value i else h.zero i)) := cell
  have write := write_root lookup normal
  refine ⟨_, write, by simpa using hs.1, ?_, ?_⟩
  · intro j hj
    by_cases ij : i = j
    · subst j
      have bound : i < st.length := by omega
      simp [List.getElem?_set_self bound]
    · have addresses : h.base + i ≠ h.base + j := by omega
      dsimp only
      rw [Array.getElem?_set_ne _ addresses]
      simpa [List.getElem?_set_ne ij] using hs.2.1 j hj
  · intro a outside
    have ne : h.base + i ≠ a := fun eq => outside ⟨i, hi, eq.symm⟩
    simpa [ne] using hs.2.2 a outside

end GoLean.GoCore.Relational.Unseq
