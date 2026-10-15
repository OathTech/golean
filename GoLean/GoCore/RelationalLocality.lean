import GoLean.GoCore.RelationalMemory

/-! Operational root support, including failed reads and allocator bounds.
This is not derived from an access trace and is not context extension. -/
namespace GoLean.GoCore.Relational
open Machine

def AgreeOn (roots : Nat → Prop) (s t : Store) : Prop :=
  s.heap.size = t.heap.size ∧ ∀ i, roots i → s.heap[i]? = t.heap[i]?

theorem loadLoc_agrees {ctx : ProgramCtx} {s t : Store} (l : Loc)
    (same : s.heap[(Loc.rootPath l).1.id]? = t.heap[(Loc.rootPath l).1.id]?) :
    loadLoc ctx s l = loadLoc ctx t l := by
  induction l with
  | base a =>
      change s.heap[a.id]? = t.heap[a.id]? at same
      simp only [loadLoc, Heap.lookup, same]
  | field l ty name ih => simp only [loadLoc, ih (by simpa [Loc.rootPath] using same)]
  | index l index ih => simp only [loadLoc, ih (by simpa [Loc.rootPath] using same)]

theorem loadRoot_agrees {ctx : ProgramCtx} {s t : Store} (l : Loc)
    (same : s.heap[(Loc.rootPath l).1.id]? = t.heap[(Loc.rootPath l).1.id]?) :
    loadRoot ctx s l = loadRoot ctx t l := by
  cases l with
  | base a => exact loadLoc_agrees (ctx := ctx) (.base a) same
  | field => rfl
  | index => rfl

/-- Different roots suffice; distinct paths under one root do not. The
conclusion preserves success and every failure result, not only read values. -/
theorem write_preserves_load {ctx : ProgramCtx} {s t : Store} {dst src : Loc}
    {v : GoValue} (write : storeLoc ctx s dst v = .ok t)
    (different : (Loc.rootPath src).1.id ≠ (Loc.rootPath dst).1.id) :
    loadLoc ctx t src = loadLoc ctx s src := by
  obtain ⟨size, outside⟩ := write_support write
  apply loadLoc_agrees
  by_cases bound : (Loc.rootPath src).1.id < s.heap.size
  · exact outside _ bound different
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- Exact fresh-address equality fails whenever allocator bounds differ,
even though both allocations can have empty race traces. Later extension
needs a location correspondence mapping the two fresh roots. -/
theorem allocations_distinct_bounds {ctx : ProgramCtx} {s t s' t' : Store}
    {v w : GoValue} {ty uy : Ty} {l m : Loc}
    (left : Store.alloc ctx s v ty = .ok (l, s'))
    (right : Store.alloc ctx t w uy = .ok (m, t'))
    (different : s.heap.size ≠ t.heap.size) : l ≠ m := by
  obtain ⟨rfl, _⟩ := Store.alloc_shape left
  obtain ⟨rfl, _⟩ := Store.alloc_shape right
  intro equal
  exact different (congrArg (fun l => (Loc.rootPath l).1.id) equal)

end GoLean.GoCore.Relational
