import U1.Symbolic

namespace U1.Controls
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational

/-- Unordered aliased write/read effects cannot satisfy the stable-expression
domain: the actual read result changes. Stores and the aliased address vary. -/
theorem alias_order (ctx : ProgramCtx) (s : Store) (a : Nat)
    (cell : s.heap[a]? = some (.value .bool (.bool false))) :
    ∃ t, storeLoc ctx s (.base ⟨a⟩) (.bool true) = .ok t ∧
      loadRoot ctx s (.base ⟨a⟩) = .ok (.bool false) ∧
      loadRoot ctx t (.base ⟨a⟩) = .ok (.bool true) := by
  have bound := (Array.getElem?_eq_some_iff.mp cell).1
  refine ⟨⟨s.heap.set a (.value .bool (.bool true)) bound⟩,
    write_root cell rfl, read_root cell, ?_⟩
  apply read_root (ty := .bool)
  simp [Heap.lookup]

/-- Output ordering is observable even for actions with no heap accesses.
This is the actual print rendering used by the statement apply and its label.
Such actions cannot be admitted merely by disjoint root supports. -/
theorem output_order :
    stmtOpOut (.print false) [.bool false] ++ stmtOpOut (.print false) [.bool true] ≠
    stmtOpOut (.print false) [.bool true] ++ stmtOpOut (.print false) [.bool false] := by
  intro equal
  have projected := congrArg (List.map (fun x => x.bytes.size)) equal
  change [5, 4] = [4, 5] at projected
  contradiction

theorem print_has_no_heap_effect (ctx : ProgramCtx) (s : Store) (tape : Choices) (b : Bool) :
    applyStmtOp ctx s tape (.print false) 0 [.bool b] = .ok (s, tape, [], []) := by
  cases b <;> rfl

/-- The allocator obstruction uses two successful actual allocations, not a
postulated fresh-address function. The old heaps and their sizes are arbitrary. -/
theorem allocation_bound (ctx : ProgramCtx) (s t : Store) (sizes : s.heap.size ≠ t.heap.size) :
    ∃ l m s' t', Store.alloc ctx s (.bool false) .bool = .ok (l,s') ∧
      Store.alloc ctx t (.bool false) .bool = .ok (m,t') ∧ l ≠ m := by
  refine ⟨.base ⟨s.heap.size⟩, .base ⟨t.heap.size⟩,
    ⟨s.heap.push (.value .bool (.bool false))⟩,
    ⟨t.heap.push (.value .bool (.bool false))⟩, rfl, rfl, ?_⟩
  exact allocations_distinct_bounds (ctx := ctx) (v := .bool false) (w := .bool false)
    (ty := .bool) (uy := .bool) rfl rfl sizes

end U1.Controls
