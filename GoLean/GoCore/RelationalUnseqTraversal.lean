import GoLean.GoCore.RelationalUnseqGraph
import GoLean.GoCore.RelationalStorePathFor

namespace GoLean.GoCore.Relational.Unseq

/-- Finite all-ready traversal carrying actual store-uniform occurrence paths.
The status predicate need not fix a whole heap. Resource interpreters and the
state safety interpretation consume the same paths and every ready branch. -/
inductive Traversal (ctx : ProgramCtx) (g : UnseqGraph) (env : LocalEnv)
    (fact : List UnseqStatus → Store → Prop) (policy : Machine.Config → Prop)
    (head : Nat → Expr) (value : Nat → GoValue) : List UnseqStatus → Prop where
  | done {st} : Binary g st → g.allSettled st = true →
      Traversal ctx g env fact policy head value st
  | next {st} : Binary g st → g.allSettled st = false → g.ready st ≠ [] →
      (∀ i, i ∈ g.ready st → ReadOnlyExprFor ctx (fact st) policy env (head i) (value i)) →
      (∀ i, i ∈ g.ready st → Traversal ctx g env fact policy head value (st.set i .done)) →
      Traversal ctx g env fact policy head value st

theorem Ranked.traversal {ctx g env fact policy head value} (ranked : Ranked g)
    (paths : ∀ st, Binary g st → ∀ i, i ∈ g.ready st →
      ReadOnlyExprFor ctx (fact st) policy env (head i) (value i))
    (st : List UnseqStatus) (binary : Binary g st) :
    Traversal ctx g env fact policy head value st := by
  generalize measure : st.count .active = n
  induction n using Nat.strongRecOn generalizing st with
  | ind n ih =>
    cases settled : g.allSettled st with
    | true => exact .done binary settled
    | false =>
      obtain ⟨i, ready, _⟩ := ranked.progress binary settled
      refine .next binary settled (List.ne_nil_of_mem ready) (paths st binary) ?_
      intro i hi
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hi
      exact ih _ (by rw [← measure]; exact active_count_decreases (UnseqGraph.ready_active hj).2)
        _ (binary.set_done i) rfl

end GoLean.GoCore.Relational.Unseq
