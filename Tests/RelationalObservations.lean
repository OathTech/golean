import GoLean.Relational

/-! Facade-only symbolic clients of the complete semantic observation surface. -/
namespace Tests.RelationalObservations
open GoLean GoCore Relational Boundary

-- An empty base label does not establish observer silence.
theorem pure_return_observable (ctx : ProgramCtx) (fid : FuncId) (k : Continuation) (s : Store) :
    Pure ctx (returning fid k s) (resumed k s) ∧
    events ctx (returning fid k s) = [.returned ⟨fid, [], s⟩] := by
  have h : ReturnsDiscarded (returning fid k s) (resumed k s) ⟨fid, [], s⟩ := .returning
  exact ⟨h.pure, events_return_iff.mpr ((return?_on_transition h.pure.1).mpr h.observed)⟩

-- An unfinished prefix supplies a semantic history, without a success/safety premise.
theorem finite_history {Ev : Type} (observe : BoundaryEvent → List Ev) {ctx a b ls}
    (h : Run ctx a ls b) : ∃ es, History observe ctx a ls es b := History.coverage h

-- Splitting labels splits the chronological history at the same intermediate state.
theorem split_history {Ev : Type} (observe : BoundaryEvent → List Ev) {ctx a b xs ys es}
    (h : History observe ctx a (xs ++ ys) es b) :
    ∃ c left right, es = left ++ right ∧ History observe ctx a xs left c ∧
      History observe ctx c ys right b := h.split

#print axioms Transition.boundary_cases
#print axioms entry_iff_depth
#print axioms return_iff_depth
#print axioms entry?_on_transition
#print axioms return?_on_transition
#print axioms Returns.transition
#print axioms History.coverage
#print axioms History.append_iff
#print axioms History.unique
#print axioms History.realize
#print axioms History.on_prefix
#print axioms pure_return_observable
end Tests.RelationalObservations
