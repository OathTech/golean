import GoLean.GoCore.RelationalControl

/-!
# Pointer assignment from source variables

This construct law covers `*p = v`, with arbitrary identifiers, locations,
values, stores and continuation. Its premises are binding lookup and memory
operation results, not a successful machine execution or a well-formedness
assumption. Target/RHS/commit bookkeeping stays inside this proof. Every
actual label is retained; the run is pick-free and emits no output.
-/

namespace GoLean.GoCore.Relational

open Machine

/-- Execute `*p = v` from operation-derived binding/read/write premises.
The target can be an interior location or alias either parameter slot; both
operands are read before the write. No distinctness or typing premise is
added beyond what the successful operations themselves require. -/
theorem assign_pointer_variables (ctx : ProgramCtx) (s t : Store)
    (env : LocalEnv) (k : Continuation) (pId vId : VarId)
    (pSlot vSlot target : Loc) (value : GoValue)
    (pointerLookup : LocalEnv.lookup env pId = some pSlot)
    (valueLookup : LocalEnv.lookup env vId = some vSlot)
    (pointerRead : loadRoot ctx s pSlot = .ok (.addr target))
    (valueRead : loadRoot ctx s vSlot = .ok value)
    (write : storeLoc ctx s target value = .ok t) :
    ∃ ls, Run ctx (statement (.assign (.addr (.var pId)) (.var vId)) env k s)
      ls (resumed k t) ∧ (∀ label ∈ ls, label.picks = []) ∧
      (∀ label ∈ ls, label.out = []) := by
  let pointerK : Continuation := ⟨.tgtOpK (.chain []) [] [] [] [] .vals
    [.var vId] [] (.seqn #[]) env k.toMachine⟩
  let valueK : Continuation := ⟨.rhsK .vals [.chain (.addr target) [] []]
    [] [] (.seqn #[]) env k.toMachine⟩
  obtain ⟨pointerTrace, hp⟩ := read_variable ctx s env pointerK pId pSlot
    (.addr target) pointerLookup pointerRead
  obtain ⟨valueTrace, hv⟩ := read_variable ctx s env valueK vId vSlot
    value valueLookup valueRead
  have hw : storeTarget ctx s (.chain (.addr target) [] []) value =
      .ok (t, [.access .write (.data target.canon)]) := by
    simp [storeTarget, storeTarget.plan, resolveChain, valueAsLoc, Mem.store,
      write, Bind.bind, Except.bind, pure, Except.pure]
  obtain ⟨ls, finish, picks, output⟩ := empty_sequence_run ctx env k t
  have start : Transition ctx
      (statement (.assign (.addr (.var pId)) (.var vId)) env k s) ⟨[], [], []⟩
      (expression (.var pId) env pointerK s) := Step.assignFirst rfl
  have rhs : Transition ctx (returned (.addr target) pointerK s) ⟨[], [], []⟩
      (expression (.var vId) env valueK s) := Step.tgtOpRhs rfl
  have values : Transition ctx (returned value valueK s) ⟨[], [], []⟩
      ⟨.next (.storeK [.chain (.addr target) [] []] [value] (.seqn #[]) env k.toMachine), s⟩ :=
    Step.rhsStores rfl rfl
  have commit : Transition ctx
      ⟨.next (.storeK [.chain (.addr target) [] []] [value] (.seqn #[]) env k.toMachine), s⟩
      ⟨[.access .write (.data target.canon)], [], []⟩
      ⟨.next (.storeK [] [] (.seqn #[]) env k.toMachine), t⟩ :=
    Step.storeStep (r := .ok (t, [.access .write (.data target.canon)]))
      (by rw [hw]; rfl) rfl
  have done : Transition ctx ⟨.next (.storeK [] [] (.seqn #[]) env k.toMachine), t⟩
      ⟨[], [], []⟩ (statement (.seqn #[]) env k t) := Step.storeDone
  refine ⟨⟨[], [], []⟩ :: ⟨pointerTrace, [], []⟩ :: ⟨[], [], []⟩ ::
    ⟨valueTrace, [], []⟩ :: ⟨[], [], []⟩ ::
    ⟨[.access .write (.data target.canon)], [], []⟩ :: ⟨[], [], []⟩ :: ls,
    ?_, ?_, ?_⟩
  · exact .cons start (.cons hp (.cons rhs (.cons hv
      (.cons values (.cons commit (.cons done finish))))))
  · simpa using picks
  · simpa using output

end GoLean.GoCore.Relational
