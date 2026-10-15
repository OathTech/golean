import U1RD8.Source

namespace U1RD8
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.Relational
open GoLean.GoCore.Relational.Unseq
open GoLean.Logic GoLean.IrisCustomer RelationalCodeX.Sweep

theorem empty_path (ctx : ProgramCtx) (e env : LocalEnv) (rest : List Stmt) (k : Cont)
    (fact : Store → Prop) : StorePathFor ctx fact (Quiet ctx)
      (.exec (.seqn #[]) e (.seq rest env k)) (destination env rest k) := by
  apply (StorePathFor.step (d := .next (seqCont [] e (.seq rest env k)))
    (fun _ _ => ⟨_, Step.seqn, rfl⟩) ⟨(by intro h; cases h), rfl⟩
    (by intro Ev O s ch; rfl) .refl).trans
  by_cases same : env = e
  · subst e; simpa [seqCont, destination] using
      (StorePathFor.refl (ctx := ctx) (fact := fact) (policy := Quiet ctx)
        (c := destination env rest k))
  · simp only [seqCont, if_neg same]
    exact .step (fun _ _ => ⟨_, Step.seqDone, rfl⟩)
      ⟨(by intro h; cases h), rfl⟩ (by intro Ev O s ch; rfl) .refl

theorem rows_get (p q base : Nat) (x y : Input) (st : List UnseqStatus)
    (i : Nat) (hi : i < 3) :
    (rows p q base x y st)[i+2]? = some (base+i, cell (content x y st i)) := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> simp [rows]

theorem rows_set (p q base : Nat) (x y : Input) (st : List UnseqStatus)
    (binary : Binary graph st) (i : Nat) (hi : i < 3) :
    (rows p q base x y st).set (i+2) (base+i,cell (result x y i)) =
      rows p q base x y (st.set i .done) := by
  have len : st.length = 3 := by simpa [graph] using binary.1
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;>
    simp [rows, content, len]

theorem body_eq (i : Nat) (hi : i < graph.occs.length) :
    graph.occs[i].body = .eval (i+3) (head i) := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by simp [graph] at hi; omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

theorem binding (env : LocalEnv) (base i : Nat) (hi : i < 3) :
    (scope env base).lookup (i+3) = some (.base ⟨base+i⟩) := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl
  · exact Frame.lookup_declared env.pushScope base [3,4,5] (by decide) ⟨0,by decide⟩
  · exact Frame.lookup_declared env.pushScope base [3,4,5] (by decide) ⟨1,by decide⟩
  · exact Frame.lookup_declared env.pushScope base [3,4,5] (by decide) ⟨2,by decide⟩

theorem normal (ctx : ProgramCtx) (x y : Input) (i : Nat) :
    normalizeValueForTy ctx (.int .int64) (val (result x y i)) = .ok (val (result x y i)) := by
  have hn : IntKind.int64.normalize (result x y i) = result x y i := by
    cases i with
    | zero => exact x.property
    | succ i => cases i with
      | zero => exact y.property
      | succ i => exact IntKind.normalize_idem _ _
  simp [normalizeValueForTy, normalizeValueForTyTy, val, hn]

/-- Interpret the general all-ready traversal. Every recursive branch and its
actual expression path is consumed; there is no schedule enumeration. -/
theorem interpret {ctx env p q base x y st}
    (tree : Traversal ctx graph (scope env base) (fun st => Facts (rows p q base x y st))
      (Quiet ctx) head (fun i => val (result x y i)) st)
    (rest : List Stmt) (k : Cont) :
    Plan ctx (destination env rest k)
      (fun rs => ∃ b, rs = [(p,cell x.val),(q,cell y.val)] ++ allocated b (results x y))
      (.next (.unseqK graph (.seqn #[]) st [] (scope env base) .pick (.seq rest env k)))
      (rows p q base x y st) := by
  induction tree with
  | @done st binary settled =>
    apply path_plan (completion_path ranked binary settled rfl
      (quiet_next _ _ _ _ _ _ _) (by intro Ev O s ch; rfl))
    apply path_plan (empty_path _ _ _ _ _ _)
    apply Plan.done
    refine ⟨base, ?_⟩
    have h0 := binary.settled_done settled 0 (by decide)
    have h1 := binary.settled_done settled 1 (by decide)
    have h2 := binary.settled_done settled 2 (by decide)
    simp [rows, content, h0, h1, h2, result, allocated, results, Nat.add_assoc]
  | @next st binary pending nonempty paths _ ih =>
    refine Plan.choose (ι := {i : Nat // i ∈ graph.ready st})
      (next := fun i => .next (.unseqK graph (.seqn #[]) st [] (scope env base)
        (.run i.val) (.seq rest env k)))
      ⟨(by intro h; cases h), rfl⟩ (quiet_next _ _ _ _ _ _ _) ?_ ?_
    · intro s _ ch
      obtain ⟨i, ready, l, residual, ht, hr⟩ := scheduler_cover
        (ctx := ctx) (env := scope env base) (body := .seqn #[])
        (tail := ⟨.seq rest env k⟩) binary pending nonempty s ch
      exact ⟨⟨i,ready⟩,l,residual,ht,hr⟩
    intro ⟨i, ready⟩
    have hi : i < graph.occs.length := List.mem_range.mp (List.mem_filter.mp ready).1
    have small : i < 3 := by simpa [graph] using hi
    have get : graph.occs[i]? = some graph.occs[i] := List.getElem?_eq_getElem hi
    apply path_plan (StorePathFor.step
      (d := .evalE (head i) (scope env base)
        (.unseqK graph (.seqn #[]) st [] (scope env base) (.wait i) (.seq rest env k)))
      (fun _ _ => ⟨_, Step.unseqRunEval get (body_eq i hi), rfl⟩)
      ⟨(by intro h; cases h), rfl⟩ (quiet_next _ _ _ _ _ _ _) .refl)
    apply path_plan (paths i ready ⟨.unseqK graph (.seqn #[]) st []
      (scope env base) (.wait i) (.seq rest env k)⟩)
    apply write_at (rows_get p q base x y st i small)
      (quiet_wait _ _ _ _ _ _ _ _) (int_shape _ _ _ _)
      (binder_effect get (body_eq i hi) (binding env base i small) (normal ctx x y i))
    rw [rows_set p q base x y st binary i small]
    exact ih i ready

theorem simulation : SimulationLaw := by
  intro ctx env rest k p q x y h0 h1 h3 h4 h5
  refine Plan.allocate zeros
    (fun base => .next (.unseqK graph (.seqn #[]) graph.initStatus []
      (scope env base) .pick (.seq rest env k)))
    ⟨(by intro h; cases h), rfl⟩ (by intro Ev O s ch; rfl) ?_ ?_
  · intro s
    refine ⟨_, Step.unseqEnter graph_wellFormed (entry_check env p q h0 h1 h3 h4 h5) ?_, rfl⟩
    exact Frame.defaults (ctx := ctx) [(3,.integer .int64),(4,.integer .int64),(5,.integer .int64)]
      env.pushScope s
  · intro base _
    simpa [rows, content, UnseqGraph.initStatus, graph, allocated, zeros, Nat.add_assoc] using
      interpret (traversal ctx env p q base x y h0 h1) rest k

theorem closed_guarded : GuardedTarget := guarded_acceptance simulation

end U1RD8
