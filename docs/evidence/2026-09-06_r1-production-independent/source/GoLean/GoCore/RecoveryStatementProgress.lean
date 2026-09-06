import GoLean.GoCore.RecoveryValueCalls

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem block_advances {world fs s Γ env decls ss k}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : StorageParams decls) (hd : DistinctParams decls)
    (hs : ControlStmts fs (push Γ decls) ss.toList) (hk : ReturnCont world fs k) :
    Advances world fs s (.exec (.block decls ss) env k) := by
  obtain ⟨next, env', t, run, ex, hh, he', ctx, _⟩ :=
    allocDecls_typed decls.toList heap he.push ht
  have henv : EnvTyped next (push Γ decls) env' := by
    simpa using he'.pushedDecls hd
  exact fun ch => ⟨next, _, t, by simp [stepFn, run]; rfl,
    ⟨ex, hh, ctx⟩, .next (.stmt (.seq henv hs (hk.mono ex)))⟩

theorem assign_advances {world fs s Γ env target expr k}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : Assignment Γ target expr) (hk : ReturnCont world fs k) :
    Advances world fs s (.exec (.assign target expr) env k) := by
  obtain ⟨ty, targetTyped, exprTyped⟩ := assignment_typed ht
  obtain ⟨plan, run, hplan⟩ := target_plan_typed targetTyped
  cases hplan with
  | root hty hx =>
    let q : Param := ⟨"", ty⟩
    exact advances_same heap (.eval he hx
      (.target (p := q) (before := []) he hty .nil .nil
        (.expressions (.cons exprTyped .nil)) hk)) (fun _ => by simp [stepFn, run])

theorem direct_call_advances {p : Program} {world s Γ env targets fid args k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : DirectCall p.funcs Γ targets fid args) (hk : ReturnCont world p.funcs k) :
    Advances world p.funcs s (.exec (.call targets fid args) env k) := by
  obtain ⟨f, hf, ha, ht⟩ := ht
  obtain ⟨plans, runPlans, plansTyped⟩ := targets_plan_typed ht
  cases hargs : args.toList with
  | nil =>
    rw [hargs] at ha
    have arity : f.args.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using ha.length.symm)
    have values : ParamsValues world f.args.toList [] := arity ▸ .nil
    intro ch
    obtain ⟨next, env', roots, t, run, ex, hw, control⟩ :=
      call_entry_control hp hc heap hf values he plansTyped hk ch
    exact ⟨next, _, t, by
      simp only [stepFn, runPlans, hargs, run]
      simp [deliverS, hw, Bind.bind, Except.bind, Pure.pure, Except.pure], ex, control⟩
  | cons e es =>
    rw [hargs] at ha
    generalize hps : f.args.toList = ps at ha
    cases ha with
    | cons hx hxs =>
      exact advances_same heap (.eval he (.typed hx)
        (.callArgs (before := []) he hf hps .nil hxs plansTyped hk))
        (fun _ => by simp [stepFn, runPlans, hargs])

theorem closure_call_advances {world fs s Γ env targets callee args k}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : ClosureCall fs Γ targets args callee) (hk : ReturnCont world fs k) :
    Advances world fs s (.exec (.callValue targets callee args) env k) := by
  cases ht with
  | known hf _ ha ht =>
    obtain ⟨caps, ps, arity, hcaps, hargs⟩ := arguments_split ha
    obtain ⟨plans, run, hplans⟩ := targets_plan_typed ht
    exact advances_same heap (.eval he (.closure hcaps)
      (.callCallee he hf arity hargs hplans hk)) (fun _ => by simp [stepFn, run])

theorem defer_call_advances {world fs s Γ env callee args k}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : DeferredCall fs Γ args callee) (hk : ReturnCont world fs k) :
    Advances world fs s (.exec (.deferCall callee args) env k) := by
  cases ht with
  | known hf _ ha =>
    obtain ⟨caps, ps, arity, hcaps, hargs⟩ := arguments_split ha
    exact advances_same heap (.eval he (.closure hcaps)
      (.deferCallee he hf arity hargs hk)) (fun _ => rfl)

theorem exec_neutral_advances {p : Program} {world s Γ env stmt k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hs : ControlStmt p.funcs false Γ stmt) (hn : declarationCount stmt = 0)
    (hk : ReturnCont world p.funcs k) : Advances world p.funcs s (.exec stmt env k) := by
  cases hs with
  | seqn hs =>
    exact advances_same heap (.next (.stmt (hk.seqCont_neutral he hs hn))) (fun _ => rfl)
  | block ht hd hs => exact block_advances heap he ht hd hs hk
  | assign ht => exact assign_advances heap he ht hk
  | branch he' ht hf nt nf =>
    exact advances_same heap (.eval he (.value he') (.branch he ht hf nt nf hk)) (fun _ => rfl)
  | call ht => exact direct_call_advances hp hc heap he ht hk
  | closureCall ht => exact closure_call_advances heap he ht hk
  | deferCall ht => exact defer_call_advances heap he ht hk
  | panic ht => exact advances_same heap (.eval he (.boxed ht) (.panic hk)) (fun _ => rfl)
  | ret => exact advances_same heap (.returning hk) (fun _ => rfl)

theorem exec_frame_advances {p : Program} {world s Γ env stmt plans tenv results ds k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hs : ControlStmt p.funcs false Γ stmt)
    (hk : ReturnCont world p.funcs (.frame plans tenv results ds k false)) :
    Advances world p.funcs s (.exec stmt env (.frame plans tenv results ds k false)) := by
  cases hs with
  | seqn hs => exact advances_same heap (.next (.stmt (.seq he hs hk))) (fun _ => rfl)
  | block ht hd hs => exact block_advances heap he ht hd hs hk
  | assign ht => exact assign_advances heap he ht hk
  | branch he' ht hf nt nf =>
    exact advances_same heap (.eval he (.value he') (.branch he ht hf nt nf hk)) (fun _ => rfl)
  | call ht => exact direct_call_advances hp hc heap he ht hk
  | closureCall ht => exact closure_call_advances heap he ht hk
  | deferCall ht => exact defer_call_advances heap he ht hk
  | panic ht => exact advances_same heap (.eval he (.boxed ht) (.panic hk)) (fun _ => rfl)
  | ret => exact advances_same heap (.returning hk) (fun _ => rfl)

theorem initialization_advances {world fs s Γ env q rest k}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (ht : StorageType q.typ) (hs : ControlStmts fs (declare Γ q) rest)
    (hk : ReturnCont world fs k) :
    Advances world fs s (.exec (.initialization q) env (.seq rest env k)) := by
  obtain ⟨sort, v, run, hty, hv⟩ := default_storage ht world s
  have ex := Extends.push world sort
  have he' := (he.mono ex).declare q
    ⟨sort, hty, heap.allocated_address (sort := sort) (ty := q.typ) (v := v)⟩
  exact fun ch => ⟨world.push sort, _, (s.alloc v q.typ).2,
    by simp [stepFn, run]; rfl,
    ⟨ex, heap.alloc hty hv, rfl⟩, .next (.stmt (.seq he' hs (hk.mono ex)))⟩

theorem exec_seq_advances {p : Program} {world s Γ env stmt rest k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hs : ControlStmt p.funcs true Γ stmt) (hrest : ControlStmts p.funcs (afterStmt Γ stmt) rest)
    (hk : ReturnCont world p.funcs k) :
    Advances world p.funcs s (.exec stmt env (.seq rest env k)) := by
  cases hs with
  | seqn hs =>
    exact advances_same heap (.next (.stmt (.seq he (hs.append hrest) hk)))
      (fun _ => by simp [stepFn, seqCont])
  | initialization ht => exact initialization_advances heap he ht hrest hk
  | block ht hd hs => exact block_advances heap he ht hd hs (.seq he hrest hk)
  | assign ht => exact assign_advances heap he ht (.seq he hrest hk)
  | branch he' ht hf nt nf =>
    exact advances_same heap (.eval he (.value he') (.branch he ht hf nt nf (.seq he hrest hk)))
      (fun _ => rfl)
  | call ht => exact direct_call_advances hp hc heap he ht (.seq he hrest hk)
  | closureCall ht => exact closure_call_advances heap he ht (.seq he hrest hk)
  | deferCall ht => exact defer_call_advances heap he ht (.seq he hrest hk)
  | panic ht =>
    exact advances_same heap (.eval he (.boxed ht) (.panic (.seq he hrest hk)))
      (fun _ => rfl)
  | ret => exact advances_same heap (.returning (.seq he hrest hk)) (fun _ => rfl)

end GoLean.GoCore.RecoveryRuntime
