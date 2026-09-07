import GoLean.GoCore.RecoverySetupReadout

/-! Reusable actual ordinary/deferred call entry. Incoming root references
retain their existing pointees while fresh parameter and result slots are
allocated. The statement contains no assumption about the callee's run. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem enterFrame_typed {p : Program} {world s fid f args}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hf : findFunctionIn? p.funcs fid = some f)
    (values : ParamsValues world f.args.toList args) :
    ∃ next env locs s',
      enterFrame s fid args = .ok (f, env, locs, s') ∧
      Extends world next ∧ HeapTyped next s' ∧
      EnvTyped next (initialContext f) env ∧ ResultRoots next f.results.toList locs ∧
      BooleanRuntime.SameContext s s' ∧
      s'.heap.size = s.heap.size + f.args.size + f.results.size ∧
      FunctionTyped p.funcs f ∧ f.wrapper = false := by
  have hft := hp.2.2.1 f (BooleanRuntime.findFunction_mem hf)
  have harity : f.args.size = args.length := by simpa using values.length
  have hfunctions : s.functions = p.funcs := (congrArg ExecState.functions hc).symm
  have hmethods : s.methods = #[] :=
    (congrArg ExecState.methods hc).symm.trans (Array.eq_empty_of_size_eq_zero hp.2.1)
  have hdispatch : dynamicDispatch? s f args.toArray = .ok none := by
    simp [dynamicDispatch?, methodInfoByFuncId?, hmethods]
  obtain ⟨w₁, env₁, s₁, hb, ex₁, hh₁, he₁, hc₁, hs₁⟩ :=
    bindParams_typed heap (EnvTyped.empty world) values
  obtain ⟨next, env, s', ha, ex₂, hh₂, he₂, hc₂, hs₂⟩ :=
    allocDecls_typed f.results.toList hh₁ he₁ hft.2.2.1
  have hdecl : EnvTyped next (declareMany [] (f.args.toList ++ f.results.toList)) env := by
    simpa [declareMany_append] using he₂
  obtain ⟨locs, hpin, hroots⟩ := pinResultLocs_typed f.results.toList (by
    intro q hq
    exact hdecl.lookup q.id q.typ
      (declareMany_lookup_member [] _ hft.2.2.2.1 q (by simp [hq])))
  refine ⟨next, env, locs, s', ?_, ex₁.trans ex₂, hh₂,
    hdecl.initialContext hft.2.2.2.1, hroots, hc₁.trans hc₂, ?_, hft, hft.1.2.2⟩
  · simp [enterFrame, hfunctions, hf, harity, hdispatch, hb, ha, hpin,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [Array.length_toList] at hs₁ hs₂
    omega

theorem enterFramePick_typed {p : Program} {world s fid f args}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hf : findFunctionIn? p.funcs fid = some f)
    (values : ParamsValues world f.args.toList args) (ch : Choices) :
    ∃ next env locs s',
      enterFramePick s fid args ch = .ok (.ok (f, env, locs, s'), ch) ∧
      Extends world next ∧ HeapTyped next s' ∧
      EnvTyped next (initialContext f) env ∧ ResultRoots next f.results.toList locs ∧
      BooleanRuntime.SameContext s s' ∧
      s'.heap.size = s.heap.size + f.args.size + f.results.size ∧
      FunctionTyped p.funcs f ∧ f.wrapper = false := by
  obtain ⟨next, env, locs, s', he, ex, hh, henv, hr, hctx, hsize, hft, hw⟩ :=
    enterFrame_typed hp hc heap hf values
  exact ⟨next, env, locs, s', enterFramePick_ok he, ex, hh, henv, hr, hctx, hsize, hft, hw⟩

end GoLean.GoCore.RecoveryRuntime
