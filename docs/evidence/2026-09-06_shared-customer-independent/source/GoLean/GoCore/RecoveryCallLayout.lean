import GoLean.GoCore.RecoveryCallEntry

/-! Exact argument/result allocation layout. These equations expose actual
machine allocation without requiring any hypothesis about future execution.
They do not transfer ownership of roots referenced by argument values. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

def callEnv (f : Func) (base : Nat) : LocalEnv :=
  BooleanRuntime.declareRoots [] base (BooleanRuntime.initialNames f)

def callResults (f : Func) (base : Nat) : List Loc :=
  (List.range f.results.size).map (fun i => .base ⟨base + f.args.size + i⟩)

def callCells (f : Func) (args zeros : List GoValue) : List HeapCell :=
  parameterCells f.args.toList args ++ parameterCells f.results.toList zeros

theorem callEnv_result {f : Func} (base : Nat) (hd : SignatureDistinct f)
    (i : Nat) (hi : i < f.results.size) :
    (callEnv f base).lookup f.results[i].id = some (.base ⟨base + f.args.size + i⟩) := by
  have h := BooleanRuntime.declareRoots_lookup [] base (BooleanRuntime.initialNames f)
    hd (f.args.size + i) (by simp [BooleanRuntime.initialNames]; omega)
  simpa [callEnv, BooleanRuntime.initialNames, List.getElem_append_right, hi, Nat.add_assoc] using h

theorem callEnv_pins {f : Func} (base : Nat) (hd : SignatureDistinct f) :
    pinResultLocs (callEnv f base) f.results.toList = .ok (callResults f base) := by
  apply BooleanRuntime.pinResultLocs_of_lookup
  intro i hi
  simpa using callEnv_result base hd i (by simpa using hi)

/-- Exact call allocation, independent of preexisting heap contents. The pure
argument schema alone does not establish liveness in the actual heap; that
is supplied separately by runtime typing or client pointee ownership. -/
theorem enterFrame_layout {p : Program} {world s fid f args zeros}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (hf : findFunctionIn? p.funcs fid = some f)
    (values : ParamsValues world f.args.toList args)
    (zeroValues : ZeroValues f.results.toList zeros) :
    enterFrame s fid args = .ok
      (f, callEnv f s.heap.size, callResults f s.heap.size,
        {s with heap := s.heap ++ (callCells f args zeros).toArray}) := by
  have hft := hp.2.2.1 f (BooleanRuntime.findFunction_mem hf)
  have harity : f.args.size = args.length := by simpa using values.length
  have hfunctions : s.functions = p.funcs := (congrArg ExecState.functions hc).symm
  have hfind : findFunctionIn? s.functions fid = some f := by simpa only [hfunctions] using hf
  have hmethods : s.methods = #[] :=
    (congrArg ExecState.methods hc).symm.trans (Array.eq_empty_of_size_eq_zero hp.2.1)
  have hdispatch : dynamicDispatch? s f args.toArray = .ok none := by
    simp [dynamicDispatch?, methodInfoByFuncId?, hmethods]
  have hb := bindParams_exact values [] s
  have ha := allocDecls_exact zeroValues
    (BooleanRuntime.declareRoots [] s.heap.size (f.args.toList.map Param.id))
    {s with heap := s.heap ++ (parameterCells f.args.toList args).toArray}
  have ha' : allocDecls
      (BooleanRuntime.declareRoots [] s.heap.size (f.args.toList.map Param.id))
      {s with heap := s.heap ++ (parameterCells f.args.toList args).toArray}
      f.results.toList = .ok (callEnv f s.heap.size,
        {s with heap := s.heap ++ (callCells f args zeros).toArray}) := by
    simpa [callEnv, callCells, BooleanRuntime.initialNames, List.map_append,
      BooleanRuntime.declareRoots_append, parameterCells_length values,
      Array.append_assoc, List.append_toArray] using ha
  simp [enterFrame, hfind, harity, hdispatch, hb, ha',
    callEnv_pins _ hft.2.2.2.1, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem enterFramePick_layout {p : Program} {world s fid f args zeros}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (hf : findFunctionIn? p.funcs fid = some f)
    (values : ParamsValues world f.args.toList args)
    (zeroValues : ZeroValues f.results.toList zeros) (ch : Choices) :
    enterFramePick s fid args ch = .ok (.ok
      (f, callEnv f s.heap.size, callResults f s.heap.size,
        {s with heap := s.heap ++ (callCells f args zeros).toArray}), ch) :=
  enterFramePick_ok (enterFrame_layout hp hc hf values zeroValues)

/-- Instantiate the generic admitted setup with a selected entry and its
independent zero-value vector. The same layout vocabulary serves the actual
program entry and subsequent calls. -/
theorem setup_layout {p : Program} {name : String} {args : Array GoValue} {f zeros}
    (h : RecoveryAdmission p name args)
    (hf : findFunctionIn? p.funcs ⟨name⟩ = some f)
    (hz : ZeroValues f.results.toList zeros) (fuel : Nat) (ch : Choices) :
    runProgramSetupM fuel p name args ch =
      .ok (.exec f.body (callEnv f 0) (.frame [] [] [] [] .stop false),
        {BooleanRuntime.programState p with heap := (callCells f args.toList zeros).toArray},
        callResults f 0, ch) := by
  obtain ⟨f', zs, world, hf', _, hz', run, _⟩ := setup_typed h fuel ch
  have he := Option.some.inj (hf'.symm.trans hf)
  subst f'
  have he := hz'.unique hz
  subst zs
  simpa [callEnv, callCells, callResults, initialState,
    BooleanRuntime.initialEnv, BooleanRuntime.initialResults] using run

end GoLean.GoCore.RecoveryRuntime
