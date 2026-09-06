import GoLean.GoCore.RecoveryInitialization
import GoLean.GoCore.RecoveryResultRoots

/-! Actual recovery-profile entry. Admission constructs canonical parameter
and zero-result cells, a typed environment, and result pins for every setup
fuel and choice stream. Control preservation is a separate obligation. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

def initialState (p : Program) (f : Func) (args results : List GoValue) : ExecState :=
  { BooleanRuntime.programState p with
    heap := (parameterCells f.args.toList args ++
      parameterCells f.results.toList results).toArray }

/-- This is the existing driver's actual setup, including its well-formedness
guard, empty package-init path, allocation order and original choices.
The heap uses unbounded Lean arrays; no extra allocation-capacity premise is
hidden in this statement. The existing default platform is unchanged. -/
theorem setup_typed {p : Program} {name : String} {args : Array GoValue}
    (h : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (zeros : List GoValue) (world : World),
      findFunctionIn? p.funcs ⟨name⟩ = some f ∧ FunctionTyped p.funcs f ∧
      ZeroValues f.results.toList zeros ∧
      runProgramSetupM fuel p name args ch =
        .ok (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop),
          initialState p f args.toList zeros, BooleanRuntime.initialResults f, ch) ∧
      HeapTyped world (initialState p f args.toList zeros) ∧
      EnvTyped world (initialContext f) (BooleanRuntime.initialEnv f) ∧
      ResultRoots world f.results.toList (BooleanRuntime.initialResults f) ∧
      BooleanRuntime.SameContext (BooleanRuntime.programState p)
        (initialState p f args.toList zeros) ∧
      (initialState p f args.toList zeros).heap.size = args.size + f.results.size ∧
      f.args.size = args.size := by
  have hentry := h.2.1
  have hp := h.2.2
  cases hf : findFunctionIn? p.funcs ⟨name⟩ with
  | none => simp [Admission.Entry, hf] at hentry
  | some f =>
    have he : f.args.size = args.size ∧ Admission.BoolParams f.args ∧
        Admission.InitialArguments args := by simpa [Admission.Entry, hf] using hentry
    obtain ⟨harity, hargs, hvalues⟩ := he
    have ht := hp.2.2.1 f (BooleanRuntime.findFunction_mem hf)
    obtain ⟨bs, hbs⟩ := BooleanRuntime.initialArguments_bools hvalues
    have hlen : f.args.toList.length = bs.length := by
      have hh := congrArg List.length hbs
      simpa [harity] using hh
    have values : ParamsValues #[] f.args.toList args.toList := by
      rw [hbs]
      exact ParamsValues.booleans _ _ _ hargs hlen
    obtain ⟨zeros, hz⟩ := ZeroValues.exists f.results.toList ht.2.2.1
    obtain ⟨w₁, env₁, s₁, hb, ext₁, hh₁, he₁, hc₁, hs₁⟩ :=
      bindParams_typed (HeapTyped.empty (s := BooleanRuntime.programState p) rfl)
        (EnvTyped.empty #[]) values
    have hbe := Except.ok.inj (hb.symm.trans
      (bindParams_exact values [] (BooleanRuntime.programState p)))
    rcases Prod.mk.inj hbe with ⟨rfl, rfl⟩
    obtain ⟨world, env₂, s₂, ha, ext₂, hh₂, he₂, hc₂, hs₂⟩ :=
      allocDecls_typed f.results.toList hh₁ he₁ ht.2.2.1
    have hae : allocDecls
        (BooleanRuntime.declareRoots [] (BooleanRuntime.programState p).heap.size
          (f.args.toList.map Param.id))
        { BooleanRuntime.programState p with
          heap := (BooleanRuntime.programState p).heap ++
            (parameterCells f.args.toList args.toList).toArray }
        f.results.toList =
        .ok (BooleanRuntime.initialEnv f, initialState p f args.toList zeros) := by
      simpa [BooleanRuntime.initialEnv, BooleanRuntime.initialNames, initialState,
        BooleanRuntime.programState, BooleanRuntime.declareRoots_append,
        List.map_append, ← List.append_toArray, parameterCells_length values]
        using allocDecls_exact hz
          (BooleanRuntime.declareRoots [] 0 (f.args.toList.map Param.id))
          { BooleanRuntime.programState p with
            heap := (parameterCells f.args.toList args.toList).toArray }
    have hae' := Except.ok.inj (ha.symm.trans hae)
    rcases Prod.mk.inj hae' with ⟨rfl, rfl⟩
    have hdecl : EnvTyped world
        (declareMany [] (f.args.toList ++ f.results.toList)) (BooleanRuntime.initialEnv f) := by
      simpa [declareMany_append] using he₂
    have henv := hdecl.initialContext ht.2.2.2.1
    obtain ⟨locs, hpin, hroots⟩ := pinResultLocs_typed f.results.toList (by
      intro q hq
      exact hdecl.lookup q.id q.typ
        (declareMany_lookup_member [] _ ht.2.2.2.1 q (by simp [hq])))
    have hpinexact := BooleanRuntime.initialEnv_pins ht.2.2.2.1
    have hlocs := Except.ok.inj (hpin.symm.trans hpinexact)
    subst locs
    have hg : p.globals = #[] := Array.eq_empty_of_size_eq_zero hp.1
    have hreserved := BooleanRuntime.reservedPrefix_runtime h.1.1
    have hw := programState_wf hp
    have hinit := program_no_init hp
    have hseed := BooleanRuntime.seedGlobals_empty p
    dsimp only [BooleanRuntime.programState] at hseed hw hb
    simp only [BooleanRuntime.programState, Array.size_empty, Array.empty_append] at hae
    refine ⟨f, zeros, world, rfl, ht, hz, ?_, hh₂, henv, hroots, rfl, ?_, harity⟩
    · simp [runProgramSetupM, hf, harity, hreserved, hg, hseed, hw,
        runPkgInitM, hinit, hb, hae, hpinexact,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [initialState, parameterCells_length values,
        parameterCells_length (hz.typed world), harity]

end GoLean.GoCore.RecoveryRuntime
