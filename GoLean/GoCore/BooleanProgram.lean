import GoLean.GoCore.BooleanInitialization
import GoLean.GoCore.BooleanSafety

/-! Scoped admission connected to actual setup, the structural runtime
invariant and sequential typed readout. No successful-run premise is used
for setup or generic safety; execution fuel remains explicit. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

/-- Scoped admission supplies the actual driver entry invariant for every
Boolean argument array. Setup fuel and choices remain arbitrary. -/
theorem setup_typed {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (env : LocalEnv) (s : ExecState) (locs : List Loc),
      findFunctionIn? p.funcs ⟨name⟩ = some f ∧ FunctionTyped f ∧
      runProgramSetupM fuel p name args ch =
        .ok (.exec f.body env (.frame [] [] [] [] .stop), s, locs, ch) ∧
      Inv (programState p) locs s (.exec f.body env (.frame [] [] [] [] .stop)) ∧
      locs.length = f.results.size := by
  obtain ⟨f, env, s, locs, hf, hsetup, hh, he, hn, hr, hl, hc, _⟩ :=
    setup_boolean h.1 fuel ch
  have ht := h.2 f (findFunction_mem hf)
  have hcover : Covers (initialContext f) env := Covers.of_names (by
    simpa [initialContext] using hn)
  exact ⟨f, env, s, locs, hf, ht, hsetup,
    ⟨hc, hh, hr, initial_control ht hcover he,
      booleanEntry_wf h.1.2.2 (findFunction_mem hf) hh he hc⟩, hl⟩

/-- The canonical initialized values and locations establish the same
invariant used for all-successor preservation and progress. -/
theorem setup_typed_exact_inv {p : Program} {name : String} {bs : List Bool}
    (h : TypedBooleanAdmission p name (bs.map GoValue.bool).toArray)
    (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧ FunctionTyped f ∧
      runProgramSetupM fuel p name (bs.map GoValue.bool).toArray ch =
        .ok (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop),
          initialState p f bs, initialResults f, ch) ∧
      Inv (programState p) (initialResults f) (initialState p f bs)
        (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop)) ∧
      bs.length = f.args.size := by
  obtain ⟨f, hf, ht, hs, hw, hh, he, hn, hr, hc, ha⟩ := setup_typed_exact h fuel ch
  have hcover : Covers (initialContext f) (initialEnv f) := Covers.of_names (by
    simpa [initialContext, initialNames] using hn)
  exact ⟨f, hf, ht, hs, ⟨hc, hh, hr, initial_control ht hcover he, hw⟩, ha⟩

/-- The actual sequential whole-program driver either reads Boolean results
at the declared arity, with empty output, or exhausts its supplied fuel.
This theorem gives no lower bound sufficient for termination. -/
theorem runProgram_typed {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ bs : List Bool, bs.length = f.results.size ∧
        runProgramM fuel p name args ch = .ok { values := (bs.map GoValue.bool).toArray }) ∨
       runProgramM fuel p name args ch = .error .fuelOut) := by
  obtain ⟨f, env, s, locs, hf, _, hs, hi, hl⟩ := setup_typed h fuel ch
  refine ⟨f, hf, ?_⟩
  rcases hi.run_ok_or_fuelOut fuel ch with ⟨t, ch', hr⟩ | hr
  · obtain ⟨bs, hb, hlen⟩ := hi.run_readout hr
    exact .inl ⟨bs, hlen.trans hl, by simp [runProgramM, hs, hr, hb,
      Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  · exact .inr (by simp [runProgramM, hs, hr, Bind.bind, Except.bind])

end GoLean.GoCore.BooleanRuntime
