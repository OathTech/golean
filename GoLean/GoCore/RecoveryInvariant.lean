import GoLean.GoCore.RecoveryPanicProgress

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem control_stepFn {p : Program} {world s c ch c' t ch'}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (control : Control world p.funcs c)
    (step : stepFn s c ch = .ok (c', t, ch')) :
    ∃ next, StoreExtension world next s t ∧ Control next p.funcs c' ∧ ch' = ch := by
  rcases control_progress hp hc heap control with rfl | ⟨first, rest, rfl⟩ | ha
  · exact False.elim (step_terminal_elim (stepFn_sound step))
  · exact False.elim (step_abort_elim (stepFn_sound step))
  · obtain ⟨next, d, u, run, ext, hd⟩ := ha ch
    rw [run] at step
    cases step
    exact ⟨next, ext, hd, rfl⟩

/-- Arbitrary relational successors preserve the structural typing. The
realizing stream comes from `step_complete`; uniform executable progress
then determines that successor, rather than selecting one allowed step. -/
theorem control_step {p : Program} {world s c c' t}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (control : Control world p.funcs c)
    (step : Step c s c' t) :
    ∃ next, StoreExtension world next s t ∧ Control next p.funcs c' := by
  obtain ⟨ch, ch', run⟩ := step_complete step
  obtain ⟨next, ext, control', _⟩ := control_stepFn hp hc heap control run
  exact ⟨next, ext, control'⟩

/-- The schema is existential and may grow on allocation. Every component
is structural: current static program, immutable context, actual typed
heap/environment/control, pinned result roots and address well-formedness. -/
structure Inv (p : Program) (ps : List Param) (results : List Loc)
    (s : ExecState) (c : Config) : Prop where
  program : ProgramTyped p
  sameContext : BooleanRuntime.SameContext (BooleanRuntime.programState p) s
  machineWf : MachineWf s c
  typed : ∃ world, HeapTyped world s ∧ Control world p.funcs c ∧ ResultRoots world ps results

theorem Inv.step {p ps results s c t c'} (h : Inv p ps results s c)
    (step : Step c s c' t) : Inv p ps results t c' := by
  obtain ⟨world, heap, control, roots⟩ := h.typed
  obtain ⟨next, ext, control'⟩ := control_step h.program h.sameContext heap control step
  exact ⟨h.program, h.sameContext.trans ext.context, step.preserves_wf h.machineWf,
    next, ext.heap, control', roots.mono ext.world⟩

theorem Inv.steps {p ps results s c t c'} (h : Inv p ps results s c)
    (steps : Steps c s c' t) : Inv p ps results t c' := by
  induction steps with
  | refl => exact h
  | tail _ step ih => exact ih.step step

theorem Inv.iter {p ps results s c t c' n ch ch'} (h : Inv p ps results s c)
    (run : stepFnIter n s c ch = .ok (c', t, ch')) : Inv p ps results t c' :=
  h.steps (stepFnIter_sound run)

theorem Inv.progress {p ps results s c} (h : Inv p ps results s c) :
    c = .next .stop ∨ (∃ first rest, c = .panicking (first :: rest) .stop) ∨
      ∃ c' t, Step c s c' t := by
  obtain ⟨world, heap, control, _⟩ := h.typed
  rcases control_progress h.program h.sameContext heap control with hn | ha | hs
  · exact .inl hn
  · exact .inr (.inl ha)
  · obtain ⟨_, c', t, run, _, _⟩ := hs []
    exact .inr (.inr ⟨c', t, stepFn_sound run⟩)

theorem Inv.reachable_progress {p ps results s c t c'} (h : Inv p ps results s c)
    (steps : Steps c s c' t) :
    c' = .next .stop ∨ (∃ first rest, c' = .panicking (first :: rest) .stop) ∨
      ∃ c'' u, Step c' t c'' u := (h.steps steps).progress

theorem Inv.readout {p ps results s c} (h : Inv p ps results s c) :
    ∃ world vs, loadMany s results = .ok vs ∧ ParamsValues world ps vs ∧
      vs.length = results.length := by
  obtain ⟨world, heap, _, roots⟩ := h.typed
  obtain ⟨vs, run, hv⟩ := roots.load heap
  exact ⟨world, vs, run, hv, hv.length.symm.trans roots.length⟩

theorem initial_control {world fs f env} (hf : FunctionTyped fs f)
    (he : EnvTyped world (initialContext f) env) :
    Control world fs (.exec f.body env (.frame [] [] [] [] .stop)) :=
  .execFrame he (.of_static hf.2.2.2.2.1)
    (.frame (EnvTyped.empty world) .nil .nil (by simp [DefersTyped]) .stop (by simp))

/-- Actual admitted setup establishes the invariant for all setup fuels and
choice streams. No invariant or future-success premise is supplied by the caller. -/
theorem setup_inv {p : Program} {name : String} {args : Array GoValue}
    (h : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f zeros,
      findFunctionIn? p.funcs ⟨name⟩ = some f ∧ ZeroValues f.results.toList zeros ∧
      runProgramSetupM fuel p name args ch =
        .ok (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop),
          initialState p f args.toList zeros, BooleanRuntime.initialResults f, ch) ∧
      Inv p f.results.toList (BooleanRuntime.initialResults f)
        (initialState p f args.toList zeros)
        (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop)) := by
  obtain ⟨f, zeros, world, hf, ht, hz, setup, wf, heap, env, roots, context, _, _⟩ :=
    setup_typed_wf h fuel ch
  exact ⟨f, zeros, hf, hz, setup,
    ⟨h.2.2, context, wf, world, heap, initial_control ht env, roots⟩⟩

end GoLean.GoCore.RecoveryRuntime
