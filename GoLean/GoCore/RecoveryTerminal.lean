import GoLean.GoCore.RecoveryObservation
import GoLean.GoCore.RecoveryChoices
import GoLean.GoCore.StringPanic

/-! Unconditional bounded driver classification for the admitted recovery
profile. Actual boxed-string readout makes panic a terminal outcome for all
bytes and recovery flags. Exhaustion stays distinct from terminal panic. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine RecoveryTyping

/-- For every fuel and original stream, the real sequential driver returns
a typed-domain state, an explicit string panic member, or fuel exhaustion.
No successful-run premise or caller-supplied terminal metadata is required. -/
theorem Inv.run_classified {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) :
    (∃ final, runConfig fuel s c ch = .ok (final, ch)) ∨
    (∃ bytes recovered, runConfig fuel s c ch =
      .error (.panic (stringPanicHead bytes recovered))) ∨
    runConfig fuel s c ch = .error .fuelOut := by
  induction fuel generalizing s c with
  | zero =>
    by_cases hn : c = .next .stop
    · subst c; exact .inl ⟨s, rfl⟩
    · obtain ⟨world, heap, control, pins⟩ := inv.typed
      exact .inr (.inr (control.runConfig_zero hn s ch))
  | succ fuel ih =>
    obtain ⟨world, heap, control, pins⟩ := inv.typed
    rcases control_progress inv.program inv.sameContext heap control with rfl | abort | advance
    · exact .inl ⟨s, rfl⟩
    · obtain ⟨first, rest, rfl⟩ := abort
      have typed := control.abort_chain rfl
      obtain ⟨bytes, value⟩ := typed.2 first (by simp)
      exact .inr (.inl ⟨bytes, first.recovered,
        runConfig_string_abort fuel s _ ch first rest bytes rfl value⟩)
    · obtain ⟨nextWorld, next, t, step, ext, nextControl⟩ := advance ch
      have run : runConfig (fuel + 1) s c ch = runConfig fuel t next ch := by
        rw [BooleanRuntime.runConfig_eq_loop, execStmtLoop_step step,
          ← BooleanRuntime.runConfig_eq_loop]
      simpa only [run] using ih (inv.step (stepFn_sound step))

theorem Inv.run_no_refusal {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) (reason : Refusal) :
    runConfig fuel s c ch ≠ .error (.refusal reason) := by
  rcases inv.run_classified fuel ch with ⟨final, run⟩ | ⟨bytes, recovered, run⟩ | run <;>
    rw [run] <;> simp

/-- A computed record's exact terminal member comes from the actual reached
abort query, including all bytes after LF and the actual recovered flag. -/
theorem Inv.observed_abort_member {p ps roots fuel s c ch result record}
    (inv : Inv p ps roots s c)
    (observed : runConfigWithAbort fuel s c ch = (result, some record)) :
    result = .error (.panic (stringPanicHead record.bytes record.recovered)) := by
  obtain ⟨n, t, terminal, residual, message, first, rest, _, _, _, query,
    _, value, recovered, _, step, result⟩ := inv.observed_abort observed
  have actual := stepFn_string_abort t terminal residual first rest record.bytes query value
  rw [recovered] at actual
  have he := step.symm.trans actual
  have message_eq : message = stringPanicHead record.bytes record.recovered := by simpa using he
  simpa only [message_eq] using result

/-- The actual whole-program driver obtains its initial invariant from
admission and reads the actual external result pins on normal termination. -/
theorem runProgram_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramM fuel p name args ch =
          .ok {values := values.toArray, output := GoString.empty}) ∨
       (∃ bytes recovered, runProgramM fuel p name args ch =
          .error (.panic (stringPanicHead bytes recovered))) ∨
       runProgramM fuel p name args ch = .error .fuelOut) := by
  obtain ⟨f, zeros, find, zero, setup, inv⟩ := setup_inv admitted fuel ch
  refine ⟨f, find, ?_⟩
  rcases inv.run_classified fuel ch with ⟨final, run⟩ | ⟨bytes, recovered, run⟩ | run
  · obtain ⟨world, values, load, typed, length⟩ := inv.run_readout run
    exact .inl ⟨world, values, typed, by simpa using typed.length.symm,
      by simp [runProgramM, setup, run, load, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  · exact .inr (.inl ⟨bytes, recovered, by simp [runProgramM, setup, run, Bind.bind, Except.bind]⟩)
  · exact .inr (.inr (by simp [runProgramM, setup, run, Bind.bind, Except.bind]))

/-- The SHIPPED pool entry has only typed readout, explicit string panic,
or fuel exhaustion. Every alternative has proved empty output. -/
theorem runProgramPool_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramPoolOutM fuel p name args ch =
          .ok {values := values.toArray, output := GoString.empty}) ∨
       (∃ bytes recovered, runProgramPoolOutM fuel p name args ch =
          .error (.panic (stringPanicHead bytes recovered), GoString.empty)) ∨
       runProgramPoolOutM fuel p name args ch = .error (.fuelOut, GoString.empty)) := by
  obtain ⟨f, find, outcome⟩ := runProgram_typed admitted fuel ch
  refine ⟨f, find, ?_⟩
  rw [runProgramPool_eq_sequential admitted]
  rcases outcome with ⟨world, values, typed, length, run⟩ | ⟨bytes, recovered, run⟩ | run
  · exact .inl ⟨world, values, typed, length, by rw [run]; rfl⟩
  · exact .inr (.inl ⟨bytes, recovered, by rw [run]; rfl⟩)
  · exact .inr (.inr (by rw [run]; rfl))

theorem runProgramPool_no_refusal {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) :
    runProgramPoolOutM fuel p name args ch ≠ .error (.refusal reason, out) := by
  obtain ⟨_, _, outcome⟩ := runProgramPool_typed admitted fuel ch
  rcases outcome with ⟨_, _, _, _, run⟩ | ⟨_, _, run⟩ | run <;> rw [run] <;> simp

theorem runProgram_no_refusal {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices)
    (reason : Refusal) :
    runProgramM fuel p name args ch ≠ .error (.refusal reason) := by
  obtain ⟨_, _, outcome⟩ := runProgram_typed admitted fuel ch
  rcases outcome with ⟨_, _, _, _, run⟩ | ⟨_, _, run⟩ | run <;> rw [run] <;> simp

end GoLean.GoCore.RecoveryRuntime
