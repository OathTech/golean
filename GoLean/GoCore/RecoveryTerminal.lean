import GoLean.GoCore.RecoveryObservation
import GoLean.GoCore.RecoveryChoices
import GoLean.GoCore.StringPanic

/-! Unconditional bounded driver classification for the admitted recovery
profile, over the `repanicCollapse` tape and the D5 refusal (landing chunk
L3, `docs/2026-09-07_land-panic-text-tape.md` §3; the sprint's
`RecoveryTerminal` of `7bd32ad6`, RESTATED). Every run of an invariant
state is: a typed normal completion, a `panic` terminal whose text is the
string MEMBER the stream's pick selects, the NAMED refusal of a string
payload whose first line is not valid UTF-8, or fuel exhaustion. The
refusal disjunct is what the sprint's "no refusal" theorems hid behind a
total renderer: an admitted recovery program with an invalid-UTF-8 literal
DOES refuse, by name (`Inv.run_refusal_named`) — the theorem says so instead
of proving it away. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine RecoveryTyping

/-- The classification of every run of an invariant state, for every fuel
and every original stream. The panic disjunct exposes the collapse bit the
STREAM selects at the abort (`collapseBit … (abortConsult …).1`) — on the
`repanicProgram` shape it is genuinely two-valued (`Tests/RecoveryTerminal`).
No successful-run premise or caller-supplied terminal metadata is required. -/
theorem Inv.run_classified {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) :
    (∃ final, runConfig fuel s c ch = .ok (final, ch)) ∨
    (∃ bytes recovered collapsed msg, stringPanicHead bytes recovered collapsed = some msg ∧
      runConfig fuel s c ch = .error (.panic msg)) ∨
    (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      runConfig fuel s c ch = .error (.unsupported (abortRefusal t first))) ∨
    runConfig fuel s c ch = .error .fuelOut := by
  induction fuel generalizing s c with
  | zero =>
    by_cases hn : c = .next .stop
    · subst c; exact .inl ⟨s, rfl⟩
    · obtain ⟨world, heap, control, pins⟩ := inv.typed
      exact .inr (.inr (.inr (control.runConfig_zero hn s ch)))
  | succ fuel ih =>
    obtain ⟨world, heap, control, pins⟩ := inv.typed
    rcases control_progress inv.program inv.sameContext heap control with rfl | abort | advance
    · exact .inl ⟨s, rfl⟩
    · obtain ⟨first, rest, rfl⟩ := abort
      have typed := control.abort_chain rfl
      obtain ⟨bytes, value⟩ := typed.2 first (by simp)
      cases hm : stringPanicHead bytes first.recovered
          (collapseBit first rest (abortConsult first rest ch).1) with
      | some msg =>
        exact .inr (.inl ⟨bytes, first.recovered, _, msg, hm,
          runConfig_string_abort fuel s _ ch first rest bytes msg rfl value hm⟩)
      | none =>
        refine .inr (.inr (.inl ⟨s, first, bytes, value, ?_,
          runConfig_string_abort_refused fuel s _ ch first rest bytes rfl value hm⟩))
        have := (stringPanicHead_none_iff bytes first.recovered
          (collapseBit first rest (abortConsult first rest ch).1)).mp hm
        simp [stringFirstLine?, this]
    · obtain ⟨nextWorld, next, t, step, ext, nextControl⟩ := advance ch
      have run : runConfig (fuel + 1) s c ch = runConfig fuel t next ch := by
        rw [BooleanRuntime.runConfig_eq_loop, execStmtLoop_step step,
          ← BooleanRuntime.runConfig_eq_loop]
      simpa only [run] using ih (inv.step (stepFn_sound step))

/-- The ONLY refusal an admitted recovery program's run can reach is the
named invalid-first-line abort refusal (D5): every other `Refusal` is
excluded, and the one that remains carries its cause. -/
theorem Inv.run_refusal_named {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) (reason : Refusal)
    (run : runConfig fuel s c ch = .error (.refusal reason)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      reason = .unsupported (abortRefusal t first) := by
  rcases inv.run_classified fuel ch with ⟨final, h⟩ | ⟨_, _, _, _, _, h⟩
    | ⟨t, first, bytes, hv, hnone, h⟩ | h <;> rw [h] at run
  · cases run
  · cases run
  · exact ⟨t, first, bytes, hv, hnone, (Stop.refusal.inj (Except.error.inj run)).symm⟩
  · cases run

/-- A computed record's terminal text is the member the reached abort's
stream pick selects — for the record's whole head bytes and recovered flag. -/
theorem Inv.observed_abort_member {p ps roots fuel s c ch result record}
    (inv : Inv p ps roots s c)
    (observed : runConfigWithAbort fuel s c ch = (result, some record)) :
    ∃ collapsed msg, stringPanicHead record.bytes record.recovered collapsed = some msg ∧
      result = .error (.panic msg) := by
  obtain ⟨n, t, terminal, residual, message, first, rest, _, _, _, query,
    _, value, recovered, _, step, result⟩ := inv.observed_abort observed
  rw [stepFn_abort query] at step
  have hok : abortMsg t first rest (abortConsult first rest residual).1 = .ok message := by
    cases hm : abortMsg t first rest (abortConsult first rest residual).1 with
    | error e =>
      -- The render's only error is the named `.unsupported` refusal, never
      -- a `panic` terminal.
      rw [hm] at step
      simp only [Bind.bind, Except.bind, Except.error.injEq] at step
      have he : e = .unsupported (abortRefusal t first) := by
        unfold abortMsg at hm
        split at hm
        · cases hm
        · exact (Except.error.inj hm).symm
      rw [he] at step
      exact (Stop.panic_ne_unsupported.mp step.symm).elim
    | ok m =>
      rw [hm] at step
      simp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        Except.error.injEq, Stop.panic_inj] at step
      rw [step]
  have member := abortMsg_string_ok t first rest record.bytes _ message value hok
  rw [recovered] at member
  exact ⟨_, message, member, result⟩

/-- The actual whole-program driver obtains its initial invariant from
admission and reads the actual external result pins on normal termination;
its other outcomes are the member panic, the named refusal, or exhaustion. -/
theorem runProgram_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramM fuel p name args ch =
          .ok {values := values.toArray, output := GoString.empty}) ∨
       (∃ bytes recovered collapsed msg, stringPanicHead bytes recovered collapsed = some msg ∧
          runProgramM fuel p name args ch = .error (.panic msg)) ∨
       (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
          first.value = .interface .string (.string bytes) ∧
          stringFirstLine? bytes.bytes = none ∧
          runProgramM fuel p name args ch = .error (.unsupported (abortRefusal t first))) ∨
       runProgramM fuel p name args ch = .error .fuelOut) := by
  obtain ⟨f, zeros, find, zero, setup, inv⟩ := setup_inv admitted fuel ch
  refine ⟨f, find, ?_⟩
  rcases inv.run_classified fuel ch with ⟨final, run⟩ | ⟨bytes, recovered, collapsed, msg, hm, run⟩
    | ⟨t, first, bytes, hv, hnone, run⟩ | run
  · obtain ⟨world, values, load, typed, length⟩ := inv.run_readout run
    exact .inl ⟨world, values, typed, by simpa using typed.length.symm,
      by simp [runProgramM, setup, run, load, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  · exact .inr (.inl ⟨bytes, recovered, collapsed, msg, hm,
      by simp [runProgramM, setup, run, Bind.bind, Except.bind]⟩)
  · exact .inr (.inr (.inl ⟨t, first, bytes, hv, hnone,
      by simp [runProgramM, setup, run, Bind.bind, Except.bind]⟩))
  · exact .inr (.inr (.inr (by simp [runProgramM, setup, run, Bind.bind, Except.bind])))

/-- The SHIPPED pool entry has only typed readout, the member panic, the
named refusal, or fuel exhaustion. Every alternative has proved empty output. -/
theorem runProgramPool_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramPoolOutM fuel p name args ch =
          .ok {values := values.toArray, output := GoString.empty}) ∨
       (∃ bytes recovered collapsed msg, stringPanicHead bytes recovered collapsed = some msg ∧
          runProgramPoolOutM fuel p name args ch = .error (.panic msg, GoString.empty)) ∨
       (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
          first.value = .interface .string (.string bytes) ∧
          stringFirstLine? bytes.bytes = none ∧
          runProgramPoolOutM fuel p name args ch =
            .error (.unsupported (abortRefusal t first), GoString.empty)) ∨
       runProgramPoolOutM fuel p name args ch = .error (.fuelOut, GoString.empty)) := by
  obtain ⟨f, find, outcome⟩ := runProgram_typed admitted fuel ch
  refine ⟨f, find, ?_⟩
  rw [runProgramPool_eq_sequential admitted]
  rcases outcome with ⟨world, values, typed, length, run⟩ | ⟨bytes, recovered, collapsed, msg, hm, run⟩
    | ⟨t, first, bytes, hv, hnone, run⟩ | run
  · exact .inl ⟨world, values, typed, length, by rw [run]; rfl⟩
  · exact .inr (.inl ⟨bytes, recovered, collapsed, msg, hm, by rw [run]; rfl⟩)
  · exact .inr (.inr (.inl ⟨t, first, bytes, hv, hnone, by rw [run]; rfl⟩))
  · exact .inr (.inr (.inr (by rw [run]; rfl)))

/-- The pool driver's only refusal on an admitted program is the named
invalid-first-line abort refusal. -/
theorem runProgramPool_refusal_named {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString)
    (run : runProgramPoolOutM fuel p name args ch = .error (.refusal reason, out)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      reason = .unsupported (abortRefusal t first) ∧ out = GoString.empty := by
  obtain ⟨_, _, outcome⟩ := runProgramPool_typed admitted fuel ch
  rcases outcome with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨t, first, bytes, hv, hnone, h⟩ | h <;>
    rw [h] at run
  · cases run
  · cases run
  · obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.error.inj run)
    exact ⟨t, first, bytes, hv, hnone, (Stop.refusal.inj h1).symm, h2.symm⟩
  · cases run

theorem runProgram_refusal_named {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices)
    (reason : Refusal)
    (run : runProgramM fuel p name args ch = .error (.refusal reason)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      reason = .unsupported (abortRefusal t first) := by
  obtain ⟨_, _, outcome⟩ := runProgram_typed admitted fuel ch
  rcases outcome with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨t, first, bytes, hv, hnone, h⟩ | h <;>
    rw [h] at run
  · cases run
  · cases run
  · exact ⟨t, first, bytes, hv, hnone, (Stop.refusal.inj (Except.error.inj run)).symm⟩
  · cases run

end GoLean.GoCore.RecoveryRuntime
