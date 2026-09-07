import GoLean.GoCore.RecoveryObservation
import GoLean.GoCore.RecoveryChoices
import GoLean.GoCore.StringPanic

/-! Unconditional bounded driver classification for the admitted recovery
profile, over the `repanicCollapse` tape and the D5 refusal (landing chunk
L3, `docs/2026-09-07_land-panic-text-tape.md` §3; the sprint's
`RecoveryTerminal` of `7bd32ad6`, RESTATED). Every run of an invariant
state is: a typed normal completion, a `panic` terminal whose text is the
string MEMBER at the collapse bit the stream's pick selects ON THE REACHED
ABORT'S CHAIN, the NAMED refusal of a string payload whose first line is not
valid UTF-8, or fuel exhaustion. The refusal disjunct is what the sprint's
"no refusal" theorems hid behind a total renderer: an admitted recovery
program with an invalid-UTF-8 literal DOES refuse, by name
(`Inv.run_refusal_named`) — the theorem says so instead of proving it away.

Audit fix round 2026-09-07 (R7, [AGENT]): the panic disjunct used to bind
`bytes`/`recovered`/`collapsed`/`msg` existentially with nothing anchoring
`bytes` to the payload or `collapsed` to the stream's pick (with
`recovered := false` it reduced to "msg has no LF"). It is now anchored
through the computed observer's RECORD: `runConfigWithAbort` returns the
record of the reached abort configuration (its provenance witness
`Inv.observed_abort` ties `record.bytes`/`record.chain` to that
configuration's chain and the residual stream to the original `ch`), and the
member is `stringPanicHead record.bytes record.recovered (collapseBit first
rest (abortConsult first rest ch).1)` for `first :: rest = record.chain`. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine RecoveryTyping

/-- A computed record's terminal text is the member the reached abort's
STREAM pick selects, on the RECORD's own chain: `first :: rest = record.chain`
are the reached abort configuration's entries (`Inv.observed_abort`), the
head's bytes and recovered flag are the record's, and the collapse bit is
the one the ORIGINAL stream `ch` selects — the profile's steps retain the
stream verbatim, so the residual at the abort IS `ch`
(`Inv.trace_choices`). -/
theorem Inv.observed_abort_member {p ps roots fuel s c ch result record}
    (inv : Inv p ps roots s c)
    (observed : runConfigWithAbort fuel s c ch = (result, some record)) :
    ∃ (first : PanicEntry) (rest : List PanicEntry) (msg : String),
      first :: rest = record.chain ∧
      stringPanicHead record.bytes record.recovered
        (collapseBit first rest (abortConsult first rest ch).1) = some msg ∧
      result = .error (.panic msg) := by
  obtain ⟨n, t, terminal, residual, message, first, rest, _, _, hres, query,
    _, value, recovered, chain, step, result⟩ := inv.observed_abort observed
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
  rw [recovered, hres] at member
  exact ⟨first, rest, message, chain, member, result⟩

/-- The SHAPE of every run (the induction): normal, some `panic` terminal,
the named refusal, or exhaustion. The panic disjunct is anchored by
`Inv.run_classified` below through the computed record; this lemma only
carries the induction. -/
theorem Inv.run_outcomes {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) :
    (∃ final, runConfig fuel s c ch = .ok (final, ch)) ∨
    (∃ msg, runConfig fuel s c ch = .error (.panic msg)) ∨
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
        exact .inr (.inl ⟨msg, runConfig_string_abort fuel s _ ch first rest bytes msg rfl value hm⟩)
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

/-- The classification of every run of an invariant state, for every fuel
and every original stream. The panic disjunct is ANCHORED: the computed
observer (`runConfigWithAbort`, which erases to `runConfig`) returns the
RECORD of the reached abort, and the terminal text is the string member for
the record's head bytes and recovered flag at the collapse bit the STREAM
selects on the record's chain (`collapseBit first rest (abortConsult first
rest ch).1`, `first :: rest = record.chain`) — on the `repanicProgram` shape
it is genuinely two-valued (`Tests/RecoveryTerminal`). No successful-run
premise or caller-supplied terminal metadata is required. -/
theorem Inv.run_classified {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) :
    (∃ final, runConfig fuel s c ch = .ok (final, ch)) ∨
    (∃ (record : AbortRecord) (first : PanicEntry) (rest : List PanicEntry) (msg : String),
      runConfigWithAbort fuel s c ch = (.error (.panic msg), some record) ∧
      first :: rest = record.chain ∧
      stringPanicHead record.bytes record.recovered
        (collapseBit first rest (abortConsult first rest ch).1) = some msg ∧
      runConfig fuel s c ch = .error (.panic msg)) ∨
    (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      runConfig fuel s c ch = .error (.unsupported (abortRefusal t first))) ∨
    runConfig fuel s c ch = .error .fuelOut := by
  rcases inv.run_outcomes fuel ch with h | ⟨msg, run⟩ | h | h
  · exact .inl h
  · obtain ⟨record, observed⟩ := inv.observation_complete run
    obtain ⟨first, rest, msg', chain, member, hres⟩ := inv.observed_abort_member observed
    have hmsg : msg' = msg := by simpa using hres.symm
    subst hmsg
    exact .inr (.inl ⟨record, first, rest, msg', observed, chain, member, run⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

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
  rcases inv.run_classified fuel ch with ⟨final, h⟩ | ⟨_, _, _, _, _, _, _, h⟩
    | ⟨t, first, bytes, hv, hnone, h⟩ | h <;> rw [h] at run
  · cases run
  · cases run
  · exact ⟨t, first, bytes, hv, hnone, (Stop.refusal.inj (Except.error.inj run)).symm⟩
  · cases run

/-- The actual whole-program driver obtains its initial invariant from
admission and reads the actual external result pins on normal termination;
its other outcomes are the member panic — anchored to the driver's OWN setup
(`runProgramSetupM`) and the record the computed observer returns from that
setup, at the stream's pick on the record's chain — the named refusal, or
exhaustion. -/
theorem runProgram_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramM fuel p name args ch =
          .ok {values := values.toArray, output := GoString.empty}) ∨
       (∃ (c : Config) (s : ExecState) (locs : List Loc) (record : AbortRecord)
          (first : PanicEntry) (rest : List PanicEntry) (msg : String),
          runProgramSetupM fuel p name args ch = .ok (c, s, locs, ch) ∧
          runConfigWithAbort fuel s c ch = (.error (.panic msg), some record) ∧
          first :: rest = record.chain ∧
          stringPanicHead record.bytes record.recovered
            (collapseBit first rest (abortConsult first rest ch).1) = some msg ∧
          runProgramM fuel p name args ch = .error (.panic msg)) ∨
       (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
          first.value = .interface .string (.string bytes) ∧
          stringFirstLine? bytes.bytes = none ∧
          runProgramM fuel p name args ch = .error (.unsupported (abortRefusal t first))) ∨
       runProgramM fuel p name args ch = .error .fuelOut) := by
  obtain ⟨f, zeros, find, zero, setup, inv⟩ := setup_inv admitted fuel ch
  refine ⟨f, find, ?_⟩
  rcases inv.run_classified fuel ch with ⟨final, run⟩
    | ⟨record, first, rest, msg, observed, chain, member, run⟩
    | ⟨t, first, bytes, hv, hnone, run⟩ | run
  · obtain ⟨world, values, load, typed, length⟩ := inv.run_readout run
    exact .inl ⟨world, values, typed, by simpa using typed.length.symm,
      by simp [runProgramM, setup, run, load, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  · exact .inr (.inl ⟨_, _, _, record, first, rest, msg, setup, observed, chain, member,
      by simp [runProgramM, setup, run, Bind.bind, Except.bind]⟩)
  · exact .inr (.inr (.inl ⟨t, first, bytes, hv, hnone,
      by simp [runProgramM, setup, run, Bind.bind, Except.bind]⟩))
  · exact .inr (.inr (.inr (by simp [runProgramM, setup, run, Bind.bind, Except.bind])))

/-- The SHIPPED pool entry has only typed readout, the member panic (anchored
exactly as `runProgram_typed`'s), the named refusal, or fuel exhaustion.
Every alternative has proved empty output. -/
theorem runProgramPool_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramPoolOutM fuel p name args ch =
          .ok {values := values.toArray, output := GoString.empty}) ∨
       (∃ (c : Config) (s : ExecState) (locs : List Loc) (record : AbortRecord)
          (first : PanicEntry) (rest : List PanicEntry) (msg : String),
          runProgramSetupM fuel p name args ch = .ok (c, s, locs, ch) ∧
          runConfigWithAbort fuel s c ch = (.error (.panic msg), some record) ∧
          first :: rest = record.chain ∧
          stringPanicHead record.bytes record.recovered
            (collapseBit first rest (abortConsult first rest ch).1) = some msg ∧
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
  rcases outcome with ⟨world, values, typed, length, run⟩
    | ⟨c, s, locs, record, first, rest, msg, setup, observed, chain, member, run⟩
    | ⟨t, first, bytes, hv, hnone, run⟩ | run
  · exact .inl ⟨world, values, typed, length, by rw [run]; rfl⟩
  · exact .inr (.inl ⟨c, s, locs, record, first, rest, msg, setup, observed, chain, member,
      by rw [run]; rfl⟩)
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
  rcases outcome with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩
    | ⟨t, first, bytes, hv, hnone, h⟩ | h <;>
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
  rcases outcome with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩
    | ⟨t, first, bytes, hv, hnone, h⟩ | h <;>
    rw [h] at run
  · cases run
  · cases run
  · exact ⟨t, first, bytes, hv, hnone, (Stop.refusal.inj (Except.error.inj run)).symm⟩
  · cases run

end GoLean.GoCore.RecoveryRuntime
