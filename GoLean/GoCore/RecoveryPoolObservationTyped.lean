import GoLean.GoCore.RecoveryTerminal
import GoLean.GoCore.RecoveryProgramObservation

/-! Typed completeness for the computed actual-pool observer, and generic
member correctness for every emitted record, including broader subjects. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine RecoveryTyping
open GoLean.Semantics

/-- The checked actual abort transition determines the exact member from
the complete head bytes and recovered flag; no typing premise is needed. -/
theorem stepAbortRecord?_member {before after event message record}
    (h : stepAbortRecord? before after event message = some record) :
    message = stringPanicHead record.bytes record.recovered := by
  obtain ⟨c, flag, first, rest, _, _, _, query, chain, render⟩ := stepAbortRecord?_some h
  have head : first = (AbortHead.mk record.bytes record.recovered).entry := (List.cons.inj chain).1
  have value : first.value = .interface .string (.string record.bytes) := by rw [head]; rfl
  have member := abortMsg_string before.shared first rest record.bytes value
  rw [show first.recovered = record.recovered from congrArg PanicEntry.recovered head] at member
  exact Except.ok.inj (render.symm.trans member)

theorem PoolAbortWitness.string_member {fuel m r ch out result record}
    (witness : PoolAbortWitness fuel m r ch out result record) :
    ∃ finalOut, result = (finalOut, .error (.panic (stringPanicHead record.bytes record.recovered))) := by
  obtain ⟨spent, remaining, before, beforeRace, beforeCh, beforeOut, next,
    after, afterCh, event, afterRace, finalOut, message,
    _, _, _, _, _, metadata, _, result⟩ := witness.reached
  exact ⟨finalOut, by simpa only [stepAbortRecord?_member metadata] using result⟩

theorem runProgramPoolWithAbort_member {fuel p name args ch result record}
    (observed : runProgramPoolWithAbort fuel p name args ch = (result, some record)) :
    ∃ out, result = .error (.panic (stringPanicHead record.bytes record.recovered), out) := by
  obtain ⟨c, s, locs, initial, out, message, _, witness, result⟩ :=
    runProgramPoolWithAbort_witness observed
  obtain ⟨out', h⟩ := witness.string_member
  have message_eq : message = stringPanicHead record.bytes record.recovered := by simpa using (Prod.mk.inj h).2
  exact ⟨out, by simpa only [message_eq] using result⟩

theorem Control.singleton_front {world fs c} (control : Control world fs c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    Pool.front ⟨#[.running c none], s, 0⟩ ch = .ok (.inr ch) := by
  have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
    (fun ht => hn (control.terminal_iff.mp ht))
  have hrun : threadRunnable s (.running c none) = true := by
    simp [threadRunnable, hd, control.not_blocked]
  simp [Pool.front, control.main_outcome hn, runnableIdxs_singleton hrun, MultiConfig.panicMsg?]

theorem singleton_observer_string_abort (fuel : Nat) (s : ExecState)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (value : first.value = .interface .string (.string bytes))
    (ch : Choices) (rs : RaceState) (out : GoString) :
    execPoolWithAbort (fuel + 1)
      ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ rs ch out =
      ((out, .error (.panic (stringPanicHead bytes first.recovered))),
        abortRecord? (.panicking (first :: rest) .stop)) := by
  have front : Pool.front ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ ch =
      .ok (.inr ch) := rfl
  have step := singleton_abort_step s first rest ch
  rw [abortMsg_string s first rest bytes value] at step
  simp only [Except.map] at step
  rw [execPoolWithAbort, front]
  dsimp only
  rw [step]
  simp only [raceUpdate_single, List.foldl_nil]
  rw [execPoolWithAbort]
  change attachAbort _ _ _ ((out, .error (.panic (stringPanicHead bytes first.recovered))), none) = _
  simp [attachAbort, stepAbortRecord?, Config.abort?, abortMsg_string s first rest bytes value]

theorem Control.observer_zero {world fs c} (control : Control world fs c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    runConfigWithAbort 0 s c ch = (.error .fuelOut, none) := by
  cases control <;> try rfl
  case next hk =>
    cases hk with
    | stop => contradiction
    | stmt hk => cases hk <;> rfl
    | resume => rfl

theorem Control.observer_step {world fs c} (control : Control world fs c)
    {s ch next t} (step : stepFn s c ch = .ok (next, t, ch)) (fuel : Nat) :
    runConfigWithAbort (fuel + 1) s c ch = runConfigWithAbort fuel t next ch := by
  cases control <;> (first | simp [runConfigWithAbort, step] | skip)
  case next hk =>
    cases hk with
    | stop => simp [stepFn, throw, throwThe, MonadExceptOf.throw] at step
    | stmt hk => cases hk <;> simp [runConfigWithAbort, step]
    | resume => simp [runConfigWithAbort, step]

theorem attachAbort_private (before after : MultiConfig)
    (observed : Pool.Result × Option AbortRecord) :
    attachAbort before after ⟨0, .privateStep, [], []⟩ observed = observed := by
  obtain ⟨⟨out, result⟩, metadata⟩ := observed
  cases metadata with
  | some record => rfl
  | none =>
    cases result with
    | ok value => rfl
    | error e => cases e with
      | fuelOut => rfl
      | refusal reason => rfl
      | terminal term => cases term <;> rfl

/-- The typed singleton pool computes exactly the same reached record as
the sequential observer. The actual pool still supplies its own proven
provenance; this theorem additionally discharges metadata completeness. -/
theorem Inv.pool_observation_eq {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) (rs : RaceState) (out : GoString) :
    execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ rs ch out =
      ((out, (runConfigWithAbort fuel s c ch).1), (runConfigWithAbort fuel s c ch).2) := by
  induction fuel generalizing s c with
  | zero =>
    obtain ⟨world, heap, control, pins⟩ := inv.typed
    by_cases hn : c = .next .stop
    · subst c; rfl
    · rw [control.observer_zero hn, execPoolWithAbort, control.singleton_front hn]
  | succ fuel ih =>
    obtain ⟨world, heap, control, pins⟩ := inv.typed
    rcases control_progress inv.program inv.sameContext heap control with rfl | abort | advance
    · rfl
    · obtain ⟨first, rest, rfl⟩ := abort
      obtain ⟨bytes, value⟩ := (control.abort_chain rfl).2 first (by simp)
      rw [singleton_observer_string_abort fuel s first rest bytes value]
      simp [runConfigWithAbort,
        stepFn_string_abort s (.panicking (first :: rest) .stop) ch first rest bytes rfl value]
    · obtain ⟨nextWorld, next, t, step, ext, nextControl⟩ := advance ch
      have hn : c ≠ .next .stop := by intro he; subst c; simp [stepFn] at step
      have poolStep := control.singleton_step hn (stepFn_success_no_abort step) s ch
      rw [step] at poolStep
      simp only [Except.map] at poolStep
      rw [control.observer_step step, execPoolWithAbort, control.singleton_front hn]
      dsimp only
      rw [poolStep]
      simp only [raceUpdate_single, List.foldl_nil]
      rw [attachAbort_private, ih (inv.step (stepFn_sound step))]

theorem Inv.pool_observation_complete {p ps roots s c fuel ch rs out message}
    (inv : Inv p ps roots s c)
    (run : execProgLoopOut fuel ⟨#[.running c none], s, 0⟩ rs ch out =
      (out, .error (.panic message))) :
    ∃ record, execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ rs ch out =
      ((out, .error (.panic message)), some record) := by
  rw [inv.pool_eq_runConfig] at run
  have actual := (Prod.mk.inj run).2
  obtain ⟨record, metadata⟩ := inv.observation_complete actual
  exact ⟨record, by rw [inv.pool_observation_eq, metadata]⟩

theorem runConfigWithAbort_nonpanic {fuel s c ch result}
    (run : runConfig fuel s c ch = result)
    (hn : ∀ message, result ≠ .error (.panic message)) :
    runConfigWithAbort fuel s c ch = (result, none) := by
  generalize observed : runConfigWithAbort fuel s c ch = pair
  obtain ⟨actual, metadata⟩ := pair
  have erase := runConfigWithAbort_erasure fuel s c ch
  rw [observed, run] at erase
  dsimp only at erase
  subst actual
  cases metadata with
  | none => rfl
  | some record =>
    obtain ⟨_, _, _, _, message, _, _, _, _, hp⟩ := runConfigWithAbort_witness observed
    exact False.elim (hn message hp)

/-- Unconditional classification includes computed metadata on every typed
panic, and none on success or exhaustion. All records retain whole chains. -/
theorem Inv.observer_classified {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) :
    (∃ final, runConfigWithAbort fuel s c ch = (.ok (final, ch), none)) ∨
    (∃ record, runConfigWithAbort fuel s c ch =
      (.error (.panic (stringPanicHead record.bytes record.recovered)), some record)) ∨
    runConfigWithAbort fuel s c ch = (.error .fuelOut, none) := by
  rcases inv.run_classified fuel ch with ⟨final, run⟩ | ⟨bytes, recovered, run⟩ | run
  · exact .inl ⟨final, runConfigWithAbort_nonpanic run (by intro message; simp)⟩
  · obtain ⟨record, observed⟩ := inv.observation_complete run
    have member := inv.observed_abort_member observed
    exact .inr (.inl ⟨record, by simpa only [member] using observed⟩)
  · exact .inr (.inr (runConfigWithAbort_nonpanic run (by intro message; simp)))

theorem runProgramPoolWithAbort_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramPoolWithAbort fuel p name args ch =
          (.ok {values := values.toArray, output := GoString.empty}, none)) ∨
       (∃ record, runProgramPoolWithAbort fuel p name args ch =
          (.error (.panic (stringPanicHead record.bytes record.recovered), GoString.empty), some record)) ∨
       runProgramPoolWithAbort fuel p name args ch = (.error (.fuelOut, GoString.empty), none)) := by
  obtain ⟨f, zeros, find, zero, setup, inv⟩ := setup_inv admitted fuel ch
  refine ⟨f, find, ?_⟩
  rcases inv.observer_classified fuel ch with ⟨final, observed⟩ | ⟨record, observed⟩ | observed
  · have run : runConfig fuel (initialState p f args.toList zeros)
        (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop)) ch = .ok (final, ch) := by
      rw [← runConfigWithAbort_erasure, observed]
    obtain ⟨world, values, load, typed, length⟩ := inv.run_readout run
    exact .inl ⟨world, values, typed, by simpa using typed.length.symm, by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed, load]⟩
  · exact .inr (.inl ⟨record, by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed]⟩)
  · exact .inr (.inr (by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed]))

/-- Typed actual-program metadata is complete in both directions. The
message premise identifies an observed outcome, not a future-safety premise. -/
theorem runProgramPoolWithAbort_panic_iff {p : Program} {name : String}
    {args : Array GoValue} (admitted : RecoveryAdmission p name args)
    (fuel : Nat) (ch : Choices) (message : String) :
    runProgramPoolOutM fuel p name args ch = .error (.panic message, GoString.empty) ↔
      ∃ record, runProgramPoolWithAbort fuel p name args ch =
        (.error (.panic message, GoString.empty), some record) ∧
        message = stringPanicHead record.bytes record.recovered := by
  constructor
  · intro run
    obtain ⟨_, _, outcome⟩ := runProgramPoolWithAbort_typed admitted fuel ch
    have erase := runProgramPoolWithAbort_erasure fuel p name args ch
    rw [run] at erase
    rcases outcome with ⟨_, _, _, _, observed⟩ | ⟨record, observed⟩ | observed
    · rw [observed] at erase; simp at erase
    · rw [observed] at erase
      have message_eq : message = stringPanicHead record.bytes record.recovered := by
        simpa using erase.symm
      exact ⟨record, by simpa only [message_eq] using observed, message_eq⟩
    · rw [observed] at erase; simp at erase
  · rintro ⟨record, observed, _⟩
    rw [← runProgramPoolWithAbort_erasure, observed]

theorem runProgramPoolWithAbort_no_refusal {p : Program} {name : String}
    {args : Array GoValue} (admitted : RecoveryAdmission p name args)
    (fuel : Nat) (ch : Choices) (reason : Refusal) (out : GoString)
    (record : Option AbortRecord) :
    runProgramPoolWithAbort fuel p name args ch ≠ (.error (.refusal reason, out), record) := by
  intro observed
  apply runProgramPool_no_refusal admitted fuel ch reason out
  rw [← runProgramPoolWithAbort_erasure, observed]

end GoLean.GoCore.RecoveryRuntime
