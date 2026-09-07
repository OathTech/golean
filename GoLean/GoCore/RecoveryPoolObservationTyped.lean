import GoLean.GoCore.RecoveryTerminal
import GoLean.GoCore.RecoveryProgramObservation

/-! Typed completeness for the computed actual-pool observer, and generic
member correctness for every emitted record, over the `repanicCollapse`
tape (landing chunk L3; the sprint's `RecoveryPoolObservationTyped` of
`7bd32ad6`, RESTATED). Every member statement is indexed by the collapse
bit ON THE RECORD'S CHAIN (`first :: rest = record.chain`) at the pick the
abort EVENT recorded (`abortEventPick?`) — the observer re-derives the
rendered member from the event's own pick, never from a guess. Audit fix
round 2026-09-07 (R7, [AGENT]): the statements used to bind `collapsed`
existentially; now the bit is `collapseBit first rest pick` on the record's
own chain, so an unrecovered or unequal head forces it false. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine RecoveryTyping
open GoLean.Semantics

/-- The checked actual abort transition determines the member from the
complete head bytes, the recovered flag, the record's chain and the event's
recorded pick; no typing premise is needed. -/
theorem stepAbortRecord?_member {before after event message record}
    (h : stepAbortRecord? before after event message = some record) :
    ∃ (pick : Nat) (first : PanicEntry) (rest : List PanicEntry),
      abortEventPick? event = some pick ∧ first :: rest = record.chain ∧
      stringPanicHead record.bytes record.recovered (collapseBit first rest pick) = some message := by
  obtain ⟨c, flag, first, rest, pick, _, _, _, query, hpick, chain, render⟩ :=
    stepAbortRecord?_some h
  have head : first = (AbortHead.mk record.bytes record.recovered).entry := (List.cons.inj chain).1
  have value : first.value = .interface .string (.string record.bytes) := by rw [head]; rfl
  have member := abortMsg_string_ok before.shared first rest record.bytes pick message value render
  rw [show first.recovered = record.recovered from congrArg PanicEntry.recovered head] at member
  exact ⟨pick, first, rest, hpick, chain, member⟩

/-- The witnessed pool abort's text is the member on the record's chain at
the pick the witnessed abort EVENT recorded (`stepAbortRecord?_member`; the
event is inside the witness). -/
theorem PoolAbortWitness.string_member {fuel m r ch out result record}
    (witness : PoolAbortWitness fuel m r ch out result record) :
    ∃ finalOut pick first rest msg,
      first :: rest = record.chain ∧
      stringPanicHead record.bytes record.recovered (collapseBit first rest pick) = some msg ∧
      result = (finalOut, .error (.panic msg)) := by
  obtain ⟨spent, remaining, before, beforeRace, beforeCh, beforeOut, next,
    after, afterCh, event, afterRace, finalOut, message,
    _, _, _, _, _, metadata, _, result⟩ := witness.reached
  obtain ⟨pick, first, rest, _, chain, member⟩ := stepAbortRecord?_member metadata
  exact ⟨finalOut, pick, first, rest, message, chain, member, result⟩

theorem runProgramPoolWithAbort_member {fuel p name args ch result record}
    (observed : runProgramPoolWithAbort fuel p name args ch = (result, some record)) :
    ∃ out pick first rest msg,
      first :: rest = record.chain ∧
      stringPanicHead record.bytes record.recovered (collapseBit first rest pick) = some msg ∧
      result = .error (.panic msg, out) := by
  obtain ⟨c, s, locs, initial, out, message, _, witness, result⟩ :=
    runProgramPoolWithAbort_witness observed
  obtain ⟨out', pick, first, rest, msg, chain, member, h⟩ := witness.string_member
  obtain ⟨-, hmsg⟩ := Prod.mk.inj h
  have message_eq : message = msg := by simpa using hmsg
  exact ⟨out, pick, first, rest, msg, chain, member, by simpa only [message_eq] using result⟩

theorem Control.singleton_front {world fs c} (control : Control world fs c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    Pool.front ⟨#[.running c none], s, 0⟩ ch = .ok (.inr ch) := by
  have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
    (fun ht => hn (control.terminal_iff.mp ht))
  have hrun : threadRunnable s (.running c none) = true := by
    simp [threadRunnable, hd, control.not_blocked]
  simp [Pool.front, control.main_outcome hn, runnableIdxs_singleton hrun, MultiConfig.panicMsg?]

/-- The singleton pool observer at an abort frontier whose string head HAS a
member at the stream's pick: the member panic, and the record of the whole
chain — the record is re-derived from the event's own recorded pick. -/
theorem singleton_observer_string_abort (fuel : Nat) (s : ExecState)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString) (msg : String)
    (value : first.value = .interface .string (.string bytes))
    (ch : Choices) (rs : RaceState) (out : GoString)
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest ch).1) = some msg) :
    execPoolWithAbort (fuel + 1)
      ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ rs ch out =
      ((out, .error (.panic msg)), abortRecord? (.panicking (first :: rest) .stop)) := by
  have front : Pool.front ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ ch =
      .ok (.inr ch) := rfl
  have hpick : (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
      = (abortConsult first rest ch).1 := by
    unfold abortConsult
    rw [← Choices.consumeAtE_fst_snd]
  have hmsg : abortMsg s first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 = .ok msg := by
    rw [hpick]
    exact abortMsg_string s first rest bytes _ msg value hm
  have step := singleton_abort_step s first rest ch
  rw [hmsg] at step
  simp only [Except.map] at step
  rw [execPoolWithAbort, front]
  dsimp only
  rw [step]
  simp only [raceUpdate_single, List.foldl_nil]
  rw [execPoolWithAbort]
  change attachAbort _ _ _ ((out, .error (.panic msg)), none) = _
  simp only [attachAbort, stepAbortRecord?, Config.abort?, abortEventPick?_consumeAtE, hmsg,
    Array.getElem?_singleton, bne_self_eq_false, Bool.false_eq_true, reduceIte]

/-- …and at a frontier whose string head has NO member: the named refusal,
no record. -/
theorem singleton_observer_string_abort_refused (fuel : Nat) (s : ExecState)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (value : first.value = .interface .string (.string bytes))
    (ch : Choices) (rs : RaceState) (out : GoString)
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest ch).1) = none) :
    execPoolWithAbort (fuel + 1)
      ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ rs ch out =
      ((out, .error (.unsupported (abortRefusal s first))), none) := by
  have front : Pool.front ⟨#[.running (.panicking (first :: rest) .stop) none], s, 0⟩ ch =
      .ok (.inr ch) := rfl
  have hpick : (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
      = (abortConsult first rest ch).1 := by
    unfold abortConsult
    rw [← Choices.consumeAtE_fst_snd]
  have hmsg : abortMsg s first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
      = .error (.unsupported (abortRefusal s first)) := by
    rw [hpick]
    exact abortMsg_string_refused s first rest bytes _ value hm
  have step := singleton_abort_step s first rest ch
  rw [hmsg] at step
  simp only [Except.map] at step
  rw [execPoolWithAbort, front]
  dsimp only
  rw [step]

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
the sequential observer — on the member path AND on the refusal path. -/
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
      cases hm : stringPanicHead bytes first.recovered
          (collapseBit first rest (abortConsult first rest ch).1) with
      | some msg =>
        rw [singleton_observer_string_abort fuel s first rest bytes msg value ch rs out hm]
        simp [runConfigWithAbort,
          stepFn_string_abort s (.panicking (first :: rest) .stop) ch first rest bytes msg rfl value hm]
      | none =>
        rw [singleton_observer_string_abort_refused fuel s first rest bytes value ch rs out hm]
        simp [runConfigWithAbort,
          stepFn_string_abort_refused s (.panicking (first :: rest) .stop) ch first rest bytes rfl
            value hm]
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

/-- Unconditional classification with computed metadata on every typed
panic (the member at the collapse bit the STREAM selects on the record's
chain), and none on success, the named refusal or exhaustion. All records
retain whole chains. -/
theorem Inv.observer_classified {p ps roots s c} (inv : Inv p ps roots s c)
    (fuel : Nat) (ch : Choices) :
    (∃ final, runConfigWithAbort fuel s c ch = (.ok (final, ch), none)) ∨
    (∃ (record : AbortRecord) (first : PanicEntry) (rest : List PanicEntry) (msg : String),
      first :: rest = record.chain ∧
      stringPanicHead record.bytes record.recovered
        (collapseBit first rest (abortConsult first rest ch).1) = some msg ∧
      runConfigWithAbort fuel s c ch = (.error (.panic msg), some record)) ∨
    (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      runConfigWithAbort fuel s c ch = (.error (.unsupported (abortRefusal t first)), none)) ∨
    runConfigWithAbort fuel s c ch = (.error .fuelOut, none) := by
  rcases inv.run_classified fuel ch with ⟨final, run⟩
    | ⟨record, first, rest, msg, observed, chain, member, run⟩
    | ⟨t, first, bytes, hv, hnone, run⟩ | run
  · exact .inl ⟨final, runConfigWithAbort_nonpanic run (by intro message; simp)⟩
  · exact .inr (.inl ⟨record, first, rest, msg, chain, member, observed⟩)
  · exact .inr (.inr (.inl ⟨t, first, bytes, hv, hnone,
      runConfigWithAbort_nonpanic run (by intro message; simp)⟩))
  · exact .inr (.inr (.inr (runConfigWithAbort_nonpanic run (by intro message; simp))))

theorem runProgramPoolWithAbort_typed {p : Program} {name : String} {args : Array GoValue}
    (admitted : RecoveryAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ world values, ParamsValues world f.results.toList values ∧
        values.length = f.results.size ∧ runProgramPoolWithAbort fuel p name args ch =
          (.ok {values := values.toArray, output := GoString.empty}, none)) ∨
       (∃ (record : AbortRecord) (first : PanicEntry) (rest : List PanicEntry) (msg : String),
          first :: rest = record.chain ∧
          stringPanicHead record.bytes record.recovered
            (collapseBit first rest (abortConsult first rest ch).1) = some msg ∧
          runProgramPoolWithAbort fuel p name args ch =
            (.error (.panic msg, GoString.empty), some record)) ∨
       (∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
          first.value = .interface .string (.string bytes) ∧
          stringFirstLine? bytes.bytes = none ∧
          runProgramPoolWithAbort fuel p name args ch =
            (.error (.unsupported (abortRefusal t first), GoString.empty), none)) ∨
       runProgramPoolWithAbort fuel p name args ch = (.error (.fuelOut, GoString.empty), none)) := by
  obtain ⟨f, zeros, find, zero, setup, inv⟩ := setup_inv admitted fuel ch
  refine ⟨f, find, ?_⟩
  rcases inv.observer_classified fuel ch with ⟨final, observed⟩
    | ⟨record, first, rest, msg, chain, member, observed⟩
    | ⟨t, first, bytes, hv, hnone, observed⟩ | observed
  · have run : runConfig fuel (initialState p f args.toList zeros)
        (.exec f.body (BooleanRuntime.initialEnv f) (.frame [] [] [] [] .stop)) ch = .ok (final, ch) := by
      rw [← runConfigWithAbort_erasure, observed]
    obtain ⟨world, values, load, typed, length⟩ := inv.run_readout run
    exact .inl ⟨world, values, typed, by simpa using typed.length.symm, by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed, load]⟩
  · exact .inr (.inl ⟨record, first, rest, msg, chain, member, by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed]⟩)
  · exact .inr (.inr (.inl ⟨t, first, bytes, hv, hnone, by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed]⟩))
  · exact .inr (.inr (.inr (by
      simp [runProgramPoolWithAbort, setup, inv.pool_observation_eq, observed])))

/-- Typed actual-program metadata is complete in both directions: a panic
result has a record whose head bytes and flag render the message at the
collapse bit the stream selects on the record's chain, and a record's run
is that panic. -/
theorem runProgramPoolWithAbort_panic_iff {p : Program} {name : String}
    {args : Array GoValue} (admitted : RecoveryAdmission p name args)
    (fuel : Nat) (ch : Choices) (message : String) :
    runProgramPoolOutM fuel p name args ch = .error (.panic message, GoString.empty) ↔
      ∃ record, runProgramPoolWithAbort fuel p name args ch =
        (.error (.panic message, GoString.empty), some record) ∧
        ∃ (first : PanicEntry) (rest : List PanicEntry), first :: rest = record.chain ∧
          stringPanicHead record.bytes record.recovered
            (collapseBit first rest (abortConsult first rest ch).1) = some message := by
  constructor
  · intro run
    obtain ⟨_, _, outcome⟩ := runProgramPoolWithAbort_typed admitted fuel ch
    have erase := runProgramPoolWithAbort_erasure fuel p name args ch
    rw [run] at erase
    rcases outcome with ⟨_, _, _, _, observed⟩ | ⟨record, first, rest, msg, chain, member, observed⟩
      | ⟨_, _, _, _, _, observed⟩ | observed
    · rw [observed] at erase; simp at erase
    · rw [observed] at erase
      have message_eq : msg = message := by simpa using erase
      exact ⟨record, by simpa only [message_eq] using observed, first, rest, chain,
        by simpa only [message_eq] using member⟩
    · rw [observed] at erase; simp at erase
    · rw [observed] at erase; simp at erase
  · rintro ⟨record, observed, _⟩
    rw [← runProgramPoolWithAbort_erasure, observed]

/-- The observer's only refusal on an admitted program is the named
invalid-first-line abort refusal, with no record. -/
theorem runProgramPoolWithAbort_refusal_named {p : Program} {name : String}
    {args : Array GoValue} (admitted : RecoveryAdmission p name args)
    (fuel : Nat) (ch : Choices) (reason : Refusal) (out : GoString)
    (record : Option AbortRecord)
    (observed : runProgramPoolWithAbort fuel p name args ch = (.error (.refusal reason, out), record)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes : GoString),
      first.value = .interface .string (.string bytes) ∧
      stringFirstLine? bytes.bytes = none ∧
      reason = .unsupported (abortRefusal t first) ∧ out = GoString.empty ∧ record = none := by
  obtain ⟨_, _, outcome⟩ := runProgramPoolWithAbort_typed admitted fuel ch
  rcases outcome with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨t, first, bytes, hv, hnone, h⟩ | h <;>
    rw [h] at observed
  · cases observed
  · cases observed
  · obtain ⟨h1, h2⟩ := Prod.mk.inj observed
    obtain ⟨h3, h4⟩ := Prod.mk.inj (Except.error.inj h1)
    exact ⟨t, first, bytes, hv, hnone, (Stop.refusal.inj h3).symm, h4.symm, h2.symm⟩
  · cases observed

end GoLean.GoCore.RecoveryRuntime
