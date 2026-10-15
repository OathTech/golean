import GoLean.GoCore.RelationalProgramOutcome
import GoLean.GoCore.RelationalLocalExecutionSound
import GoLean.GoCore.RelationalProgram

namespace GoLean.GoCore.Relational.ProgramExecution
open Machine

/-- The seeded-state check is represented at its actual position, but its
failure is unreachable after a successful empty-store seeding operation. -/
theorem Seeding.invalid_unreachable {program : Program} {s : Store}
    (h : seedGlobals ⟨program⟩ {} program.globals = .ok s) : StateWf ⟨program⟩ s :=
  SetupSound.seedGlobals_wf h

namespace Correspondence
open ExecutionStatement

def project : Outcome → Except Stop Readout
  | .ok values => .ok { values := values.toArray }
  | .error failure => .error failure.cause

def SegmentReplay (ctx : ProgramCtx) (seg : Segment) (ch tail : Choices) : Prop :=
  ∃ middle, ExecutionStatement.Prefix ctx seg.labels.length seg.start.store seg.start.control ch
    seg.labels seg.finish.store seg.finish.control middle ∧ replays seg.records middle tail

def OptionalReplay (ctx : ProgramCtx) : Option Segment → Choices → Choices → Prop
  | none, ch, tail => ch = tail
  | some seg, ch, tail => SegmentReplay ctx seg ch tail

def HistoryReplay (ctx : ProgramCtx) (history : History) (ch tail : Choices) : Prop :=
  ∃ middle, OptionalReplay ctx history.initialization ch middle ∧
    OptionalReplay ctx history.body middle tail

/-- Unrestricted coverage of the actual selected program result. The suffix
is a semantic witness only: even successful `Readout` does not return it. -/
def Coverage : Prop :=
  ∀ program name args fuel ch, ∃ history outcome tail,
    Execution program name args fuel history outcome ∧
    HistoryReplay ⟨program⟩ history ch tail ∧ runProgramM fuel program name args ch = project outcome

/-- Every admitted program execution realizes with arbitrary final suffix.
The same budget is supplied independently to initialization and body. -/
def Realization : Prop :=
  ∀ program name args fuel history outcome,
    Execution program name args fuel history outcome → ∀ tail,
    ∃ ch, HistoryReplay ⟨program⟩ history ch tail ∧ runProgramM fuel program name args ch = project outcome

def RefusalExclusion : Prop :=
  ∀ program name args, Avoids program name args Outcome.isRefusal → ∀ fuel ch reason,
    runProgramM fuel program name args ch ≠ .error (.refusal reason)

def FatalExclusion : Prop :=
  ∀ program name args, Avoids program name args Outcome.isFatal → ∀ fuel ch message,
    runProgramM fuel program name args ch ≠ .error (.terminal (.fatal message))


theorem initialization_projection (e : Stop) : initStop e = markInitPhase e := by
  cases e with
  | terminal t => cases t <;> rfl
  | refusal r => cases r <;> rfl
  | fuelOut => rfl



def forget {α : Type} : Result α → Except Stop α
  | .ok a => .ok a
  | .error e => .error e.cause

def validate (program : Program) (name : String) (args : Array GoValue) : Except Stop Func := do
  let f ← match findFunctionIn? program.funcs ⟨name⟩ with
    | none => throw (missingFunction name)
    | some f => pure f
  if f.args.size != args.size then throw (wrongArity f.args.size args.size)
  if program.typeDefs.hasReservedPrefix then pure f else throw (badTypeTable program)

def seed (program : Program) : Except Stop Store := do
  let s ← seedGlobals ⟨program⟩ {} program.globals
  if StateWf ⟨program⟩ s then pure s else throw badSeededState

def activate (ctx : ProgramCtx) (f : Func) (args : List GoValue) (s : Store) : Except Stop Activation := do
  let (env, t) ← bindParams ctx [] s f.args.toList args
  let (frameEnv, u) ← allocDecls ctx env t f.results.toList
  let results ← pinResultLocs frameEnv f.results.toList
  return ⟨frameEnv, u, results⟩

theorem validation_sound {program name args r} (h : Validation program name args r) :
    validate program name args = forget r := by
  cases h <;> simp_all [validate, forget, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, Bind.bind, Except.bind]

theorem validation_total (program : Program) (name : String) (args : Array GoValue) :
    ∃ r, Validation program name args r := by
  cases hf : findFunctionIn? program.funcs ⟨name⟩ with
  | none => exact ⟨_, .missing hf⟩
  | some f =>
    by_cases ha : f.args.size = args.size
    · cases ht : program.typeDefs.hasReservedPrefix with
      | false => exact ⟨_, .types hf ha ht⟩
      | true => exact ⟨_, .ready hf ha ht⟩
    · exact ⟨_, .arity hf ha⟩

theorem seeding_sound {program r} (h : Seeding program r) : seed program = forget r := by
  cases h <;> simp_all [seed, forget, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, Bind.bind, Except.bind]

theorem seeding_total (program : Program) : ∃ r, Seeding program r := by
  cases hs : seedGlobals ⟨program⟩ {} program.globals with
  | error e => exact ⟨_, .failed hs⟩
  | ok s => exact ⟨_, .ready hs (SetupSound.seedGlobals_wf hs)⟩

theorem activation_sound {ctx f args s r} (h : ActivationPhase ctx f args s r) :
    activate ctx f args s = forget r := by
  cases h with
  | ready he =>
    obtain ⟨env, t, hb, ha, hp⟩ := LocalEntry.ready_iff.mp he
    simp [activate, hb, ha, hp, forget, pure, Except.pure, Bind.bind, Except.bind]
  | parameters hb => simp [activate, hb, forget, Bind.bind, Except.bind]
  | results hb ha => simp [activate, hb, ha, forget, Bind.bind, Except.bind]
  | locations hb ha hp => simp [activate, hb, ha, hp, forget, Bind.bind, Except.bind]

theorem activation_total (ctx : ProgramCtx) (f : Func) (args : List GoValue) (s : Store) :
    ∃ r, ActivationPhase ctx f args s r := by
  obtain ⟨r, h⟩ := LocalEntry.total ctx f args s
  cases h with
  | ready hb ha hp => exact ⟨_, .ready (.ready hb ha hp)⟩
  | parametersFailed hb => exact ⟨_, .parameters hb⟩
  | resultsFailed hb ha => exact ⟨_, .results hb ha⟩
  | locationsFailed hb ha hp => exact ⟨_, .locations hb ha hp⟩

def storeResult (r : Result Store) (tail : Choices) : Except Stop (Store × Choices) :=
  match r with
  | .ok s => .ok (s, tail)
  | .error e => .error e.cause

theorem local_normal {o : Local.Outcome} (h : o.stop? = none) : o = .boundary .normal := by
  cases o with
  | boundary ending => cases ending <;> simp_all [Local.Outcome.stop?]
  | failed cause => cases cause <;> cases h
  | initializationPrint => cases h
  | exhausted => cases h

theorem initialization_coverage (ctx : ProgramCtx) (fuel : Nat) (s : Store) (ch : Choices) :
    ∃ seg r tail, Initialization ctx fuel s seg r ∧ OptionalReplay ctx seg ch tail ∧
      runPkgInitM ctx fuel s ch = storeResult r tail := by
  cases hf : findFunctionIn? ctx.functions pkgInitFuncId with
  | none => exact ⟨none, .ok s, ch, .absent hf, rfl, by simp [runPkgInitM, hf, storeResult, pure, Except.pure]⟩
  | some f =>
    by_cases shape : f.args.size = 0 ∧ f.results.size = 0
    · obtain ⟨ha, hr⟩ := shape
      obtain ⟨ls, b, records, o, cost, middle, tail, hx, hp, hrec, he⟩ :=
        Local.Correspondence.initialization_coverage ctx fuel (initializerPoint f s) ch
      let seg : Segment := ⟨initializerPoint f s, b, ls, records, o, cost⟩
      have hs : seg.Runs .initialization ctx fuel := hx
      have replay : OptionalReplay ctx (some seg) ch tail := ⟨middle, hp, hrec⟩
      cases ho : o.stop? with
      | none =>
        have hon := local_normal ho
        refine ⟨some seg, .ok b.store, tail, .normal hf ha hr rfl hs hon, replay, ?_⟩
        change runInitConfig ctx fuel s (initializerPoint f s).control ch = _ at he
        simp only [Local.Correspondence.observe, ho] at he
        simp [initializerPoint, statement] at he
        simp [runPkgInitM, hf, ha, hr, storeResult, he]
      | some e =>
        refine ⟨some seg, .error ⟨.initialization, initStop e⟩, tail,
          .stopped hf ha hr rfl hs ho, replay, ?_⟩
        change runInitConfig ctx fuel s (initializerPoint f s).control ch = _ at he
        simp only [Local.Correspondence.observe, ho] at he
        simp [runPkgInitM, hf, ha, hr, storeResult, initializerPoint, statement] at he ⊢
        rw [he]
        exact congrArg Except.error (initialization_projection e).symm
    · have malformed : f.args.size ≠ 0 ∨ f.results.size ≠ 0 := by omega
      refine ⟨none, .error ⟨.initializationShape, badInitializerShape⟩, ch,
        .malformed hf malformed, rfl, ?_⟩
      simp only [runPkgInitM, hf, bne_iff_ne, Bool.or_eq_true, if_pos malformed]
      rfl

theorem initialization_realization {ctx fuel s seg r}
    (h : Initialization ctx fuel s seg r) (tail : Choices) :
    ∃ ch, OptionalReplay ctx seg ch tail ∧ runPkgInitM ctx fuel s ch = storeResult r tail := by
  cases h with
  | absent hf => exact ⟨tail, rfl, by simp [runPkgInitM, hf, storeResult, pure, Except.pure]⟩
  | malformed hf shape =>
    refine ⟨tail, rfl, ?_⟩
    simp only [runPkgInitM, hf, bne_iff_ne, Bool.or_eq_true, if_pos shape]
    rfl
  | normal hf ha hr start hs ho =>
    obtain ⟨ch, middle, hp, hrec, he⟩ := Local.Correspondence.initialization_realization
      _ _ _ _ _ _ _ _ hs tail
    refine ⟨ch, ⟨middle, hp, hrec⟩, ?_⟩
    simp only [Local.Correspondence.driver, start, Local.Correspondence.observe, ho,
      Local.Outcome.stop?] at he
    simp [initializerPoint, statement] at he
    simp [runPkgInitM, hf, ha, hr, storeResult, he]
  | stopped hf ha hr start hs ho =>
    obtain ⟨ch, middle, hp, hrec, he⟩ := Local.Correspondence.initialization_realization
      _ _ _ _ _ _ _ _ hs tail
    refine ⟨ch, ⟨middle, hp, hrec⟩, ?_⟩
    simp only [Local.Correspondence.driver, start, Local.Correspondence.observe, ho] at he
    simp [runPkgInitM, hf, ha, hr, storeResult, initializerPoint, statement] at he ⊢
    rw [he]
    exact congrArg Except.error (initialization_projection _).symm

def setupResult (program : Program) (r : Result Ready) (tail : Choices) :
    Except Stop (ProgramCtx × Config × Store × List Loc × Choices) :=
  match r with
  | .error e => .error e.cause
  | .ok ready => .ok (⟨program⟩, (activationPoint ready.function ready.activation).control,
      ready.activation.store, ready.activation.results, tail)

theorem setup_eq (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (ch : Choices) :
    runProgramSetupM fuel program name args ch =
      (validate program name args).bind fun f =>
      (seed program).bind fun seeded =>
      (runPkgInitM ⟨program⟩ fuel seeded ch).bind fun (initialized, tail) =>
      (activate ⟨program⟩ f args.toList initialized).bind fun a =>
        setupResult program (.ok ⟨f, a⟩) tail := by
  unfold runProgramSetupM validate seed activate setupResult
  cases hf : findFunctionIn? program.funcs ⟨name⟩ with
  | none => rfl
  | some f =>
    simp only [pure_eq_ok, except_bind_ok, Except.bind]
    by_cases ha : f.args.size = args.size
    · simp only [ha, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      cases ht : program.typeDefs.hasReservedPrefix <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      · rfl
      · cases hg : seedGlobals ⟨program⟩ {} program.globals with
        | error e => rfl
        | ok seeded =>
          simp only [except_bind_ok]
          by_cases hw : StateWf ⟨program⟩ seeded
          · simp only [hw, ↓reduceIte]
            cases hi : runPkgInitM ⟨program⟩ fuel seeded ch with
            | error e => rfl
            | ok pair =>
              obtain ⟨initialized, tail⟩ := pair
              simp only [except_bind_ok]
              cases hb : bindParams ⟨program⟩ [] initialized f.args.toList args.toList with
              | error e => rfl
              | ok pair =>
                obtain ⟨env, t⟩ := pair
                simp only [except_bind_ok]
                cases hd : allocDecls ⟨program⟩ env t f.results.toList with
                | error e => rfl
                | ok pair =>
                  obtain ⟨frameEnv, u⟩ := pair
                  simp only [except_bind_ok]
                  cases hp : pinResultLocs frameEnv f.results.toList <;> rfl
          · simp only [hw, ↓reduceIte]
            rfl
    · simp [ha, wrongArity, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind]

theorem setup_coverage (program : Program) (name : String) (args : Array GoValue)
    (fuel : Nat) (ch : Choices) :
    ∃ seg r tail, Setup program name args fuel seg r ∧ OptionalReplay ⟨program⟩ seg ch tail ∧
      runProgramSetupM fuel program name args ch = setupResult program r tail := by
  obtain ⟨v, hv⟩ := validation_total program name args
  have hev := validation_sound hv
  rw [setup_eq]
  cases v with
  | error e => exact ⟨none, .error e, ch, .validationFailed hv, rfl, by rw [hev]; rfl⟩
  | ok f =>
    obtain ⟨s, hs⟩ := seeding_total program
    have hes := seeding_sound hs
    cases s with
    | error e => exact ⟨none, .error e, ch, .seedingFailed hv hs, rfl, by rw [hev]; simp only [forget, Except.bind]; rw [hes]; rfl⟩
    | ok seeded =>
      obtain ⟨seg, initialized, tail, hi, hr, hei⟩ := initialization_coverage ⟨program⟩ fuel seeded ch
      cases initialized with
      | error e =>
        refine ⟨seg, .error e, tail, .initializationFailed hv hs hi, hr, ?_⟩
        rw [hev]
        simp only [forget, Except.bind]
        rw [hes]
        simp only [forget]
        rw [hei]
        rfl
      | ok initialized =>
        obtain ⟨a, ha⟩ := activation_total ⟨program⟩ f args.toList initialized
        have hea := activation_sound ha
        cases a with
        | error e =>
          refine ⟨seg, .error e, tail, .activationFailed hv hs hi ha, hr, ?_⟩
          rw [hev]
          simp only [forget, Except.bind]
          rw [hes]
          simp only [forget]
          rw [hei]
          simp only [storeResult]
          rw [hea]
          rfl
        | ok a =>
          refine ⟨seg, .ok ⟨f, a⟩, tail, .ready hv hs hi ha, hr, ?_⟩
          rw [hev]
          simp only [forget, Except.bind]
          rw [hes]
          simp only [forget]
          rw [hei]
          simp only [storeResult]
          rw [hea]
          rfl

theorem setup_realization {program name args fuel seg r}
    (h : Setup program name args fuel seg r) (tail : Choices) :
    ∃ ch, OptionalReplay ⟨program⟩ seg ch tail ∧
      runProgramSetupM fuel program name args ch = setupResult program r tail := by
  cases h with
  | validationFailed hv =>
    exact ⟨tail, rfl, by rw [setup_eq, validation_sound hv]; rfl⟩
  | seedingFailed hv hs =>
    refine ⟨tail, rfl, ?_⟩
    rw [setup_eq, validation_sound hv]
    simp only [forget, Except.bind]
    rw [seeding_sound hs]
    rfl
  | initializationFailed hv hs hi =>
    obtain ⟨ch, hr, he⟩ := initialization_realization hi tail
    refine ⟨ch, hr, ?_⟩
    rw [setup_eq, validation_sound hv]
    simp only [forget, Except.bind]
    rw [seeding_sound hs]
    simp only [forget]
    rw [he]
    rfl
  | activationFailed hv hs hi ha =>
    obtain ⟨ch, hr, he⟩ := initialization_realization hi tail
    refine ⟨ch, hr, ?_⟩
    rw [setup_eq, validation_sound hv]
    simp only [forget, Except.bind]
    rw [seeding_sound hs]
    simp only [forget]
    rw [he]
    simp only [storeResult]
    rw [activation_sound ha]
    rfl
  | ready hv hs hi ha =>
    obtain ⟨ch, hr, he⟩ := initialization_realization hi tail
    refine ⟨ch, hr, ?_⟩
    rw [setup_eq, validation_sound hv]
    simp only [forget, Except.bind]
    rw [seeding_sound hs]
    simp only [forget]
    rw [he]
    simp only [storeResult]
    rw [activation_sound ha]
    rfl

theorem coverage : Coverage := by
  intro program name args fuel ch
  obtain ⟨init, setup, middle, hs, hi, hes⟩ := setup_coverage program name args fuel ch
  cases setup with
  | error e =>
    refine ⟨⟨init, none⟩, .error e, middle, .setupFailed hs, ⟨middle, hi, rfl⟩, ?_⟩
    simp [runProgramM, hes, setupResult, project, Bind.bind, Except.bind]
  | ok ready =>
    obtain ⟨ls, b, records, o, cost, last, tail, hx, hp, hr, he⟩ :=
      Local.Correspondence.main_coverage ⟨program⟩ fuel (activationPoint ready.function ready.activation) middle
    let seg : Segment := ⟨activationPoint ready.function ready.activation, b, ls, records, o, cost⟩
    have hseg : seg.Runs .main ⟨program⟩ fuel := hx
    have replay : HistoryReplay ⟨program⟩ ⟨init, some seg⟩ ch tail :=
      ⟨middle, hi, last, hp, hr⟩
    have he' : runConfig ⟨program⟩ fuel ready.activation.store
        (activationPoint ready.function ready.activation).control middle =
        Local.Correspondence.observe o b tail := by
      simpa [runConfig_eq_loop, Local.Correspondence.driver, activationPoint, statement] using he
    cases ho : o.stop? with
    | some e =>
      refine ⟨⟨init, some seg⟩, .error ⟨.body, e⟩, tail,
        .bodyStopped hs rfl hseg ho, replay, ?_⟩
      simp [runProgramM, hes, setupResult, he', Local.Correspondence.observe, ho,
        project, Bind.bind, Except.bind]
    | none =>
      have hon := local_normal ho
      cases hv : loadMany ⟨program⟩ b.store ready.activation.results with
      | error e =>
        refine ⟨⟨init, some seg⟩, .error ⟨.readback, e⟩, tail,
          .readbackFailed hs rfl hseg hon hv, replay, ?_⟩
        simp [runProgramM, hes, setupResult, he', Local.Correspondence.observe, ho,
          hv, project, Bind.bind, Except.bind]
      | ok values =>
        refine ⟨⟨init, some seg⟩, .ok values, tail,
          .normal hs rfl hseg hon hv, replay, ?_⟩
        simp [runProgramM, hes, setupResult, he', Local.Correspondence.observe, ho,
          hv, project, Bind.bind, Except.bind, pure, Except.pure]

theorem realization : Realization := by
  intro program name args fuel history outcome h tail
  cases h with
  | setupFailed hs =>
    obtain ⟨ch, hr, he⟩ := setup_realization hs tail
    refine ⟨ch, ⟨tail, hr, rfl⟩, ?_⟩
    simp [runProgramM, he, setupResult, project, Bind.bind, Except.bind]
  | bodyStopped hs start hseg ho =>
    obtain ⟨middle, last, hp, hr, he⟩ := Local.Correspondence.main_realization
      _ _ _ _ _ _ _ _ hseg tail
    obtain ⟨ch, hi, hes⟩ := setup_realization hs middle
    refine ⟨ch, ⟨middle, hi, last, hp, hr⟩, ?_⟩
    simp only [Local.Correspondence.driver, start, Local.Correspondence.observe, ho] at he
    simp [runProgramM, hes, setupResult, runConfig_eq_loop, activationPoint, statement,
      project, Bind.bind, Except.bind] at he ⊢
    rw [he]
  | readbackFailed hs start hseg ho hv =>
    obtain ⟨middle, last, hp, hr, he⟩ := Local.Correspondence.main_realization
      _ _ _ _ _ _ _ _ hseg tail
    obtain ⟨ch, hi, hes⟩ := setup_realization hs middle
    refine ⟨ch, ⟨middle, hi, last, hp, hr⟩, ?_⟩
    simp only [Local.Correspondence.driver, start, Local.Correspondence.observe, ho,
      Local.Outcome.stop?] at he
    simp [runProgramM, hes, setupResult, runConfig_eq_loop, activationPoint, statement,
      project, Bind.bind, Except.bind] at he ⊢
    rw [he]
    simp [Readback] at hv
    simp [hv]
  | normal hs start hseg ho hv =>
    obtain ⟨middle, last, hp, hr, he⟩ := Local.Correspondence.main_realization
      _ _ _ _ _ _ _ _ hseg tail
    obtain ⟨ch, hi, hes⟩ := setup_realization hs middle
    refine ⟨ch, ⟨middle, hi, last, hp, hr⟩, ?_⟩
    simp only [Local.Correspondence.driver, start, Local.Correspondence.observe, ho,
      Local.Outcome.stop?] at he
    simp [runProgramM, hes, setupResult, runConfig_eq_loop, activationPoint, statement,
      project, Bind.bind, Except.bind] at he ⊢
    rw [he]
    simp [Readback] at hv
    simp [hv]

theorem refusal_exclusion : RefusalExclusion := by
  intro program name args avoid fuel ch reason h
  obtain ⟨history, outcome, tail, hx, _, he⟩ := coverage program name args fuel ch
  have bad := avoid fuel history outcome hx
  cases outcome with
  | ok values => simp [project, he] at h
  | error e =>
    apply bad
    refine ⟨reason, ?_⟩
    simpa [project, he] using h

theorem fatal_exclusion : FatalExclusion := by
  intro program name args avoid fuel ch message h
  obtain ⟨history, outcome, tail, hx, _, he⟩ := coverage program name args fuel ch
  have bad := avoid fuel history outcome hx
  cases outcome with
  | ok values => simp [project, he] at h
  | error e =>
    apply bad
    refine ⟨message, ?_⟩
    simpa [project, he] using h

end Correspondence

/-- Compatibility with the existing success-only contract, with independent
initialization and body bounds and unchanged sequential readout. -/
theorem normal_iff (program : Program) (name : String) (args : Array GoValue)
    (fuel : Nat) (values : List GoValue) :
    (∃ history, Execution program name args fuel history (.ok values)) ↔
      ∃ initLabels bodyLabels final,
        initLabels.length ≤ fuel ∧ bodyLabels.length ≤ fuel ∧
        ProgramNormal program name args initLabels bodyLabels final values := by
  constructor
  · rintro ⟨history, hx⟩
    obtain ⟨ch, _, he⟩ := Correspondence.realization _ _ _ _ _ _ hx []
    obtain ⟨il, bl, final, vs, hi, hb, hn, hv⟩ := program_normal_of_run he
    have eqValues : vs = values := by
      have hh := congrArg (fun r : Readout => r.values.toList) hv
      simpa [Correspondence.project] using hh.symm
    subst vs
    exact ⟨il, bl, final, hi, hb, hn⟩
  · rintro ⟨il, bl, final, hi, hb, hn⟩
    obtain ⟨ch, he⟩ := hn.realize fuel hi hb
    obtain ⟨history, o, tail, hx, _, hp⟩ := Correspondence.coverage program name args fuel ch
    rw [he] at hp
    cases o with
    | error e => cases hp
    | ok vs =>
      have hv : values = vs := by
        have hh := congrArg (fun r : Readout => r.values.toList) (Except.ok.inj hp)
        simpa [Correspondence.project] using hh
      subst vs
      exact ⟨history, hx⟩

end GoLean.GoCore.Relational.ProgramExecution
