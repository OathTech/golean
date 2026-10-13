import GoLean.GoCore.RelationalEntry
import GoLean.GoCore.RelationalPhaseSound

/-!
# Successful sequential program executions

This specification includes validation, global seeding, actual initialization,
local activation, a labelled body run and final readback. Initialization and
body each have their own fuel bound in the bridge. The sequential driver
returns values and does not fold output labels; no pool/CLI claim is made.

This is the successful-program subset. It is not an exhaustive outcome
classification: setup errors, fatal failures and ordinary operation refusals
need the broader failure relation before a general adequacy transfer.
-/

namespace GoLean.GoCore.Relational

open Machine

inductive PackageInit (ctx : ProgramCtx) (s : Store) : List StepLabel → Store → Prop where
  | absent : findFunctionIn? ctx.functions pkgInitFuncId = none → PackageInit ctx s [] s
  | present {f ls t} : findFunctionIn? ctx.functions pkgInitFuncId = some f →
      f.args.size = 0 → f.results.size = 0 →
      Initializes ctx (statement f.body [] ⟨.frame [] [] [] [] .stop f.id⟩ s) ls t →
      PackageInit ctx s ls t

def ProgramNormal (program : Program) (name : String) (args : Array GoValue)
    (initLabels bodyLabels : List StepLabel) (final : Store) (values : List GoValue) : Prop :=
  ∃ f seeded initialized a,
    findFunctionIn? program.funcs ⟨name⟩ = some f ∧
    f.args.size = args.size ∧ program.typeDefs.hasReservedPrefix = true ∧
    seedGlobals ⟨program⟩ {} program.globals = .ok seeded ∧
    PackageInit ⟨program⟩ seeded initLabels initialized ∧
    LocalEntry ⟨program⟩ f args.toList initialized (.ok a) ∧
    Run ⟨program⟩ (activationPoint f a) bodyLabels (resumed .halt final) ∧
    Readback ⟨program⟩ final a.results (.ok values)

theorem PackageInit.realize {ctx : ProgramCtx} {s t : Store} {ls : List StepLabel}
    (h : PackageInit ctx s ls t) (fuel : Nat) (enough : ls.length ≤ fuel) (tail : Choices) :
    ∃ ch, runPkgInitM ctx fuel s ch = .ok (t, tail) := by
  cases h with
  | absent hf => exact ⟨tail, by simp [runPkgInitM, hf, pure, Except.pure]⟩
  | present hf ha hr hi =>
    obtain ⟨ch, hc⟩ := hi.realize fuel enough tail
    refine ⟨ch, ?_⟩
    have hc' := hc
    simp only [statement] at hc'
    simp [runPkgInitM, hf, ha, hr, hc', pure, Except.pure]

/-- A successful package initialization supplies an actual guarded relational
run, not a fixed array of initial cells. -/
theorem packageInit_of_run {ctx : ProgramCtx} {fuel : Nat} {s t : Store} {ch tail : Choices}
    (h : runPkgInitM ctx fuel s ch = .ok (t, tail)) :
    ∃ ls, ls.length ≤ fuel ∧ PackageInit ctx s ls t := by
  unfold runPkgInitM at h
  cases hf : findFunctionIn? ctx.functions pkgInitFuncId with
  | none =>
    simp only [hf, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], Nat.zero_le _, .absent hf⟩
  | some f =>
    simp only [hf] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    · rename_i shape
      have sizes : f.args.size = 0 ∧ f.results.size = 0 := by simpa using shape
      obtain ⟨ha, hr⟩ := sizes
      simp only [pure_eq_ok] at h
      cases hi : runInitConfig ctx fuel s (.exec f.body [] (.frame [] [] [] [] .stop f.id)) ch with
      | error e => simp [hi, throw, throwThe, MonadExceptOf.throw] at h
      | ok pair =>
        obtain ⟨u, mid⟩ := pair
        simp only [hi, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ls, hn, hh⟩ := initializes_of_run hi
        exact ⟨ls, hn, .present hf ha hr hh⟩

/-- Sound transfer to the actual sequential driver. The two fuel bounds are
separate; terminal normal completion costs zero. -/
theorem ProgramNormal.realize {program : Program} {name : String} {args : Array GoValue}
    {initLabels bodyLabels : List StepLabel} {final : Store} {values : List GoValue}
    (h : ProgramNormal program name args initLabels bodyLabels final values)
    (fuel : Nat) (hi : initLabels.length ≤ fuel) (hb : bodyLabels.length ≤ fuel) :
    ∃ ch, runProgramM fuel program name args ch = .ok { values := values.toArray } := by
  obtain ⟨f, seeded, initialized, a, hf, ha, ht, hs, hin, he, hr, hv⟩ := h
  obtain ⟨env, bound, hbind, halloc, hpin⟩ := LocalEntry.ready_iff.mp he
  obtain ⟨bodyTape, bodyTail, hbody⟩ := normal_run_iff.mpr ⟨bodyLabels, hb, hr⟩
  obtain ⟨ch, hinit⟩ := hin.realize fuel hi bodyTape
  have hsetup := SetupSound.runProgramSetup_init hf ha ht hs hinit hbind halloc hpin
  refine ⟨ch, ?_⟩
  have hbody' : runConfig ⟨program⟩ fuel a.store
      (.exec f.body a.locals (.frame [] [] [] [] .stop f.id)) bodyTape = .ok (final, bodyTail) := by
    simpa [runConfig_eq_loop, activationPoint, statement] using hbody
  simp only [runProgramM, hsetup, Bind.bind, Except.bind, hbody', Readback] at hv ⊢
  simp [hv, pure, Except.pure]

private theorem setup_success {fuel : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {result : ProgramCtx × Config × Store × List Loc × Choices}
    (h : runProgramSetupM fuel program name args ch = .ok result) :
    ∃ f seeded initialized a tail,
      findFunctionIn? program.funcs ⟨name⟩ = some f ∧ f.args.size = args.size ∧
      program.typeDefs.hasReservedPrefix = true ∧ seedGlobals ⟨program⟩ {} program.globals = .ok seeded ∧
      runPkgInitM ⟨program⟩ fuel seeded ch = .ok (initialized, tail) ∧
      LocalEntry ⟨program⟩ f args.toList initialized (.ok a) ∧
      result = (⟨program⟩, (activationPoint f a).control, a.store, a.results, tail) := by
  unfold runProgramSetupM at h
  cases hf : findFunctionIn? program.funcs ⟨name⟩ with
  | none => simp [hf, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  | some f =>
    simp only [hf, pure_eq_ok, except_bind_ok] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    · rename_i arity
      have ha : f.args.size = args.size := by simpa using arity
      split at h
      · rename_i types
        simp only [bind_eq_ok] at h
        obtain ⟨seeded, hs, h⟩ := h
        split at h
        · simp only [bind_eq_ok] at h
          obtain ⟨⟨initialized, tail⟩, hi, ⟨⟨env, bound⟩, hb, ⟨⟨locals, final⟩, hd, ⟨results, hp, hr⟩⟩⟩⟩ := h
          exact ⟨f, seeded, initialized, ⟨locals, final, results⟩, tail, rfl, ha, types, hs, hi,
            .ready hb hd hp, (Except.ok.inj hr).symm⟩
        · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h

/-- Every actual successful program run has a relational program execution.
This direction is what transfers universal relational postconditions. -/
theorem program_normal_of_run {fuel : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {out : Readout}
    (h : runProgramM fuel program name args ch = .ok out) :
    ∃ initLabels bodyLabels final values,
      initLabels.length ≤ fuel ∧ bodyLabels.length ≤ fuel ∧
      ProgramNormal program name args initLabels bodyLabels final values ∧
      out = { values := values.toArray } := by
  simp only [runProgramM, bind_eq_ok] at h
  obtain ⟨⟨ctx, c, s, locs, mid⟩, hs, ⟨⟨final, tail⟩, hr, values, hv, ho⟩⟩ := h
  obtain ⟨f, seeded, initialized, a, mid', hf, ha, ht, hg, hi, he, hc⟩ := setup_success hs
  cases hc
  obtain ⟨initLabels, hin, hip⟩ := packageInit_of_run hi
  have hr' : execStmtLoop ⟨program⟩ fuel (activationPoint f a).store
      (activationPoint f a).control mid = .ok (final, tail) := by
    simpa [runConfig_eq_loop, activationPoint, statement] using hr
  obtain ⟨bodyLabels, hbn, hbody⟩ := normal_run_iff.mp ⟨mid, tail, hr'⟩
  exact ⟨initLabels, bodyLabels, final, values, hin, hbn,
    ⟨f, seeded, initialized, a, hf, ha, ht, hg, hip, he, hbody, hv⟩,
    (Except.ok.inj ho).symm⟩

end GoLean.GoCore.Relational
