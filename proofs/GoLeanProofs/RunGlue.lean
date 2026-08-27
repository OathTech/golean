import GoLeanProofs.FuelMeasure

/-!
# The runProgramM glue family (W1; design note
`docs/2026-08-27_w1-judgment-design.md` §4)

The whole-PROGRAM entry (`runProgramM` = setup → `$pkginit` →
subject `runConfig` → `loadMany` readback) had no proof-layer lemmas
at all (surfaced by the professor's final review; proof-structure
§4b). This module is the family that gates BOTH sentences:

* `runPkgInitM_mono` / `runProgramSetupM_mono` / **`runProgramM_mono`**
  — two-phase fuel monotonicity: a completed run is stable under
  more fuel (each phase is bounded by the same `fuel`; the pre/post
  plumbing is fuel-independent).
* **`runProgramM_readout_of_total`** — the bridge from ∃N-total
  specs to the ∀-fuel PARTIAL sentence: if for every stream some
  fuel completes the program with a `spec`-satisfying result, then
  EVERY successful completion at any fuel satisfies `spec`.
* **`runConfig_prefix_classify`** — a completed run's truncations
  die at the fuel check, never at a fault. Plus the phase lift
  `runPkgInitM_prefix_classify` and the two-phase program-level
  lift **`runProgramM_classify_of_total`** — NeverFaults'
  truncation half (`∀ fuel, .ok r ∨ .error .fuelOut` from one
  completed run).
* Conditioned unfolding/intro lemmas for `runPkgInitM` /
  `runProgramSetupM` / `runProgramM` (the forms the spec layer
  composes through — each hypothesis type pins its computation,
  StepKit rule 2).
* The readback lemmas: `loadMany_nil` / `loadMany_cons` /
  `loadMany_ok_of_loads`.

All ∀-quantified; no subject-run constants. LINEAGE (design note
§4): fuel-monotonicity/determinism lemmas standard for step-indexed
executable semantics (CompCert-style smallstep determinism; the
readout argument is the same determinism-of-a-function-of-inputs
argument as the landed `harness_readout_of_total`). Audit pins:
`Audit/W1.lean`.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-! ## The readback (`loadMany`) `.ok` lemmas -/

@[simp] theorem loadMany_nil {σ : ExecState} : loadMany σ [] = .ok [] := rfl

theorem loadMany_cons {σ : ExecState} {l : Loc} {locs : List Loc}
    {v : GoValue} {vs : List GoValue}
    (h : loadLoc σ l = .ok v) (hs : loadMany σ locs = .ok vs) :
    loadMany σ (l :: locs) = .ok (v :: vs) := by
  simp only [loadMany, h, hs, Bind.bind, Except.bind, pure, Except.pure]

/-- Readback succeeds when every pinned location loads: the `.ok`
lemma for the result reads (frame arm / `runProgramM` readback). -/
theorem loadMany_ok_of_loads {σ : ExecState} :
    ∀ {locs : List Loc}, (∀ l ∈ locs, ∃ v, loadLoc σ l = .ok v) →
      ∃ vs, loadMany σ locs = .ok vs := by
  intro locs
  induction locs with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons l ls ih =>
      intro h
      obtain ⟨v, hv⟩ := h l (List.mem_cons_self ..)
      obtain ⟨vs, hvs⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      exact ⟨v :: vs, loadMany_cons hv hvs⟩

/-! ## `runConfig`: truncation classification -/

/-- A non-terminal configuration (witnessed by a successful step) at
fuel 0 reports exhaustion. -/
theorem runConfig_zero_fuelOut {σ : ExecState} {c : Config} {ch : Choices}
    {t : Config × ExecState × Choices}
    (h : stepFn σ c ch = .ok t) :
    runConfig 0 σ c ch = .error .fuelOut := by
  rw [runConfig_unfold]
  split
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · rfl

/-- **A completed run's truncations die at the fuel check, never at a
fault**: if `runConfig` completes at some fuel, then at EVERY fuel it
either completes with the SAME result or reports `.fuelOut` — no
truncation introduces a panic, a stuck, or any other error.
NeverFaults' truncation half at configuration granularity. -/
theorem runConfig_prefix_classify :
    ∀ {fuel N : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {r : ExecState × Choices},
      runConfig N σ c ch = .ok r →
      runConfig fuel σ c ch = .ok r
        ∨ runConfig fuel σ c ch = .error .fuelOut := by
  intro fuel
  induction fuel with
  | zero =>
      intro N σ c ch r h
      match N, h with
      | 0, h => exact .inl h
      | N' + 1, h =>
          rw [runConfig_unfold] at h
          split at h
          · cases h; exact .inl runConfig_next_stop
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · rw [bind_eq_ok] at h
            obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, _⟩ := h
            exact .inr (runConfig_zero_fuelOut hstep)
  | succ m ih =>
      intro N σ c ch r h
      match N, h with
      | 0, h =>
          exact .inl (runConfig_mono 0 (m + 1) _ _ _ _ (Nat.zero_le _) h)
      | N' + 1, h =>
          rw [runConfig_unfold] at h
          split at h
          · cases h; exact .inl runConfig_next_stop
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
          · rw [bind_eq_ok] at h
            obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
            rcases ih hrest with hok | hout
            · exact .inl (by rw [runConfig_step hstep]; exact hok)
            · exact .inr (by rw [runConfig_step hstep]; exact hout)

/-! ## `runPkgInitM`: the unfolding equation, conditioned intros,
monotonicity, classification -/

/-- `runPkgInitM`, as a clean first-order cascade (the do-notation
join points eliminated) — the unfolding lemma every downstream proof
rewrites with. -/
theorem runPkgInitM_eq (fuel : Nat) (state : ExecState) (ch : Choices) :
    runPkgInitM fuel state ch =
      match findFunctionIn? state.functions pkgInitFuncId with
      | none => .ok (state, ch)
      | some initF =>
          if initF.args.size != 0 || initF.results.size != 0 then
            .error (.stuck s!"malformed {pkgInitFuncId.key}: expected no parameters and no results")
          else
            match runConfig fuel state
                (.exec initF.body [] (.frame [] [] [] [] .stop)) ch with
            | .ok r => .ok r
            | .error e => .error (markInitPhase e) := by
  unfold runPkgInitM
  cases findFunctionIn? state.functions pkgInitFuncId with
  | none => rfl
  | some initF =>
      by_cases hshape : (initF.args.size != 0 || initF.results.size != 0) = true
      · simp [hshape, throw, throwThe, MonadExceptOf.throw, Bind.bind,
          Except.bind]
      · simp only [hshape, Bool.false_eq_true, if_false]
        cases runConfig fuel state
            (.exec initF.body [] (.frame [] [] [] [] .stop)) ch with
        | ok r => simp [pure, Except.pure, Bind.bind, Except.bind]
        | error e => simp [throw, throwThe, MonadExceptOf.throw, Bind.bind,
            Except.bind]

/-- No `$pkginit` in the program: init is the identity at any fuel. -/
theorem runPkgInitM_none {fuel : Nat} {state : ExecState} {ch : Choices}
    (h : findFunctionIn? state.functions pkgInitFuncId = none) :
    runPkgInitM fuel state ch = .ok (state, ch) := by
  simp only [runPkgInitM_eq, h]

/-- A well-shaped `$pkginit` whose body run completes: init returns
the run's result (the conditioned intro form). -/
theorem runPkgInitM_some_ok {fuel : Nat} {state : ExecState} {ch : Choices}
    {initF : Func} {r : ExecState × Choices}
    (hfind : findFunctionIn? state.functions pkgInitFuncId = some initF)
    (hargs : initF.args.size = 0) (hres : initF.results.size = 0)
    (hrun : runConfig fuel state
      (.exec initF.body [] (.frame [] [] [] [] .stop)) ch = .ok r) :
    runPkgInitM fuel state ch = .ok r := by
  simp only [runPkgInitM_eq, hfind, hargs, hres, hrun,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, if_false]

/-- Init-phase fuel monotonicity. -/
theorem runPkgInitM_mono {N fuel : Nat} {state : ExecState} {ch : Choices}
    {r : ExecState × Choices} (hle : N ≤ fuel)
    (h : runPkgInitM N state ch = .ok r) :
    runPkgInitM fuel state ch = .ok r := by
  rw [runPkgInitM_eq] at h ⊢
  cases hfind : findFunctionIn? state.functions pkgInitFuncId with
  | none => simp only [hfind] at h ⊢; exact h
  | some initF =>
      simp only [hfind] at h ⊢
      by_cases hshape : (initF.args.size != 0 || initF.results.size != 0) = true
      · rw [if_pos hshape] at h; cases h
      · rw [if_neg hshape] at h; rw [if_neg hshape]
        cases hrun : runConfig N state
            (.exec initF.body [] (.frame [] [] [] [] .stop)) ch with
        | error e => rw [hrun] at h; cases h
        | ok q =>
            rw [hrun] at h
            rw [runConfig_mono N fuel _ _ _ _ hle hrun]
            exact h

/-- Init-phase truncation classification (the diagnostic marker does
not touch `.fuelOut` — `markInitPhase`'s recorded design). -/
theorem runPkgInitM_prefix_classify {N : Nat} {state : ExecState}
    {ch : Choices} {r : ExecState × Choices}
    (h : runPkgInitM N state ch = .ok r) :
    ∀ fuel : Nat, runPkgInitM fuel state ch = .ok r
      ∨ runPkgInitM fuel state ch = .error .fuelOut := by
  intro fuel
  rw [runPkgInitM_eq] at h ⊢
  cases hfind : findFunctionIn? state.functions pkgInitFuncId with
  | none => simp only [hfind] at h ⊢; exact .inl h
  | some initF =>
      simp only [hfind] at h ⊢
      by_cases hshape : (initF.args.size != 0 || initF.results.size != 0) = true
      · rw [if_pos hshape] at h; cases h
      · rw [if_neg hshape] at h; rw [if_neg hshape]
        cases hrun : runConfig N state
            (.exec initF.body [] (.frame [] [] [] [] .stop)) ch with
        | error e => rw [hrun] at h; cases h
        | ok q =>
            rw [hrun] at h
            rcases runConfig_prefix_classify (fuel := fuel) hrun with hok | hout
            · rw [hok]; exact .inl h
            · rw [hout]; exact .inr rfl

/-! ## `runProgramSetupM` / `runProgramM`: unfolding equations,
monotonicity, classification, the readout -/

/-- The initial table-carrier state `runProgramSetupM` seeds from. -/
def setupState (program : Program) : ExecState :=
  { types := program.typeDefs.toList, functions := program.funcs
    methods := program.methods, methodSets := program.methodSets }

/-- `runProgramSetupM`, as a clean first-order cascade — the
unfolding lemma (all fuel dependence isolated in the one
`runPkgInitM` occurrence). -/
theorem runProgramSetupM_eq (fuel : Nat) (program : Program)
    (name : String) (args : Array GoValue) (ch : Choices) :
    runProgramSetupM fuel program name args ch =
      match findFunctionIn? program.funcs ⟨name⟩ with
      | none => .error (.stuck s!"GoCore function not found: {name}")
      | some func =>
        if func.args.size != args.size then
          .error (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
        else
          match seedGlobals (setupState program) program.globals with
          | .error e => .error e
          | .ok s₀ =>
            if StateWf s₀ then
              match runPkgInitM fuel s₀ ch with
              | .error e => .error e
              | .ok (s₁, choices₁) =>
                match bindParams [] s₁ func.args.toList args.toList with
                | .error e => .error e
                | .ok (env, s₂) =>
                  match allocDecls env s₂ func.results.toList with
                  | .error e => .error e
                  | .ok (frameEnv, s₃) =>
                    match pinResultLocs frameEnv func.results.toList with
                    | .error e => .error e
                    | .ok resultLocs =>
                        .ok (.exec func.body frameEnv
                              (.frame [] [] [] [] .stop),
                             s₃, resultLocs, choices₁)
            else .error (.internal "seeded state ill-formed: a location in a global cell or function body dangles beyond the allocator bound") := by
  have hstate : setupState program
      = { types := program.typeDefs.toList,
          functions := program.funcs, methods := program.methods,
          methodSets := program.methodSets } := rfl
  unfold runProgramSetupM
  rw [← hstate]
  cases findFunctionIn? program.funcs ⟨name⟩ with
  | none => simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  | some func =>
      by_cases harity : (func.args.size != args.size) = true
      · simp [harity, throw, throwThe, MonadExceptOf.throw, Bind.bind,
          Except.bind]
      · simp only [harity, Bool.false_eq_true, if_false, Bind.bind,
          Except.bind, pure, Except.pure]
        cases seedGlobals (setupState program) program.globals with
        | error e => simp
        | ok s₀ =>
            by_cases hwf : StateWf s₀
            · simp only [hwf, if_true]
              cases runPkgInitM fuel s₀ ch with
              | error e => rfl
              | ok q =>
                  obtain ⟨s₁, choices₁⟩ := q
                  dsimp only
                  cases bindParams [] s₁ func.args.toList args.toList with
                  | error e => rfl
                  | ok p =>
                      obtain ⟨env, s₂⟩ := p
                      dsimp only
                      cases allocDecls env s₂ func.results.toList with
                      | error e => rfl
                      | ok p2 =>
                          obtain ⟨frameEnv, s₃⟩ := p2
                          dsimp only
                          cases pinResultLocs frameEnv func.results.toList with
                          | error e => rfl
                          | ok locs => rfl
            · simp [hwf, throw, throwThe, MonadExceptOf.throw]

/-- Setup fuel monotonicity (the only fuel-dependent phase is init). -/
theorem runProgramSetupM_mono {N fuel : Nat} {program : Program}
    {name : String} {args : Array GoValue} {ch : Choices}
    {q : Config × ExecState × List Loc × Choices} (hle : N ≤ fuel)
    (h : runProgramSetupM N program name args ch = .ok q) :
    runProgramSetupM fuel program name args ch = .ok q := by
  rw [runProgramSetupM_eq] at h
  rcases hfind : findFunctionIn? program.funcs ⟨name⟩ with _ | func
  case none => simp only [hfind] at h; cases h
  case some =>
  simp only [hfind] at h
  by_cases harity : (func.args.size != args.size) = true
  · rw [if_pos harity] at h; cases h
  · rw [if_neg harity] at h
    rcases hseed : seedGlobals (setupState program) program.globals
        with e | s₀
    case error => simp only [hseed] at h; cases h
    case ok =>
    simp only [hseed] at h
    by_cases hwf : StateWf s₀
    · rw [if_pos hwf] at h
      rcases hinit : runPkgInitM N s₀ ch with e | ⟨s₁, ch₁⟩
      case error => simp only [hinit] at h; cases h
      case ok =>
      simp only [hinit] at h
      rw [runProgramSetupM_eq]
      simp only [hfind, if_neg harity, hseed, if_pos hwf,
        runPkgInitM_mono hle hinit]
      exact h
    · rw [if_neg hwf] at h; cases h

/-- Setup truncation classification: same result or `.fuelOut`. -/
theorem runProgramSetupM_prefix_classify {N : Nat} {program : Program}
    {name : String} {args : Array GoValue} {ch : Choices}
    {q : Config × ExecState × List Loc × Choices}
    (h : runProgramSetupM N program name args ch = .ok q) :
    ∀ fuel : Nat, runProgramSetupM fuel program name args ch = .ok q
      ∨ runProgramSetupM fuel program name args ch = .error .fuelOut := by
  intro fuel
  rw [runProgramSetupM_eq] at h
  rcases hfind : findFunctionIn? program.funcs ⟨name⟩ with _ | func
  case none => simp only [hfind] at h; cases h
  case some =>
  simp only [hfind] at h
  by_cases harity : (func.args.size != args.size) = true
  · rw [if_pos harity] at h; cases h
  · rw [if_neg harity] at h
    rcases hseed : seedGlobals (setupState program) program.globals
        with e | s₀
    case error => simp only [hseed] at h; cases h
    case ok =>
    simp only [hseed] at h
    by_cases hwf : StateWf s₀
    · rw [if_pos hwf] at h
      rcases hinit : runPkgInitM N s₀ ch with e | ⟨s₁, ch₁⟩
      case error => simp only [hinit] at h; cases h
      case ok =>
      simp only [hinit] at h
      rcases runPkgInitM_prefix_classify hinit fuel with hok | hout
      · refine .inl ?_
        rw [runProgramSetupM_eq]
        simp only [hfind, if_neg harity, hseed, if_pos hwf, hok]
        exact h
      · refine .inr ?_
        rw [runProgramSetupM_eq]
        simp only [hfind, if_neg harity, hseed, if_pos hwf, hout]
    · rw [if_neg hwf] at h; cases h

/-- `runProgramM`, as setup → subject run → readback (the unfolding
lemma). -/
theorem runProgramM_eq (fuel : Nat) (program : Program) (name : String)
    (args : Array GoValue) (ch : Choices) :
    runProgramM fuel program name args ch =
      match runProgramSetupM fuel program name args ch with
      | .error e => .error e
      | .ok (c₀, s₃, resultLocs, choices₁) =>
          match runConfig fuel s₃ c₀ choices₁ with
          | .error e => .error e
          | .ok (sF, _) =>
              match loadMany sF resultLocs with
              | .error e => .error e
              | .ok vs => .ok { values := vs.toArray } := by
  unfold runProgramM
  cases runProgramSetupM fuel program name args ch with
  | error e => simp [Bind.bind, Except.bind]
  | ok q =>
      obtain ⟨c₀, s₃, resultLocs, choices₁⟩ := q
      simp only [Bind.bind, Except.bind]
      cases runConfig fuel s₃ c₀ choices₁ with
      | error e => rfl
      | ok p =>
          obtain ⟨sF, chF⟩ := p
          try dsimp only
          cases loadMany sF resultLocs with
          | error e => rfl
          | ok vs => rfl

/-- The conditioned intro form of `runProgramM` (the shape the spec
layer's assembly composes through). -/
theorem runProgramM_of_setup {fuel : Nat} {program : Program}
    {name : String} {args : Array GoValue} {ch : Choices}
    {c₀ : Config} {s₃ sF : ExecState} {resultLocs : List Loc}
    {choices₁ chF : Choices} {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch
      = .ok (c₀, s₃, resultLocs, choices₁))
    (hrun : runConfig fuel s₃ c₀ choices₁ = .ok (sF, chF))
    (hload : loadMany sF resultLocs = .ok vs) :
    runProgramM fuel program name args ch = .ok { values := vs.toArray } := by
  simp only [runProgramM_eq, hsetup, hrun, hload]

/-- **Whole-program fuel monotonicity** (two-phase: init and subject
each bounded by the same `fuel`; plumbing fuel-independent). -/
theorem runProgramM_mono {N fuel : Nat} {program : Program}
    {name : String} {args : Array GoValue} {ch : Choices} {r : Result}
    (hle : N ≤ fuel)
    (h : runProgramM N program name args ch = .ok r) :
    runProgramM fuel program name args ch = .ok r := by
  rw [runProgramM_eq] at h
  rcases hsetup : runProgramSetupM N program name args ch
      with e | ⟨c₀, s₃, resultLocs, choices₁⟩
  case error => simp only [hsetup] at h; cases h
  case ok =>
  simp only [hsetup] at h
  rcases hrun : runConfig N s₃ c₀ choices₁ with e | ⟨sF, chF⟩
  case error => simp only [hrun] at h; cases h
  case ok =>
  simp only [hrun] at h
  rw [runProgramM_eq]
  simp only [runProgramSetupM_mono hle hsetup,
    runConfig_mono N fuel _ _ _ _ hle hrun]
  exact h

/-- **The two-phase truncation classification** — NeverFaults'
truncation half at the whole-program entry: one completed run
classifies EVERY fuel's outcome as the same result or `.fuelOut`. -/
theorem runProgramM_classify_of_total {N : Nat} {program : Program}
    {name : String} {args : Array GoValue} {ch : Choices} {r : Result}
    (h : runProgramM N program name args ch = .ok r) :
    ∀ fuel : Nat, runProgramM fuel program name args ch = .ok r
      ∨ runProgramM fuel program name args ch = .error .fuelOut := by
  intro fuel
  rw [runProgramM_eq] at h
  rcases hsetup : runProgramSetupM N program name args ch
      with e | ⟨c₀, s₃, resultLocs, choices₁⟩
  case error => simp only [hsetup] at h; cases h
  case ok =>
  simp only [hsetup] at h
  rcases hrun : runConfig N s₃ c₀ choices₁ with e | ⟨sF, chF⟩
  case error => simp only [hrun] at h; cases h
  case ok =>
  simp only [hrun] at h
  rcases runProgramSetupM_prefix_classify hsetup fuel with hsok | hsout
  · rcases runConfig_prefix_classify (fuel := fuel) hrun with hok | hout
    · refine .inl ?_
      rw [runProgramM_eq]
      simp only [hsok, hok]
      exact h
    · refine .inr ?_
      rw [runProgramM_eq]
      simp only [hsok, hout]
  · refine .inr ?_
    rw [runProgramM_eq]
    simp only [hsout]

/-- **The readout bridge**: an ∃N-total family (every stream has a
completing fuel with a `spec`-satisfying result) yields the ∀-fuel
PARTIAL sentence — every successful completion at any fuel satisfies
`spec`. This is the designated bridge from ∃n span specs to the
partial harness sentence (clean-proof plan §W1). -/
theorem runProgramM_readout_of_total {program : Program} {name : String}
    {args : Array GoValue} {spec : Result → Prop}
    (h : ∀ ch : Choices, ∃ (N : Nat) (r₀ : Result),
      runProgramM N program name args ch = .ok r₀ ∧ spec r₀) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runProgramM fuel program name args ch = .ok r → spec r := by
  intro fuel ch r hrun
  obtain ⟨N, r₀, h₀, hspec⟩ := h ch
  have h1 := runProgramM_mono (Nat.le_max_right N fuel) hrun
  have h2 := runProgramM_mono (Nat.le_max_left N fuel) h₀
  rw [h1] at h2
  cases h2
  exact hspec

end GoLean.Surface
