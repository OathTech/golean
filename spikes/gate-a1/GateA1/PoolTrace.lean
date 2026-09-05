import GoLean.GoCore.MultiSound

/-! A proof-only trace for the actual output-preserving pool driver.
It retains detector state, the main-exit choice, and the output prefix.
`front` names the driver's pre-fuel classification; `unfold_driver` checks
that factoring against the existing driver. Nothing here replaces it.
-/
namespace GoLean.GateA1.Pool
open GoCore GoCore.Machine

abbrev Result := GoString × Except Stop (ExecState × Choices)

/-- Left = completed; right = the stream at the upcoming pool step.
The main-exit window can consume a choice even at zero fuel. -/
def front (m : MultiConfig) (ch : Choices) :
    Except Stop ((ExecState × Choices) ⊕ Choices) :=
  if m.threads.isEmpty then .error (.internal "thread pool without a main goroutine")
  else match m.panicMsg? with
  | some msg => .error (.panic msg)
  | none => match m.mainOutcome? with
    | some s => match runnableIdxs m.shared m.threads with
      | [] => .ok (.inl (s, ch))
      | _ :: _ =>
        let (pick, ch') := Choices.consumeAt .l5ExitWindow 2 ch
        if pick == 0 then .ok (.inl (s, ch')) else .ok (.inr ch')
    | none => if (runnableIdxs m.shared m.threads).isEmpty
      then .error .deadlock else .ok (.inr ch)

theorem unfold_driver (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) :
    execProgLoopOut fuel m r ch acc =
      match front m ch with
      | .error e => (acc, .error e)
      | .ok (.inl res) => (acc, .ok res)
      | .ok (.inr next) => match fuel with
        | 0 => (acc, .error .fuelOut)
        | n + 1 => match stepMulti m next with
          | .error e => (acc, .error e)
          | .ok (m', ch', ev) => match raceUpdate m.shared m.threads ev m' r with
            | .error e => (acc, .error e)
            | .ok r' => execProgLoopOut n m' r' ch' (ev.out.foldl GoString.append acc) := by
  rw [execProgLoopOut.eq_def]
  unfold front
  dsimp only
  split
  · rfl
  · split
    · simp_all [throw, throwThe, MonadExceptOf.throw]
    · split
      · split
        · simp_all
        · split <;> simp_all [throw, throwThe, MonadExceptOf.throw] <;> cases fuel <;> rfl
      · split <;> simp_all [throw, throwThe, MonadExceptOf.throw] <;> cases fuel <;> rfl

/-- Fuel is a bound, not a Go event. Failure constructors preserve the
existing driver's pre-step output policy, including detector rejection. -/
inductive Run : Nat → MultiConfig → RaceState → Choices → GoString → Result → Prop where
  | stop : front m ch = .error e → Run fuel m r ch acc (acc, .error e)
  | done : front m ch = .ok (.inl res) → Run fuel m r ch acc (acc, .ok res)
  | exhausted : front m ch = .ok (.inr next) → Run 0 m r ch acc (acc, .error .fuelOut)
  | stepError : front m ch = .ok (.inr next) → stepMulti m next = .error e →
      Run (n + 1) m r ch acc (acc, .error e)
  | raceError : front m ch = .ok (.inr next) → stepMulti m next = .ok (m', ch', ev) →
      raceUpdate m.shared m.threads ev m' r = .error e →
      Run (n + 1) m r ch acc (acc, .error e)
  | step : front m ch = .ok (.inr next) → stepMulti m next = .ok (m', ch', ev) →
      raceUpdate m.shared m.threads ev m' r = .ok r' →
      Run n m' r' ch' (ev.out.foldl GoString.append acc) result →
      Run (n + 1) m r ch acc result

theorem run_iff {fuel m r ch acc result} :
    execProgLoopOut fuel m r ch acc = result ↔ Run fuel m r ch acc result := by
  constructor
  · intro h
    induction fuel generalizing m r ch acc with
    | zero =>
      rw [unfold_driver] at h
      cases hf : front m ch with
      | error e => simp only [hf] at h; subst result; exact .stop hf
      | ok v => cases v with
        | inl res => simp only [hf] at h; subst result; exact .done hf
        | inr next => simp only [hf] at h; subst result; exact .exhausted hf
    | succ n ih =>
      rw [unfold_driver] at h
      cases hf : front m ch with
      | error e => simp only [hf] at h; subst result; exact .stop hf
      | ok v => cases v with
        | inl res => simp only [hf] at h; subst result; exact .done hf
        | inr next =>
          simp only [hf] at h
          cases hs : stepMulti m next with
          | error e => simp only [hs] at h; subst result; exact .stepError hf hs
          | ok v =>
            obtain ⟨m', ch', ev⟩ := v
            simp only [hs] at h
            cases hr : raceUpdate m.shared m.threads ev m' r with
            | error e => simp only [hr] at h; subst result; exact .raceError hf hs hr
            | ok r' =>
              simp only [hr] at h
              exact .step hf hs hr (ih h)
  · intro h
    induction h with
    | stop hf => rw [unfold_driver, hf]
    | done hf => rw [unfold_driver, hf]
    | exhausted hf => rw [unfold_driver, hf]
    | stepError hf hs => rw [unfold_driver, hf]; simp only [hs]
    | raceError hf hs hr => rw [unfold_driver, hf]; simp only [hs, hr]
    | step hf hs hr _ ih => rw [unfold_driver, hf]; simpa only [hs, hr] using ih

/-- Correct existential-stream observation contract, over this finite,
detector-checked, output-bearing trace rather than bare `StepsM`. -/
theorem exists_run_iff {m r acc result} :
    (∃ fuel ch, execProgLoopOut fuel m r ch acc = result) ↔
    ∃ fuel ch, Run fuel m r ch acc result := by
  simp only [run_iff]

/-- The current core exports `StepM`, but not a named `StepsM` closure. -/
inductive PoolSteps : MultiConfig → MultiConfig → Prop where
  | refl : PoolSteps m m
  | head : StepM m m' → PoolSteps m' mf → PoolSteps m mf

/-- Erase a successful detector-checked trace to current pool reachability.
The converse is deliberately not asserted: erasure loses the stream,
detector, output and exit-window policy. -/
theorem Run.success_reaches (h : Run fuel m r ch acc result) :
    ∀ sf chf, result.2 = .ok (sf, chf) →
      ∃ mf ch₁, PoolSteps m mf ∧ front mf ch₁ = .ok (.inl (sf, chf)) := by
  induction h with
  | stop _ => intro _ _ h; cases h
  | done hf =>
    intro sf chf h
    cases h
    exact ⟨_, _, .refl, hf⟩
  | exhausted _ => intro _ _ h; cases h
  | stepError _ _ => intro _ _ h; cases h
  | raceError _ _ _ => intro _ _ h; cases h
  | step _ hs _ _ ih =>
    intro sf chf h
    obtain ⟨mf, ch₁, steps, hf⟩ := ih sf chf h
    exact ⟨mf, ch₁, .head (stepMulti_sound hs) steps, hf⟩

end GoLean.GateA1.Pool
