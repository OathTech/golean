import GoLean.GoCore.MultiSound

/-! A proof-only trace for the actual output-preserving pool driver.
It retains detector state, the main-exit choice, and the output prefix.
`front` names the driver's pre-fuel classification; `unfold_driver` checks
that factoring against the existing driver. Nothing here replaces it.
-/
namespace GoLean.Semantics.Pool

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)
open GoCore GoCore.Machine

abbrev Result := GoString × Except Stop (Store × Choices)

/-- Left = completed; right = the stream at the upcoming pool step.
The main-exit window can consume a choice even at zero fuel. -/
def front (m : MultiConfig) (ch : Choices) :
    Except Stop ((Store × Choices) ⊕ Choices) :=
  if m.threads.isEmpty then .error (.internal "thread pool without a main goroutine")
  else match m.panicMsg? with
  | some msg => .error (.panic msg)
  | none => match m.mainOutcome? with
    | some s => match runnableIdxs ctx m.shared m.threads with
      | [] => .ok (.inl (s, ch))
      | _ :: _ =>
        let (pick, ch') := Choices.consumeAt .l5ExitWindow 2 ch
        if pick == 0 then .ok (.inl (s, ch')) else .ok (.inr ch')
    | none => if (runnableIdxs ctx m.shared m.threads).isEmpty
      then .error .deadlock else .ok (.inr ch)

variable {ctx}
theorem unfold_driver (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) (acc : GoString) :
    execProgLoopOut ctx fuel m r ch acc =
      match front ctx m ch with
      | .error e => (acc, .error e)
      | .ok (.inl res) => (acc, .ok res)
      | .ok (.inr next) => match fuel with
        | 0 => (acc, .error .fuelOut)
        | n + 1 => match stepMulti ctx m next with
          | .error e => (acc, .error e)
          | .ok (m', ch', ev) => match raceUpdate ctx m.shared m.threads ev m' r with
            | .error e => (acc, .error e)
            | .ok r' => execProgLoopOut ctx n m' r' ch' (ev.out.foldl GoString.append acc) := by
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

variable (ctx)
/-- Fuel is a bound, not a Go event. Failure constructors preserve the
existing driver's pre-step output policy, including detector rejection. -/
inductive Run : Nat → MultiConfig → RaceState → Choices → GoString → Result → Prop where
  | stop : front ctx m ch = .error e → Run fuel m r ch acc (acc, .error e)
  | done : front ctx m ch = .ok (.inl res) → Run fuel m r ch acc (acc, .ok res)
  | exhausted : front ctx m ch = .ok (.inr next) → Run 0 m r ch acc (acc, .error .fuelOut)
  | stepError : front ctx m ch = .ok (.inr next) → stepMulti ctx m next = .error e →
      Run (n + 1) m r ch acc (acc, .error e)
  | raceError : front ctx m ch = .ok (.inr next) → stepMulti ctx m next = .ok (m', ch', ev) →
      raceUpdate ctx m.shared m.threads ev m' r = .error e →
      Run (n + 1) m r ch acc (acc, .error e)
  | step : front ctx m ch = .ok (.inr next) → stepMulti ctx m next = .ok (m', ch', ev) →
      raceUpdate ctx m.shared m.threads ev m' r = .ok r' →
      Run n m' r' ch' (ev.out.foldl GoString.append acc) result →
      Run (n + 1) m r ch acc result

variable {ctx}
theorem run_iff {fuel m r ch acc result} :
    execProgLoopOut ctx fuel m r ch acc = result ↔ Run ctx fuel m r ch acc result := by
  constructor
  · intro h
    induction fuel generalizing m r ch acc with
    | zero =>
      rw [unfold_driver] at h
      cases hf : front ctx m ch with
      | error e => simp only [hf] at h; subst result; exact .stop hf
      | ok v => cases v with
        | inl res => simp only [hf] at h; subst result; exact .done hf
        | inr next => simp only [hf] at h; subst result; exact .exhausted hf
    | succ n ih =>
      rw [unfold_driver] at h
      cases hf : front ctx m ch with
      | error e => simp only [hf] at h; subst result; exact .stop hf
      | ok v => cases v with
        | inl res => simp only [hf] at h; subst result; exact .done hf
        | inr next =>
          simp only [hf] at h
          cases hs : stepMulti ctx m next with
          | error e => simp only [hs] at h; subst result; exact .stepError hf hs
          | ok v =>
            obtain ⟨m', ch', ev⟩ := v
            simp only [hs] at h
            cases hr : raceUpdate ctx m.shared m.threads ev m' r with
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
    (∃ fuel ch, execProgLoopOut ctx fuel m r ch acc = result) ↔
    ∃ fuel ch, Run ctx fuel m r ch acc result := by
  simp only [run_iff]

variable (ctx)
/-- The current core exports `StepM`, but not a named `StepsM` closure. -/
inductive PoolSteps : MultiConfig → MultiConfig → Prop where
  | refl : PoolSteps m m
  | head : StepM ctx m m' tr → PoolSteps m' mf → PoolSteps m mf

variable {ctx}
/-- Erase a successful detector-checked trace to current pool reachability.
The converse is deliberately not asserted: erasure loses the stream,
detector, output and exit-window policy. -/
theorem Run.success_reaches (h : Run ctx fuel m r ch acc result) :
    ∀ sf chf, result.2 = .ok (sf, chf) →
      ∃ mf ch₁, PoolSteps ctx m mf ∧ front ctx mf ch₁ = .ok (.inl (sf, chf)) := by
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

end GoLean.Semantics.Pool
