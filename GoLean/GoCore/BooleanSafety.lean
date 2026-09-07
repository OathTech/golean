import GoLean.GoCore.BooleanPreservation
import GoLean.GoCore.BooleanProgress

/-! Reachability, actual bounded drivers, and output for the Boolean profile.
Fuel exhaustion is a separate alternative throughout; these contracts do not
assume or claim a general termination bound. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

theorem Inv.steps {context results s c t c'} (h : Inv context results s c)
    (hs : Steps c s c' t) : Inv context results t c' := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact ih.step hstep

theorem Inv.reachable_progress {context results s c t c'} (h : Inv context results s c)
    (hs : Steps c s c' t) :
    c' = .next .stop ∨ ∃ c'' u, Step c' t c'' u := (h.steps hs).progress

theorem Inv.iter {context results s c t c' n ch ch'} (h : Inv context results s c)
    (hs : stepFnIter n s c ch = .ok (c', t, ch')) : Inv context results t c' :=
  h.steps (stepFnIter_sound hs)

theorem Inv.loop_ok_or_fuelOut {context results s c} (h : Inv context results s c)
    (fuel : Nat) (ch : Choices) :
    (∃ t ch', execStmtLoop fuel s c ch = .ok (t, ch')) ∨
    execStmtLoop fuel s c ch = .error .fuelOut :=
  execStmtLoop_ok_or_fuelOut (fun _ _ => h.reachable_progress) h.machineWf fuel ch

theorem Inv.loop_readout {context results s c fuel ch t ch'} (h : Inv context results s c)
    (hr : execStmtLoop fuel s c ch = .ok (t, ch')) :
    ∃ bs : List Bool, loadMany t results = .ok (bs.map GoValue.bool) ∧ bs.length = results.length :=
  (h.steps (execStmtLoop_sound_normal hr)).readout

/-- The two existing sequential drivers have identical guard/step behavior.
This equality transports safety to `runProgramM`'s actual `runConfig` path. -/
theorem runConfig_eq_loop (fuel : Nat) (s : ExecState) (c : Config) (ch : Choices) :
    runConfig fuel s c ch = execStmtLoop fuel s c ch := by
  induction fuel generalizing s c ch with
  | zero => cases c <;> try rfl
            case next k => cases k <;> rfl
  | succ fuel ih =>
      rw [runConfig.eq_def, execStmtLoop_unfold]
      split <;> try rfl
      simp only [ih]
      rfl

theorem Inv.run_ok_or_fuelOut {context results s c} (h : Inv context results s c)
    (fuel : Nat) (ch : Choices) :
    (∃ t ch', runConfig fuel s c ch = .ok (t, ch')) ∨
    runConfig fuel s c ch = .error .fuelOut := by
  simpa only [runConfig_eq_loop] using h.loop_ok_or_fuelOut fuel ch

theorem Inv.run_readout {context results s c fuel ch t ch'} (h : Inv context results s c)
    (hr : runConfig fuel s c ch = .ok (t, ch')) :
    ∃ bs : List Bool, loadMany t results = .ok (bs.map GoValue.bool) ∧ bs.length = results.length :=
  (h.steps (runConfig_sound hr)).readout

theorem Inv.run_no_refusal {context results s c} (h : Inv context results s c)
    (fuel : Nat) (ch : Choices) (r : Refusal) :
    runConfig fuel s c ch ≠ .error (.refusal r) := by
  rcases h.run_ok_or_fuelOut fuel ch with ⟨t, ch', hr⟩ | hr <;> rw [hr] <;> simp

theorem Control.silent {root roots c} (h : Control root roots c) : printOut? c = none := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Inv.reachable_silent {context results s c t c'} (h : Inv context results s c)
    (hs : Steps c s c' t) : printOut? c' = none := (h.steps hs).control.silent

theorem Inv.loop_choices {context results s c fuel ch t ch'} (h : Inv context results s c)
    (hr : execStmtLoop fuel s c ch = .ok (t, ch')) : ch' = ch := by
  induction fuel generalizing s c ch with
  | zero =>
      rw [execStmtLoop_unfold] at hr
      split at hr
      · cases hr; rfl
      all_goals contradiction
  | succ fuel ih =>
      rcases control_advances h.heap h.control with rfl | ha
      · cases hr; rfl
      · obtain ⟨d, u, hu, _, _⟩ := ha ch
        rw [execStmtLoop_step hu] at hr
        exact ih (h.step (stepFn_sound hu)) hr

theorem Inv.run_choices {context results s c fuel ch t ch'} (h : Inv context results s c)
    (hr : runConfig fuel s c ch = .ok (t, ch')) : ch' = ch :=
  h.loop_choices (by simpa only [runConfig_eq_loop] using hr)

end GoLean.GoCore.BooleanRuntime
