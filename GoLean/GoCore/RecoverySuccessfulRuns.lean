import GoLean.GoCore.RecoveryInvariant
import GoLean.GoCore.BooleanSafety

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem ValueCont.silent {world fs kind k} (h : ValueCont world fs kind k) (v : GoValue) :
    printOut? (.retV v k) = none := by
  induction h <;> first | assumption | rfl

theorem Control.silent {world fs c} (h : Control world fs c) : printOut? c = none := by
  cases h <;> try rfl
  case ret hv hk => exact hk.silent _

theorem Inv.reachable_silent {p ps results s c t c'} (h : Inv p ps results s c)
    (steps : Steps c s c' t) : printOut? c' = none := by
  obtain ⟨_, _, control, _⟩ := (h.steps steps).typed
  exact control.silent

theorem Inv.loop_readout {p ps results s c fuel ch t ch'} (h : Inv p ps results s c)
    (run : execStmtLoop fuel s c ch = .ok (t, ch')) :
    ∃ world vs, loadMany t results = .ok vs ∧ ParamsValues world ps vs ∧
      vs.length = results.length :=
  (h.steps (execStmtLoop_sound_normal run)).readout

theorem Inv.run_readout {p ps results s c fuel ch t ch'} (h : Inv p ps results s c)
    (run : runConfig fuel s c ch = .ok (t, ch')) :
    ∃ world vs, loadMany t results = .ok vs ∧ ParamsValues world ps vs ∧
      vs.length = results.length := (h.steps (runConfig_sound run)).readout

theorem Inv.loop_choices {p ps results s c fuel ch t ch'} (h : Inv p ps results s c)
    (run : execStmtLoop fuel s c ch = .ok (t, ch')) : ch' = ch := by
  revert h
  fun_induction execStmtLoop fuel s c ch with
  | case1 => cases run; exact fun _ => rfl
  | case2 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case3 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case4 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case5 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case6 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case7 =>
    rename_i ih
    rw [bind_eq_ok] at run
    obtain ⟨⟨c', s', nextCh⟩, step, run⟩ := run
    intro h
    obtain ⟨world, heap, control, _⟩ := h.typed
    obtain ⟨_, _, _, heq⟩ := control_stepFn h.program h.sameContext heap control step
    exact (ih _ _ _ run (h.step (stepFn_sound step))).trans heq

theorem Inv.run_choices {p ps results s c fuel ch t ch'} (h : Inv p ps results s c)
    (run : runConfig fuel s c ch = .ok (t, ch')) : ch' = ch :=
  h.loop_choices (by simpa only [BooleanRuntime.runConfig_eq_loop] using run)

end GoLean.GoCore.RecoveryRuntime
