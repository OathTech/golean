import GoLean.GoCore.RecoveryWalk
import GoLean.GoCore.MachineSound

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

structure StoreExtension (world next : World) (s t : ExecState) : Prop where
  world : Extends world next
  heap : HeapTyped next t
  context : BooleanRuntime.SameContext s t

theorem StoreExtension.refl {world s} (heap : HeapTyped world s) :
    StoreExtension world world s s := ⟨.refl world, heap, rfl⟩

/-- Uniform one-step progress with structural preservation. This is a
theorem goal, never a field of static admission or the runtime invariant. -/
def Advances (world : World) (fs : Array Func) (s : ExecState) (c : Config) : Prop :=
  ∀ ch, ∃ next c' t, stepFn s c ch = .ok (c', t, ch) ∧
    StoreExtension world next s t ∧ Control next fs c'

theorem advances_same {world fs s c c'} (heap : HeapTyped world s)
    (control : Control world fs c')
    (step : ∀ ch, stepFn s c ch = .ok (c', s, ch)) : Advances world fs s c :=
  fun ch => ⟨world, c', s, step ch, .refl heap, control⟩

theorem expression_value_advances {world fs Γ e sort env k s}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env) (ht : ExprTyped Γ e sort)
    (hk : ValueCont world fs (.value sort) k) : Advances world fs s (.evalE e env k) := by
  cases ht with
  | var hn =>
    obtain ⟨loc, v, hl, load, hv⟩ := he.load heap hn
    exact advances_same heap (.ret (.value hv) hk)
      (fun _ => by simp [stepFn, hl, load, Bind.bind, Except.bind])
  | boolean b => exact advances_same heap (.ret (.value (.boolean b)) hk) (fun _ => rfl)
  | string bytes => exact advances_same heap (.ret (.value (.string bytes)) hk) (fun _ => rfl)
  | nil hn =>
    exact advances_same heap (.ret (.value .nil) hk)
      (fun _ => by simp [stepFn, strictPlan, apply_nil hn, toResult]; rfl)
  | not ht =>
    exact advances_same heap (.eval he (.value ht)
      (.strict he (.plain .not) .nil .nil hk)) (fun _ => rfl)
  | and hl hr =>
    exact advances_same heap (.eval he (.value hl) (.and he hr hk)) (fun _ => rfl)
  | or hl hr => exact advances_same heap (.eval he (.value hl) (.or he hr hk)) (fun _ => rfl)
  | ref hn =>
    obtain ⟨loc, hl, a, rfl, ha⟩ := he.has hn
    exact advances_same heap (.ret (.value (.root ha)) hk) (fun _ => by simp [stepFn, hl])
  | deref ht =>
    exact advances_same heap (.eval he (.value ht)
      (.strict he (.plain .deref) .nil .nil hk)) (fun _ => rfl)
  | box hty ht =>
    exact advances_same heap (.eval he (.value ht)
      (.strict he (.plain (.box hty)) .nil .nil hk)) (fun _ => rfl)
  | recover =>
    obtain ⟨v, next, run, hv, hk⟩ := hk.recover
    exact advances_same heap (.ret hv hk) (fun _ => by simp [stepFn, run])
  | eqBool hty hl hr =>
    cases hty
    exact advances_same heap (.eval he (.value hl)
      (.strict he (.plain .eqBoolean) .nil (.cons (.value hr) .nil) hk)) (fun _ => rfl)
  | neqBool hty hl hr =>
    cases hty
    exact advances_same heap (.eval he (.value hl)
      (.strict he (.plain .neqBoolean) .nil (.cons (.value hr) .nil) hk)) (fun _ => rfl)
  | eqNil hty hl hr _ =>
    exact advances_same heap (.eval he (.value hl)
      (.strict he (.plain (.eqPayload hty)) .nil (.cons (.value hr) .nil) hk)) (fun _ => rfl)
  | neqNil hty hl hr _ =>
    exact advances_same heap (.eval he (.value hl)
      (.strict he (.plain (.neqPayload hty)) .nil (.cons (.value hr) .nil) hk)) (fun _ => rfl)

theorem expression_advances {world fs Γ e kind env k s}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env) (ht : Expression Γ e kind)
    (hk : ValueCont world fs kind k) : Advances world fs s (.evalE e env k) := by
  cases ht with
  | value ht => exact expression_value_advances heap he ht hk
  | typed ht =>
    cases ht with
    | typed hty ht => exact expression_value_advances heap he ht (.coerce (.toAt hty) hk)
  | addressRef hn =>
    obtain ⟨loc, hl, ha⟩ := he.has hn
    exact advances_same heap (.ret (.address ha) hk) (fun _ => by simp [stepFn, hl])
  | addressExpr ht => exact expression_value_advances heap he ht (.coerce .rootAddress hk)
  | boxed ht =>
    cases ht with
    | stringBox hty ht =>
      exact advances_same heap (.eval he (.value ht)
        (.strict he (.boxed hty) .nil .nil hk)) (fun _ => rfl)
  | @closure fid caps ps ht =>
    cases hc : caps.toList with
    | nil =>
      rw [hc] at ht
      cases ht
      exact advances_same heap (.ret (.closure .nil) hk)
        (fun _ => by simp [stepFn, strictPlan, hc, applyStrictOp, toResult]; rfl)
    | cons e rest =>
      rw [hc] at ht
      cases ht with
      | @cons _ _ p ps head tail =>
        exact advances_same heap (.eval he (.typed head)
          (.strict (done := []) (doneKinds := []) he (.closure fid (p :: ps))
            .nil (Expressions.arguments tail) hk))
          (fun _ => by simp [stepFn, strictPlan, hc])

end GoLean.GoCore.RecoveryRuntime
