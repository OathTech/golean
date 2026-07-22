import GoLean.GoCore.Correspondence
import GoLeanProofs.Inversions

/-!
# Negative proof instances (the widening loop's step-0 second half)

Provable NEGATIONS, checked by the ordinary build: guards against
spec-layer trivialization — the failure mode where the relation or a law
weakens enough that wrong claims become provable while every other gate
stays green (`docs/2026-07-21_widening-loop.md`). First instances:
stuckness pins (the relation's fail-closed behavior as theorems) and a
premise pin.
-/

namespace GoLean.GoCore.NegativeSpecs

open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.Iris

/-- **Stuckness pin:** an assignment to an unbound variable has NO step —
fail-closed is a theorem, not a hope. If a relation edit ever makes
unbound-variable programs progress, this breaks the build. -/
theorem unbound_assign_stuck (σ : ExecState) (e : Expr) :
    ¬ ∃ (c' : Config) (σ' : ExecState),
      Step (.exec (.assign (.var "x") e) [] .stop) σ c' σ' := by
  rintro ⟨c', σ', hstep⟩
  cases hstep with
  | assign hA _ _ =>
      cases hA with | var hl => simp [LocalEnv.lookup] at hl
  | assignTargetPanic hA => cases hA
  | assignValuePanic hA _ =>
      cases hA with | var hl => simp [LocalEnv.lookup] at hl
  | assignStorePanic hA _ _ =>
      cases hA with | var hl => simp [LocalEnv.lookup] at hl

/-- **Stuckness pin:** the terminal value configuration is irreducible. -/
theorem terminal_stuck (σ : ExecState) :
    ¬ ∃ (c' : Config) (σ' : ExecState), Step (.next .stop) σ c' σ' := by
  rintro ⟨c', σ', hstep⟩
  cases hstep

/-- **Premise pin (`divByZero`):** the zero-divisor premise is load-bearing —
division by a nonzero literal does NOT panic-derive. If `divByZero` ever
loses its zero requirement, this breaks. -/
theorem div_nonzero_no_panic (σ : ExecState) (env : LocalEnv) (msg : String) :
    ¬ ExprR env σ (.div (.intLit 1 .int) (.intLit 1 .int)) (.panic msg) := by
  intro h
  generalize he : Expr.div (.intLit 1 .int) (.intLit 1 .int) = e at h
  cases h with
  | divByZero hl hr =>
      injection he with h1 h2
      subst h2
      have hd := exprR_intLit_det hr
      injection hd with hv hs
      injection hv with hn hk
      exact absurd hn (by decide)
  | binPanicLeft mk hmk hp =>
      rcases hmk with rfl | rfl | rfl | rfl <;>
        first
          | exact Expr.noConfusion he
          | (injection he with h1 h2
             subst h1
             exact ExprOut.noConfusion (exprR_intLit_det hp))
  | binPanicRight mk hmk hv hp =>
      rcases hmk with rfl | rfl | rfl | rfl <;>
        first
          | exact Expr.noConfusion he
          | (injection he with h1 h2
             subst h2
             exact ExprOut.noConfusion (exprR_intLit_det hp))
  | _ => exact Expr.noConfusion he

end GoLean.GoCore.NegativeSpecs
