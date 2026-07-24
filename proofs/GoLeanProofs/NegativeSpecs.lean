import GoLean.GoCore.MachineSound
import GoLeanProofs.Inversions

/-!
# Negative proof instances (R3 rewrite over the fine-grained machine)

Provable NEGATIONS, checked by the ordinary build: guards against
spec-layer trivialization (`docs/2026-07-21_widening-loop.md`). The old
`ExprR` pins move to their machine analogues: unbound-variable stuckness
now bites at the RESOLUTION step (the machine defers resolution to the
`evalE` configuration — the assign statement itself steps, its target
evaluation cannot), and the divide-by-zero premise pin moves into the
shared op table (`applyStrictOp`), which both the relation's apply rules
and `stepFn` consume.
-/

namespace GoLean.GoCore.NegativeSpecs

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- **Stuckness pin:** resolving an unbound variable has NO step — the
machine fails closed at the resolution configuration. -/
theorem unbound_ref_stuck (σ : ExecState) (k : Cont) :
    ¬ ∃ (c' : Config) (σ' : ExecState),
      Step (.evalE (.ref "x") [] k) σ c' σ' := by
  rintro ⟨c', σ', hstep⟩
  cases hstep with
  | evalRef hl => simp [LocalEnv.lookup] at hl
  | evalStrict hplan => simp [strictPlan] at hplan
  | evalStrictNullary hplan _ => simp [strictPlan] at hplan
  | evalStrictNullaryPanic hplan _ => simp [strictPlan] at hplan

/-- **Stuckness pin:** reading an unbound variable has NO step. -/
theorem unbound_var_stuck (σ : ExecState) (k : Cont) :
    ¬ ∃ (c' : Config) (σ' : ExecState),
      Step (.evalE (.var "x") [] k) σ c' σ' := by
  rintro ⟨c', σ', hstep⟩
  cases hstep with
  | evalVar hl _ => simp [LocalEnv.lookup] at hl
  | evalStrict hplan => simp [strictPlan] at hplan
  | evalStrictNullary hplan _ => simp [strictPlan] at hplan
  | evalStrictNullaryPanic hplan _ => simp [strictPlan] at hplan

/-- **Stuckness pin:** the terminal value configuration is irreducible. -/
theorem terminal_stuck (σ : ExecState) :
    ¬ ∃ (c' : Config) (σ' : ExecState), Step (.next .stop) σ c' σ' := by
  rintro ⟨c', σ', hstep⟩
  cases hstep

/-- **Premise pin (divide-by-zero):** the zero-divisor check in the shared
op table is load-bearing — dividing by a nonzero literal does not panic.
If `applyStrictOp`'s `.div` arm ever loses its divisor check's guard
direction, this breaks. -/
theorem div_nonzero_no_panic (σ : ExecState) (msg : String) :
    applyStrictOp σ .div [.int 1 .int, .int 1 .int]
      ≠ .error (.panic msg) := by
  intro h
  have h1 : IntKind.compatibleResult .int .int = some .int := rfl
  simp [applyStrictOp, intBinaryResult, valueAsIntValue, valueAsInt, h1,
    Bind.bind, Except.bind] at h

/-- ... and the step-level corollary: the `div` apply step from nonzero
literals cannot reach `panicked`. -/
theorem div_nonzero_apply_no_panic (σ σ' : ExecState) (msg : String)
    (env : LocalEnv) (k : Cont) :
    ¬ Step (.retV (.int 1 .int) (.strictK .div [.int 1 .int] [] env k)) σ
        (.panicked msg) σ' := by
  intro hstep
  cases hstep with
  | strictApplyPanic happly =>
      exact div_nonzero_no_panic σ msg (by simpa using happly)

end GoLean.GoCore.NegativeSpecs
