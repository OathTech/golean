import Tests.RecoveryTyping

namespace GoLean.GoCore.RecoveryTyping.Tests

set_option maxRecDepth 8192

def booleanPanic : Func := { emptyEntry with
  body := .block #[] #[.panicStmt (.toInterface payloadTy .bool (.boolLit true))] }

/-- `panic(true)` is valid Go, excluded by this explicit string-payload profile. -/
theorem valid_boolean_panic_is_outside_profile :
    checkRecovery { funcs := #[booleanPanic] } "entry" #[] =
      .error (.statementProfile ⟨"entry"⟩) := by
  with_unfolding_all rfl

/-- The same admitted Boolean assignment surface has an unbound destination. -/
theorem malformed_assignment_is_scoped_failure :
    checkRecovery { funcs := #[{emptyEntry with
      body := .block #[] #[.assign (.var "missing") (.boolLit true)]}] } "entry" #[] =
      .error (.body ⟨"entry"⟩) := by
  with_unfolding_all rfl

theorem malformed_bare_initialization_is_placement_failure :
    checkRecovery { funcs := #[{emptyEntry with body := .initialization ⟨"x", .bool⟩}] }
      "entry" #[] = .error (.declarationPlacement ⟨"entry"⟩) := by
  with_unfolding_all rfl

theorem malformed_boolean_operand_is_scoped_failure :
    checkRecovery { funcs := #[{emptyEntry with body := .block #[] #[
      .ifThenElse (.stringLit ⟨#[120]⟩) (.seqn #[]) (.seqn #[])]}] }
      "entry" #[] = .error (.body ⟨"entry"⟩) := by
  with_unfolding_all rfl

/-- Surface/placement diagnostics are logical consequences, not new admission clauses. -/
theorem diagnostic_checks_do_not_narrow {p : Program} {name : String} {args : Array GoValue}
    (h : RecoveryAdmission p name args) : checkRecovery p name args = .ok () :=
  checkRecovery_complete h

end GoLean.GoCore.RecoveryTyping.Tests
