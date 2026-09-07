import GoLean.GoCore.BooleanTyping
import Tests.GoCoreAdmissionFixture

namespace GoLean.GoCore.BooleanTyping.Tests
set_option maxRecDepth 4096

def booleanFunction (body : Stmt) : Func := {
  id := ⟨"F"⟩, args := #[⟨"input", .bool⟩], results := #[⟨"result", .bool⟩], body
}
def program (body : Stmt) : Program := { funcs := #[booleanFunction body] }
def accept (body : Stmt) := checkTypedBoolean (program body) "F" #[.bool true]

theorem native_argument_accepted :
    checkTypedBoolean Admission.Tests.fixture "Negate" #[.bool true] = .ok () := by
  with_unfolding_all rfl
theorem native_constant_accepted :
    checkTypedBoolean Admission.Tests.fixture "Constant" #[] = .ok () := by
  with_unfolding_all rfl

/-- The earlier admission counterexample is rejected for its unbound read,
before its additional missing-return error can obscure the cause. -/
theorem old_unbound_rejected :
    checkTypedBoolean { funcs := #[{
      id := ⟨"F"⟩, args := #[],
      results := #[⟨"result", .bool⟩], body := .assign (.var "result") (.var "missing") }] }
      "F" #[] = .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem unbound_write_rejected :
    accept (.seqn #[.assign (.var "missing") (.var "input"), .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem use_before_declaration_rejected :
    accept (.seqn #[.assign (.var "result") (.var "later"),
      .initialization ⟨"later", .bool⟩, .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem zero_local_and_result_accepted :
    accept (.seqn #[.initialization ⟨"zero", .bool⟩,
      .assign (.var "result") (.or (.var "zero") (.var "result")), .returnStmt]) =
      .ok () := by with_unfolding_all rfl

theorem untouched_result_accepted : accept .returnStmt = .ok () := by
  with_unfolding_all rfl

theorem same_scope_duplicate_rejected :
    accept (.seqn #[.initialization ⟨"x", .bool⟩, .initialization ⟨"x", .bool⟩,
      .returnStmt]) = .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem parameter_redeclaration_rejected :
    accept (.seqn #[.initialization ⟨"input", .bool⟩, .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem result_redeclaration_rejected :
    accept (.seqn #[.initialization ⟨"result", .bool⟩, .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem preallocated_duplicate_rejected :
    accept (.block #[⟨"x", .bool⟩, ⟨"x", .bool⟩] #[.returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem preallocated_then_initialization_duplicate_rejected :
    accept (.block #[⟨"x", .bool⟩] #[.initialization ⟨"x", .bool⟩, .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem nested_block_shadowing_accepted :
    accept (.seqn #[.initialization ⟨"x", .bool⟩,
      .assign (.var "x") (.var "input"),
      .block #[⟨"x", .bool⟩] #[.assign (.var "x") (.not (.var "x"))],
      .assign (.var "result") (.var "x"), .returnStmt]) = .ok () := by
  with_unfolding_all rfl

theorem escaped_block_local_rejected :
    accept (.seqn #[.block #[⟨"x", .bool⟩] #[],
      .assign (.var "result") (.var "x"), .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

/-- Regression for Machine.seqCont's same-environment splicing rule. -/
theorem nested_sequence_binding_visible :
    accept (.seqn #[.seqn #[.initialization ⟨"x", .bool⟩],
      .assign (.var "result") (.var "x"), .returnStmt]) = .ok () := by
  with_unfolding_all rfl

theorem nested_sequence_duplicate_rejected :
    accept (.seqn #[.seqn #[.initialization ⟨"x", .bool⟩],
      .initialization ⟨"x", .bool⟩, .returnStmt]) =
      .error (.scopedBody ⟨"F"⟩) := by with_unfolding_all rfl

theorem bare_initialization_outside_profile :
    checkTypedBoolean { funcs := #[{
      id := ⟨"F"⟩, args := #[], results := #[],
      body := .initialization ⟨"x", .bool⟩ }] } "F" #[] =
      .error (.unsupportedPlacement ⟨"F"⟩) := by with_unfolding_all rfl

theorem direct_branch_initialization_outside_profile :
    accept (.seqn #[.ifThenElse (.var "input") (.initialization ⟨"x", .bool⟩)
      (.seqn #[]), .returnStmt]) =
      .error (.unsupportedPlacement ⟨"F"⟩) := by with_unfolding_all rfl

theorem branch_exported_binding_outside_profile :
    accept (.seqn #[.ifThenElse (.var "input")
      (.seqn #[.initialization ⟨"x", .bool⟩]) (.seqn #[]), .returnStmt]) =
      .error (.unsupportedPlacement ⟨"F"⟩) := by with_unfolding_all rfl

theorem both_branches_return_accepted :
    accept (.ifThenElse (.var "input")
      (.block #[] #[.assign (.var "result") (.boolLit true), .returnStmt])
      (.block #[] #[.assign (.var "result") (.boolLit false), .returnStmt])) = .ok () := by
  with_unfolding_all rfl

theorem branch_fallthrough_rejected :
    accept (.ifThenElse (.var "input") .returnStmt (.seqn #[])) =
      .error (.missingReturn ⟨"F"⟩) := by with_unfolding_all rfl

theorem assignment_fallthrough_rejected :
    accept (.assign (.var "result") (.var "input")) =
      .error (.missingReturn ⟨"F"⟩) := by with_unfolding_all rfl

theorem nonterminal_tail_rejected :
    accept (.seqn #[.returnStmt, .assign (.var "result") (.var "input")]) =
      .error (.missingReturn ⟨"F"⟩) := by with_unfolding_all rfl

theorem resultless_fallthrough_accepted :
    checkTypedBoolean { funcs := #[{
      id := ⟨"F"⟩, args := #[], results := #[],
      body := .seqn #[] }] } "F" #[] = .ok () := by with_unfolding_all rfl

theorem duplicate_parameter_result_rejected :
    checkTypedBoolean { funcs := #[{
      id := ⟨"F"⟩, args := #[⟨"x", .bool⟩],
      results := #[⟨"x", .bool⟩], body := .returnStmt }] } "F" #[.bool true] =
      .error (.duplicateSignatureBinding ⟨"F"⟩) := by with_unfolding_all rfl

/-- These repeated keys can come from valid Go blank parameters. This is
an explicit storage-key profile restriction, not a Go source-error claim. -/
theorem repeated_blank_parameter_keys_outside_profile :
    checkTypedBoolean { funcs := #[{
      id := ⟨"F"⟩,
      args := #[⟨"_", .bool⟩, ⟨"_", .bool⟩], results := #[],
      body := .returnStmt }] } "F" #[.bool true, .bool false] =
      .error (.duplicateSignatureBinding ⟨"F"⟩) := by with_unfolding_all rfl

theorem unreachable_malformed_function_rejected :
    checkTypedBoolean { funcs := #[(booleanFunction .returnStmt),
      { id := ⟨"Unused"⟩, args := #[], results := #[],
        body := .assign (.var "missing") (.boolLit true) }] }
      "F" #[.bool true] = .error (.scopedBody ⟨"Unused"⟩) := by with_unfolding_all rfl

theorem initial_value_type_rejected :
    checkTypedBoolean (program .returnStmt) "F" #[.int 0 .int] =
      .error (.boundary .initialArgumentTypes) := by with_unfolding_all rfl

theorem result_type_outside_profile :
    checkTypedBoolean { funcs := #[{
      id := ⟨"F"⟩, args := #[],
      results := #[⟨"result", .int .int⟩], body := .returnStmt }] } "F" #[] =
      .error (.boundary .booleanSyntaxPolicy) := by with_unfolding_all rfl

/-- Generic families: these facts are not tied to the fixture artifact. -/
theorem zero_result_function_typed (id result : String) :
    FunctionTyped {
      id := ⟨id⟩, args := #[], results := #[⟨result, .bool⟩],
      body := .returnStmt } := by
  simp [FunctionTyped, Admission.BoolParams, SignatureDistinct,
    StmtTyped, ← checkStmt_iff, checkStmt, ReturnPolicy, ← checkReturns_iff,
    checkReturns]

theorem argument_function_typed (id arg result : String) (different : arg ≠ result)
    (negate : Bool) :
    FunctionTyped {
      id := ⟨id⟩, args := #[⟨arg, .bool⟩], results := #[⟨result, .bool⟩],
      body := .seqn #[.assign (.var result)
        (.and (.var arg) (.not (.boolLit negate))), .returnStmt] } := by
  simp [FunctionTyped, Admission.BoolParams, SignatureDistinct, different,
    StmtTyped, ← checkStmt_iff, checkStmt, checkStmts, checkExpr,
    Bound, initialContext, ReturnPolicy, ← checkReturns_iff,
    checkReturns, checkReturnsList]

theorem sequence_declaration_effect (Γ : Context) (x : String) :
    afterStmts Γ [.seqn #[.initialization ⟨x, .bool⟩]] = declare Γ x := rfl

theorem block_declaration_effect (Γ : Context) (x : String) :
    afterStmt Γ (.block #[⟨x, .bool⟩] #[]) = Γ := rfl

end GoLean.GoCore.BooleanTyping.Tests
