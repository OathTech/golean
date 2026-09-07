import GoLean.GoCore.RecoveryAdmission
import GoLean.GoCore.BooleanTyping

namespace GoLean.GoCore.RecoveryTyping.Tests

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def payloadTy : Ty := .interface ⟨"any"⟩
def boxed (bytes : GoString) : Expr := .toInterface payloadTy .string (.stringLit bytes)
def boolScope : Context := [[("x", .bool), ("result", .bool)]]

def rootReader : Func := {
  id := ⟨"reader"⟩
  args := #[⟨"root", .pointer .bool⟩, ⟨"input", .bool⟩]
  results := #[⟨"result", .bool⟩]
  body := .block #[] #[
    .assign (.var "result") (.and (.deref (.var "root") .bool) (.var "input")),
    .returnStmt]
}

theorem root_reader_typed : checkFunction #[rootReader] rootReader = .ok () := by
  with_unfolding_all rfl

theorem same_root_captured_twice :
    checkCaptures boolScope [.ref "x", .ref "x"] = true := by
  with_unfolding_all rfl

theorem direct_root_argument :
    checkDirectCall #[rootReader] boolScope #[.var "result"] ⟨"reader"⟩
      #[.ref "x", .boolLit true] = true := by
  with_unfolding_all rfl

theorem closure_prefix_and_argument :
    checkClosureCall #[rootReader] boolScope #[.var "result"] #[.boolLit true]
      (.funcVal ⟨"reader"⟩ #[.ref "x"]) = true := by
  with_unfolding_all rfl

theorem deferred_results_are_discarded :
    checkDeferredCall #[rootReader] boolScope #[.boolLit true]
      (.funcVal ⟨"reader"⟩ #[.ref "x"]) = true := by
  with_unfolding_all rfl

theorem boolean_is_not_a_capture_root :
    checkClosureCall #[rootReader] boolScope #[.var "result"] #[.boolLit true]
      (.funcVal ⟨"reader"⟩ #[.var "x"]) = false := by
  with_unfolding_all rfl

theorem nil_is_not_a_live_capture :
    checkDeferredCall #[rootReader] boolScope #[.boolLit true]
      (.funcVal ⟨"reader"⟩ #[.nil none]) = false := by
  with_unfolding_all rfl

theorem mismatched_capture_prefix :
    checkClosureCall #[{rootReader with args := #[⟨"root", .bool⟩, ⟨"input", .bool⟩]}]
      boolScope #[.var "result"] #[.boolLit true]
      (.funcVal ⟨"reader"⟩ #[.ref "x"]) = false := by
  with_unfolding_all rfl

theorem missing_explicit_argument :
    checkDeferredCall #[rootReader] boolScope #[]
      (.funcVal ⟨"reader"⟩ #[.ref "x"]) = false := by
  with_unfolding_all rfl

theorem extra_explicit_argument :
    checkDeferredCall #[rootReader] boolScope #[.boolLit true, .boolLit false]
      (.funcVal ⟨"reader"⟩ #[.ref "x"]) = false := by
  with_unfolding_all rfl

theorem ordinary_results_cannot_disappear :
    checkDirectCall #[rootReader] boolScope #[] ⟨"reader"⟩
      #[.ref "x", .boolLit true] = false := by
  with_unfolding_all rfl

theorem wrong_result_target_sort :
    checkDirectCall #[rootReader] [[("x", .bool), ("result", payloadTy)]]
      #[.var "result"] ⟨"reader"⟩ #[.ref "x", .boolLit true] = false := by
  with_unfolding_all rfl

theorem unknown_deferred_target :
    checkDeferredCall #[rootReader] boolScope #[]
      (.funcVal ⟨"absent"⟩ #[]) = false := by
  with_unfolding_all rfl

theorem unknown_higher_order_target :
    checkDeferredCall #[rootReader] boolScope #[] (.var "callee") = false := by
  with_unfolding_all rfl

theorem inner_payload_hides_outer_boolean :
    checkExpr [[("x", payloadTy)], [("x", .bool)]] (.var "x") .boolean = false := by
  with_unfolding_all rfl

theorem inner_payload_can_compare_nil :
    checkExpr [[("x", payloadTy)], [("x", .bool)]]
      (.eqCmp payloadTy (.nil none) (.var "x")) .boolean = true := by
  with_unfolding_all rfl

theorem recovery_outside_handler_is_typed (Γ : Context) :
    ExprTyped Γ .recoverCall .payload := .recover

theorem general_interface_equality_is_outside_profile :
    checkExpr [[("x", payloadTy), ("y", payloadTy)]]
      (.eqCmp payloadTy (.var "x") (.var "y")) .boolean = false := by
  with_unfolding_all rfl

theorem exported_sequence_declaration :
    checkStmts #[] [] [.seqn #[.initialization ⟨"x", .bool⟩],
      .assign (.var "x") (.boolLit true)] = true := by
  with_unfolding_all rfl

theorem exported_sequence_duplicate_rejects :
    checkStmts #[] [] [.seqn #[.initialization ⟨"x", .bool⟩],
      .initialization ⟨"x", .bool⟩] = false := by
  with_unfolding_all rfl

theorem block_shadow_admits :
    checkStmt #[] false boolScope (.block #[⟨"x", payloadTy⟩]
      #[.assign (.var "x") .recoverCall]) = true := by
  with_unfolding_all rfl

theorem block_local_does_not_escape :
    checkStmts #[] [] [.block #[⟨"x", .bool⟩] #[],
      .assign (.var "x") (.boolLit true)] = false := by
  with_unfolding_all rfl

theorem bare_initialization_rejects :
    checkStmt #[] false [] (.initialization ⟨"x", .bool⟩) = false := by
  with_unfolding_all rfl

theorem bare_if_initialization_rejects :
    checkStmt #[] false [] (.ifThenElse (.boolLit true)
      (.initialization ⟨"x", .bool⟩) (.seqn #[])) = false := by
  with_unfolding_all rfl

theorem branch_export_rejects :
    checkStmt #[] false [] (.ifThenElse (.boolLit true)
      (.seqn #[.initialization ⟨"x", .bool⟩]) (.seqn #[])) = false := by
  with_unfolding_all rfl

theorem nil_pointer_default_is_not_live :
    checkStmt #[] false [] (.block #[⟨"p", .pointer .bool⟩] #[]) = false := by
  with_unfolding_all rfl

def emptyEntry : Func := { id := ⟨"entry"⟩, args := #[], results := #[], body := .block #[] #[] }
def uncheckedBody : Func := {
  id := ⟨"unused"⟩, args := #[], results := #[]
  body := .block #[] #[.assign (.var "unbound") (.boolLit true)] }

theorem malformed_uncalled_body_rejects :
    checkRecovery { funcs := #[emptyEntry, uncheckedBody] } "entry" #[] =
      .error (.body ⟨"unused"⟩) := by
  with_unfolding_all rfl

theorem malformed_unreachable_branch_rejects :
    checkStmt #[] false [] (.ifThenElse (.boolLit false)
      uncheckedBody.body (.seqn #[])) = false := by
  with_unfolding_all rfl

theorem blank_parameter_keys_are_explicitly_outside_profile :
    checkFunction #[] { emptyEntry with args := #[⟨"_", .bool⟩, ⟨"_", .bool⟩] } =
      .error (.signatureBindingKeys ⟨"entry"⟩) := by
  with_unfolding_all rfl

theorem missing_result_return_rejects :
    checkFunction #[] { emptyEntry with results := #[⟨"result", .bool⟩] } =
      .error (.missingReturn ⟨"entry"⟩) := by
  with_unfolding_all rfl

def directCycle : Program := { funcs := #[
  { id := ⟨"entry"⟩, args := #[], results := #[], body := .block #[] #[.call #[] ⟨"other"⟩ #[]] },
  { id := ⟨"other"⟩, args := #[], results := #[], body := .block #[] #[.call #[] ⟨"entry"⟩ #[]] }] }

theorem indirect_recursion_rejects :
    checkRecovery directCycle "entry" #[] = .error .recursiveOrUnresolvedGraph := by
  with_unfolding_all rfl

def deferredCycle : Program := { funcs := #[
  { id := ⟨"entry"⟩, args := #[], results := #[], body := .block #[] #[.deferCall (.funcVal ⟨"other"⟩ #[]) #[]] },
  { id := ⟨"other"⟩, args := #[], results := #[], body := .block #[] #[.deferCall (.funcVal ⟨"entry"⟩ #[]) #[]] }] }

theorem deferred_recursion_rejects :
    checkRecovery deferredCycle "entry" #[] = .error .recursiveOrUnresolvedGraph := by
  with_unfolding_all rfl

def payloadProgram (bytes : GoString) : Program := { funcs := #[
  { id := ⟨"entry"⟩, args := #[], results := #[], body := .block #[] #[.panicStmt (boxed bytes)] }] }

theorem arbitrary_byte_payload_admits (bytes : GoString) :
    checkRecovery (payloadProgram bytes) "entry" #[] = .ok () := by
  with_unfolding_all rfl

def repanicProgram (bytes : GoString) : Program := { funcs := #[
  { id := ⟨"entry"⟩, args := #[], results := #[], body := .block #[] #[
      .deferCall (.funcVal ⟨"handler"⟩ #[]) #[], .panicStmt (boxed bytes)] },
  { id := ⟨"handler"⟩, args := #[], results := #[], body := .block #[⟨"recovered", payloadTy⟩] #[
      .assign (.var "recovered") .recoverCall, .panicStmt (boxed bytes)] }] }

theorem equal_repanic_admits (bytes : GoString) :
    checkRecovery (repanicProgram bytes) "entry" #[] = .ok () := by
  with_unfolding_all rfl

theorem invalid_utf8_and_control_bytes_admit :
    checkRecovery (repanicProgram ⟨#[255, 128, 0, 1, 9, 10, 13]⟩) "entry" #[] = .ok () :=
  equal_repanic_admits _

theorem callee_before_caller_admits (bytes : GoString) :
    checkRecovery { (repanicProgram bytes) with funcs := (repanicProgram bytes).funcs.reverse }
      "entry" #[] = .ok () := by
  with_unfolding_all rfl

theorem recovery_profile_is_distinct_from_O1 :
    BooleanTyping.checkTypedBoolean (payloadProgram ⟨#[0, 255]⟩) "entry" #[] ≠ .ok () := by
  intro h
  contradiction

end GoLean.GoCore.RecoveryTyping.Tests
