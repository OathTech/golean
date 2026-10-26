import Tests.GoCoreAdmissionFixture
import GoLean.GoCore.StepFn

namespace GoLean.GoCore.Admission.Tests
open GoLean.GoCore.Machine
-- Every `with_unfolding_all rfl` below runs the checker (`unbound_refuses`: the
-- driver) inside the elaborator's definitional unfolding, whose recursion nests
-- deeper than the default `maxRecDepth` (512): each fails at 1024 and passes at
-- 2048 (measured 2026-10-26, lane core/dc12-warnings-1026), so each theorem that
-- needs it raises the limit for itself, at 2x the measured need; the three that
-- pass at the default carry none. Core has no `DecidableEq (Except ..)`, so
-- `decide +kernel` is not a drop-in; the kernel check itself is unaffected.

set_option maxRecDepth 4096 in
theorem native_constant_accepted : checkBoolean fixture "Constant" #[] = .ok () := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem native_negate_true_accepted :
    checkBoolean fixture "Negate" #[.bool true] = .ok () := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem native_negate_false_accepted :
    checkBoolean fixture "Negate" #[.bool false] = .ok () := by with_unfolding_all rfl
theorem native_admission : BooleanAdmission fixture "Negate" #[.bool true] :=
  checkBoolean_sound native_negate_true_accepted
theorem bool_argument_typed : InitialValueHasType (.bool true) .bool := .boolean true

def simple (body : Stmt) : Program := {
  funcs := #[{ id := ⟨"F"⟩, args := #[], results := #[⟨vid "result", .bool⟩], body }]
}
def withType (body : TypeDef) : Program := {
  fixture with typeDefs := TypeEnv.reserved ++ #[(⟨"test.T"⟩, body)]
}

theorem reserved_prefix_rejected :
    checkIndices { fixture with typeDefs := #[] } = .error .reservedPrefix := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem wrong_reserved_payload_rejected :
    checkIndices { fixture with typeDefs :=
      #[(emptyStructTypeId, .struct #[]), (runtimeErrorTypeId, .opaqueDecl "wrong payload")] } =
      .error .reservedPrefix := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem direct_cycle_rejected :
    checkIndices (withType (.defined (.defined 2))) = .error .typeDependencyOrder := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem array_cycle_rejected :
    checkIndices (withType (.defined (.array 1 (.defined 2)))) =
      .error .typeDependencyOrder := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem recursive_pointer_accepted :
    checkBoolean (withType (.defined (.pointer (.defined 2)))) "Constant" #[] = .ok () := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_pointer_rejected :
    checkIndices (withType (.defined (.pointer (.defined 3)))) = .error .typeIndexBounds := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_function_signature_rejected :
    checkIndices (withType (.defined (.funcType [.slice (.defined 3)] [.pointer (.defined 4)] false))) =
      .error .typeIndexBounds := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_interface_signature_rejected :
    checkIndices (withType (.interfaceDef #[{id := ⟨"M", ""⟩, params := #[.pointer (.defined 3)], results := #[]}])) =
      .error .typeIndexBounds := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem duplicate_type_rejected :
    checkIndices { fixture with typeDefs := TypeEnv.reserved ++ #[(emptyStructTypeId, .struct #[])] } =
      .error .duplicateTypeKey := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem duplicate_function_rejected :
    checkIndices { fixture with funcs := fixture.funcs ++ fixture.funcs } =
      .error .duplicateFunctionKey := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_body_type_rejected :
    checkIndices (simple (.ifThenElse (.boolLit true) .returnStmt
      (.assign (.var (vid "result")) (.convert (.pointer (.defined 2)) (.nil none))))) =
      .error .typeIndexBounds := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_select_type_rejected :
    checkIndices (simple (.selectStmt #[
      (.recv #[] (.nil none) (.defined 2), .returnStmt)] none)) =
      .error .typeIndexBounds := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_global_type_rejected :
    checkIndices { fixture with globals := #[{name := "g", typ := .slice (.defined 2)}] } =
      .error .typeIndexBounds := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem dangling_method_receiver_rejected :
    checkIndices { fixture with methods := #[{id := ⟨"M", ""⟩, funcId := ⟨"Constant"⟩, recv := .pointer (.defined 2)}] } =
      .error .typeIndexBounds := by with_unfolding_all rfl

set_option maxRecDepth 4096 in
theorem missing_entry_rejected :
    checkBoolean fixture "Missing" #[] = .error (.missingEntry "Missing") := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem wrong_arity_rejected :
    checkBoolean fixture "Negate" #[] = .error (.entryArity 1 0) := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem wrong_initial_value_rejected :
    checkBoolean fixture "Negate" #[.int 1 .int] = .error .initialArgumentTypes := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem pointer_argument_rejected :
    checkBoolean fixture "Negate" #[.addr (.base ⟨0⟩)] = .error .initialArgumentTypes := by with_unfolding_all rfl
theorem wrong_parameter_type_rejected :
    checkEntry { funcs := #[{id := ⟨"F"⟩, args := #[⟨vid "b", .int .int⟩], results := #[], body := .returnStmt}] }
      "F" #[.bool true] = .error .entryParameterTypes := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem initializer_rejected :
    checkBoolean { fixture with funcs := (fixture.funcs.push
      {id := pkgInitFuncId, args := #[], results := #[], body := .returnStmt}) }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem unreachable_unsupported_body_rejected :
    checkBoolean { fixture with funcs := (fixture.funcs.push
      {id := ⟨"Unused"⟩, args := #[], results := #[], body := .unsupported "unmodeled"}) }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem call_rejected :
    checkBoolean (simple (.call #[] ⟨"F"⟩ #[])) "F" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem globals_rejected :
    checkBoolean { fixture with globals := #[{name := "g", typ := .bool}] }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
set_option maxRecDepth 4096 in
theorem method_declaration_rejected :
    checkBoolean { fixture with methods := #[{id := ⟨"M", ""⟩, funcId := ⟨"Constant"⟩, recv := .bool}] }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl

set_option maxRecDepth 4096 in
/-- Explicit admitted limitation: this policy does not validate method-set
keys or diagnostic displays. No operation in the Boolean fragment uses them. -/
theorem unchecked_metadata_accepted :
    checkBoolean { fixture with
      methodSets := #[{key := "no such carrier", coverage := .exported}]
      typeDisplays := #[] } "Constant" #[] = .ok () := by with_unfolding_all rfl

def unbound : Program := simple (.assign (.var (vid "result")) (.var (vid "missing")))
set_option maxRecDepth 4096 in
theorem unbound_accepted : checkBoolean unbound "F" #[] = .ok () := by with_unfolding_all rfl

set_option maxRecDepth 4096 in
/-- Admission is not refusal freedom: this admitted malformed program
actually refuses in the current executable driver. -/
theorem unbound_refuses :
    runProgramM 20 unbound "F" #[] [] =
      .error (.stuck s!"unbound GoCore variable address: {vid "missing"}") := by
  with_unfolding_all rfl

end GoLean.GoCore.Admission.Tests
