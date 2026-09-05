import Tests.GoCoreAdmissionFixture
import GoLean.GoCore.StepFn

namespace GoLean.GoCore.Admission.Tests
open GoLean.GoCore.Machine
set_option maxRecDepth 4096

theorem native_constant_accepted : checkBoolean fixture "Constant" #[] = .ok () := by with_unfolding_all rfl
theorem native_negate_true_accepted :
    checkBoolean fixture "Negate" #[.bool true] = .ok () := by with_unfolding_all rfl
theorem native_negate_false_accepted :
    checkBoolean fixture "Negate" #[.bool false] = .ok () := by with_unfolding_all rfl
theorem native_admission : BooleanAdmission fixture "Negate" #[.bool true] :=
  checkBoolean_sound native_negate_true_accepted
theorem bool_argument_typed : InitialValueHasType (.bool true) .bool := .boolean true

def simple (body : Stmt) : Program := {
  funcs := #[{ id := ⟨"F"⟩, args := #[], results := #[⟨"result", .bool⟩], body }]
}
def withType (body : TypeDef) : Program := {
  fixture with typeDefs := TypeEnv.reserved ++ #[(⟨"test.T"⟩, body)]
}

theorem reserved_prefix_rejected :
    checkIndices { fixture with typeDefs := #[] } = .error .reservedPrefix := by with_unfolding_all rfl
theorem wrong_reserved_payload_rejected :
    checkIndices { fixture with typeDefs :=
      #[(emptyStructTypeId, .struct #[]), (runtimeErrorTypeId, .opaqueDecl "wrong payload")] } =
      .error .reservedPrefix := by with_unfolding_all rfl
theorem direct_cycle_rejected :
    checkIndices (withType (.defined (.defined 2))) = .error .typeDependencyOrder := by with_unfolding_all rfl
theorem array_cycle_rejected :
    checkIndices (withType (.defined (.array 1 (.defined 2)))) =
      .error .typeDependencyOrder := by with_unfolding_all rfl
theorem recursive_pointer_accepted :
    checkBoolean (withType (.defined (.pointer (.defined 2)))) "Constant" #[] = .ok () := by with_unfolding_all rfl
theorem dangling_pointer_rejected :
    checkIndices (withType (.defined (.pointer (.defined 3)))) = .error .typeIndexBounds := by with_unfolding_all rfl
theorem dangling_function_signature_rejected :
    checkIndices (withType (.defined (.funcType [.slice (.defined 3)] [.pointer (.defined 4)] false))) =
      .error .typeIndexBounds := by with_unfolding_all rfl
theorem dangling_interface_signature_rejected :
    checkIndices (withType (.interfaceDef #[{name := "M", params := #[.pointer (.defined 3)], results := #[]}])) =
      .error .typeIndexBounds := by with_unfolding_all rfl
theorem duplicate_type_rejected :
    checkIndices { fixture with typeDefs := TypeEnv.reserved ++ #[(emptyStructTypeId, .struct #[])] } =
      .error .duplicateTypeKey := by with_unfolding_all rfl
theorem duplicate_function_rejected :
    checkIndices { fixture with funcs := fixture.funcs ++ fixture.funcs } =
      .error .duplicateFunctionKey := by with_unfolding_all rfl
theorem dangling_body_type_rejected :
    checkIndices (simple (.ifThenElse (.boolLit true) .returnStmt
      (.assign (.var "result") (.convert (.pointer (.defined 2)) (.nil none))))) =
      .error .typeIndexBounds := by with_unfolding_all rfl
theorem dangling_select_type_rejected :
    checkIndices (simple (.selectStmt #[
      (.recv #[] (.nil none) (.defined 2), .returnStmt)] none)) =
      .error .typeIndexBounds := by with_unfolding_all rfl
theorem dangling_global_type_rejected :
    checkIndices { fixture with globals := #[{name := "g", typ := .slice (.defined 2)}] } =
      .error .typeIndexBounds := by with_unfolding_all rfl
theorem dangling_method_receiver_rejected :
    checkIndices { fixture with methods := #[{name := "M", funcId := ⟨"Constant"⟩, recv := .pointer (.defined 2)}] } =
      .error .typeIndexBounds := by with_unfolding_all rfl

theorem missing_entry_rejected :
    checkBoolean fixture "Missing" #[] = .error (.missingEntry "Missing") := by with_unfolding_all rfl
theorem wrong_arity_rejected :
    checkBoolean fixture "Negate" #[] = .error (.entryArity 1 0) := by with_unfolding_all rfl
theorem wrong_initial_value_rejected :
    checkBoolean fixture "Negate" #[.int 1 .int] = .error .initialArgumentTypes := by with_unfolding_all rfl
theorem pointer_argument_rejected :
    checkBoolean fixture "Negate" #[.addr (.base ⟨0⟩)] = .error .initialArgumentTypes := by with_unfolding_all rfl
theorem wrong_parameter_type_rejected :
    checkEntry { funcs := #[{id := ⟨"F"⟩, args := #[⟨"b", .int .int⟩], results := #[], body := .returnStmt}] }
      "F" #[.bool true] = .error .entryParameterTypes := by with_unfolding_all rfl
theorem initializer_rejected :
    checkBoolean { fixture with funcs := (fixture.funcs.push
      {id := pkgInitFuncId, args := #[], results := #[], body := .returnStmt}) }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
theorem unreachable_unsupported_body_rejected :
    checkBoolean { fixture with funcs := (fixture.funcs.push
      {id := ⟨"Unused"⟩, args := #[], results := #[], body := .unsupported "unmodeled"}) }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
theorem call_rejected :
    checkBoolean (simple (.call #[] ⟨"F"⟩ #[])) "F" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
theorem globals_rejected :
    checkBoolean { fixture with globals := #[{name := "g", typ := .bool}] }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl
theorem method_declaration_rejected :
    checkBoolean { fixture with methods := #[{name := "M", funcId := ⟨"Constant"⟩, recv := .bool}] }
      "Constant" #[] = .error .booleanSyntaxPolicy := by with_unfolding_all rfl

/-- Explicit admitted limitation: this policy does not validate method-set
keys or diagnostic displays. No operation in the Boolean fragment uses them. -/
theorem unchecked_metadata_accepted :
    checkBoolean { fixture with
      methodSets := #[{key := "no such carrier", coverage := .exported}]
      typeDisplays := #[] } "Constant" #[] = .ok () := by with_unfolding_all rfl

def unbound : Program := simple (.assign (.var "result") (.var "missing"))
theorem unbound_accepted : checkBoolean unbound "F" #[] = .ok () := by with_unfolding_all rfl

set_option maxRecDepth 4096 in
/-- Admission is not refusal freedom: this admitted malformed program
actually refuses in the current executable driver. -/
theorem unbound_refuses :
    runProgramM 20 unbound "F" #[] [] =
      .error (.stuck "unbound GoCore variable address: missing") := by
  with_unfolding_all rfl

end GoLean.GoCore.Admission.Tests
