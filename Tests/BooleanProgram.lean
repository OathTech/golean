import GoLean.Interface
import Tests.BooleanTypingFixture

namespace GoLean.GoCore.BooleanRuntime.ProgramTests
open Machine BooleanTyping

set_option maxRecDepth 4096

theorem argument_admitted (b : Bool) :
    TypedBooleanAdmission BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] := by
  apply checkTypedBoolean_sound
  cases b <;> with_unfolding_all rfl

theorem argument_result (b : Bool) (ch : Choices) :
    runProgramPoolOutM 64 BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] ch =
      .ok { values := #[.bool b], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (argument_admitted b)]
  cases b <;> with_unfolding_all rfl

theorem zero_fuel_is_exhaustion (b : Bool) (ch : Choices) :
    runProgramPoolOutM 0 BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] ch =
      .error (.fuelOut, GoString.empty) := by
  rw [runProgramPool_eq_sequential (argument_admitted b)]
  cases b <;> with_unfolding_all rfl

theorem nested_shadow_result (ch : Choices) :
    runProgramPoolOutM 128 BooleanTyping.Tests.nativeFixture "Shadow" #[] ch =
      .ok { values := #[.bool false], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (checkTypedBoolean_sound BooleanTyping.Tests.native_shadow)]
  with_unfolding_all rfl

theorem branch_result (ch : Choices) :
    runProgramPoolOutM 64 BooleanTyping.Tests.nativeFixture "Branches" #[] ch =
      .ok { values := #[.bool false], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (checkTypedBoolean_sound BooleanTyping.Tests.native_branches)]
  with_unfolding_all rfl

theorem zero_local_and_result (ch : Choices) :
    runProgramPoolOutM 64 BooleanTyping.Tests.nativeFixture "Zero" #[] ch =
      .ok { values := #[.bool false], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (checkTypedBoolean_sound BooleanTyping.Tests.native_zero)]
  with_unfolding_all rfl

/-- The driver must retain an existing byte prefix, including NUL and SOH,
and the entire choice tape when classifying an already normal terminal. -/
theorem terminal_at_zero_fuel (ch : Choices) :
    execProgLoopOut 0 ⟨#[.running (.next .stop) none], {}, 0⟩ {} ch
      ⟨#[0, 1, 10, 13]⟩ = (⟨#[0, 1, 10, 13]⟩, .ok ({}, ch)) := by rfl

end GoLean.GoCore.BooleanRuntime.ProgramTests
