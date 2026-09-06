import GoLean.Interface
import Tests.BooleanTypingFixture

namespace GoLean.GoCore.BooleanRuntime.Tests
open Machine BooleanTyping

def oneBoolean : ExecState := { heap := #[.value .bool (.bool true)] }

/-- A valid visible lookup must not conceal a dangling outer binding. -/
theorem hidden_outer_binding_rejected :
    ¬ EnvRoots oneBoolean [[("x", .base ⟨0⟩)], [("x", .base ⟨999⟩)]] := by
  intro h
  obtain ⟨a, b, ha, hb⟩ := h [("x", .base ⟨999⟩)] (by simp)
    ("x", .base ⟨999⟩) (by simp)
  cases ha
  simp [oneBoolean] at hb

/-- Even a shadowed binding in the same scope is part of the invariant. -/
theorem hidden_same_scope_binding_rejected :
    ¬ EnvRoots oneBoolean [[("x", .base ⟨0⟩), ("x", .base ⟨999⟩)]] := by
  intro h
  obtain ⟨a, b, ha, hb⟩ := h [("x", .base ⟨0⟩), ("x", .base ⟨999⟩)]
    (by simp) ("x", .base ⟨999⟩) (by simp)
  cases ha
  simp [oneBoolean] at hb

def wrongCell : ExecState := { heap := #[.value .bool .nil] }

theorem address_bounds_do_not_type_storage :
    StateWf wrongCell ∧ ¬ BoolHeap wrongCell := by
  constructor
  · decide +kernel
  · intro h
    obtain ⟨b, hb⟩ := h 0 (by decide +kernel)
    simp [wrongCell] at hb

set_option maxRecDepth 4096 in
/-- The real setup path binds the argument, zeroes the result and returns
the pinned result cell outside its empty driver barrier. Both input values
are quantified; this is a small concrete check alongside the generic proof. -/
theorem native_argument_setup (b : Bool) (fuel : Nat) (ch : Choices) :
    runProgramSetupM fuel BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] ch =
      .ok (.exec (.block #[] #[
          .seqn #[.assign (.var "result") (.and (.var "b") (.boolLit true))],
          .returnStmt])
        [[("result", .base ⟨1⟩), ("b", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop),
        { programState BooleanTyping.Tests.nativeFixture with
          heap := #[.value .bool (.bool b), .value .bool (.bool false)] },
        [.base ⟨1⟩], ch) := by
  cases b <;> with_unfolding_all rfl

theorem duplicate_readout_preserves_alias (b : Bool) :
    loadMany { heap := #[.value .bool (.bool b)] } [.base ⟨0⟩, .base ⟨0⟩] =
      .ok [.bool b, .bool b] := by rfl

end GoLean.GoCore.BooleanRuntime.Tests
