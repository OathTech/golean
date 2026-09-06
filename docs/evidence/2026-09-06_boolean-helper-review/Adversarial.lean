import GoLean.Interface
import Tests.BooleanRuntime

namespace BooleanHelperAdversarial
open GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.BooleanRuntime
set_option maxRecDepth 4096

-- A3a really permits this body; setup alone must not imply execution progress.
def unbound : Program := { funcs := #[{
  id := ⟨"F"⟩, args := #[], results := #[⟨"result", .bool⟩],
  body := .assign (.var "result") (.var "missing") }] }

theorem unbound_admitted : Admission.BooleanAdmission unbound "F" #[] :=
  (Admission.checkBoolean_iff unbound "F" #[]).mp (by with_unfolding_all rfl)

theorem unbound_setup_zero_fuel (ch : Choices) :
    runProgramSetupM 0 unbound "F" #[] ch =
      .ok (.exec (.assign (.var "result") (.var "missing"))
        [[("result", .base ⟨0⟩)]] (.frame [] [] [] [] .stop),
        { programState unbound with heap := #[.value .bool (.bool false)] },
        [.base ⟨0⟩], ch) := by with_unfolding_all rfl

-- Two allocated result cells do not by themselves yield two distinct pins.
def duplicateResults : Program := { funcs := #[{
  id := ⟨"F"⟩, args := #[],
  results := #[⟨"x", .bool⟩, ⟨"x", .bool⟩], body := .returnStmt }] }

theorem duplicate_results_admitted :
    Admission.BooleanAdmission duplicateResults "F" #[] :=
  (Admission.checkBoolean_iff duplicateResults "F" #[]).mp (by with_unfolding_all rfl)

theorem duplicate_results_setup (fuel : Nat) (ch : Choices) :
    runProgramSetupM fuel duplicateResults "F" #[] ch =
      .ok (.exec .returnStmt [[("x", .base ⟨1⟩), ("x", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop),
        { programState duplicateResults with
          heap := #[.value .bool (.bool false), .value .bool (.bool false)] },
        [.base ⟨1⟩, .base ⟨1⟩], ch) := by with_unfolding_all rfl

-- Readout permits false and repeated values; it is not an ownership predicate.
theorem false_alias_readout :
    loadMany { heap := #[.value .bool (.bool false)] }
      [.base ⟨0⟩, .base ⟨0⟩] = .ok [.bool false, .bool false] := rfl

-- A typed store changes every alias's observed value; root preservation is typedness.
theorem aliased_write_readout :
    (do let s' ← storeLoc { heap := #[.value .bool (.bool true)] }
          (.base ⟨0⟩) (.bool false)
        loadMany s' [.base ⟨0⟩, .base ⟨0⟩]) =
      .ok [.bool false, .bool false] := by with_unfolding_all rfl

#print axioms unbound_admitted
#print axioms unbound_setup_zero_fuel
#print axioms duplicate_results_admitted
#print axioms duplicate_results_setup
#print axioms false_alias_readout
#print axioms aliased_write_readout
end BooleanHelperAdversarial
