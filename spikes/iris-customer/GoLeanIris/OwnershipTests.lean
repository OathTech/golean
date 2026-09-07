import GoLeanIris.SharedDriver

/-! Kernel challenges to the resource interpretation used by shared
captures. Two closures may store the same pointer; that does not duplicate
the full ownership needed to mutate its pointee. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap Iris.BI

theorem full_root_exclusive {GF : BundledGFunctors} [GoGS GF]
    (root : Nat) (left right : HeapCell) :
    (root ↦ left ∗ root ↦ right) ⊢ (False : IProp GF) := by
  iintro H
  icases pointsTo_op_cmraValid $$ H with ⟨%valid, _⟩
  have bad := DFrac.valid_op_own valid
  exact False.elim ((by decide : ¬ (1 : Qp).val < 1) bad)

/-- At every root address the proof consumes one mutable cell through
both deferred handlers and returns it once. The public functional fact
is uniform over the input and the caller's original choice stream. -/
theorem shared_result_challenges_all_choices (ch : Choices) :
    runProgramPoolOutM 200 sharedProgram "Shared" #[.bool false] ch =
        .ok {values := #[.bool true], output := GoString.empty} ∧
    runProgramPoolOutM 200 sharedProgram "Shared" #[.bool true] ch =
        .ok {values := #[.bool false], output := GoString.empty} :=
  ⟨shared_program_all_choices false ch, shared_program_all_choices true ch⟩

end GoLean.IrisCustomer
