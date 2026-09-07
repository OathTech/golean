import Tests.RecoveryTypingFixture
import GoLean.Interface

/-! Reuse the complete native artifact already checked by the recovery typing
gate. This opt-in customer imports the exact test artifact; it does not
reconstruct a smaller program or assume frontend name conventions. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryTyping

abbrev sharedProgram : Program := RecoveryTyping.Tests.nativeRecovery

theorem shared_admitted (b : Bool) : RecoveryAdmission sharedProgram "Shared" #[.bool b] :=
  checkRecovery_sound (RecoveryTyping.Tests.shared_admitted b)

theorem shared_typed : ProgramTyped sharedProgram := (shared_admitted false).2.2

def sharedState (heap : Heap := #[]) : ExecState :=
  { BooleanRuntime.programState sharedProgram with heap }

end GoLean.IrisCustomer
