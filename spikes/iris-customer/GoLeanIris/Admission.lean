import GoLeanIris.Program
import GoLean.Interface

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryTyping

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem recovery_admitted : RecoveryAdmission recoveryProgram "Recovered" #[] := by
  apply checkRecovery_sound
  with_unfolding_all rfl

theorem recovery_typed : ProgramTyped recoveryProgram := recovery_admitted.2.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem normal_admitted : RecoveryAdmission recoveryProgram "Normal" #[] := by
  apply checkRecovery_sound
  with_unfolding_all rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem uncaught_admitted : RecoveryAdmission recoveryProgram "Uncaught" #[] := by
  apply checkRecovery_sound
  with_unfolding_all rfl

end GoLean.IrisCustomer
