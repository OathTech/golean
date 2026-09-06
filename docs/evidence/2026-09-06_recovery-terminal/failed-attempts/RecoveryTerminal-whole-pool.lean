import GoLean.GoCore.RecoveryPoolObservationTyped
import Tests.RecoveryTyping

namespace GoLean.GoCore.RecoveryRuntime.TerminalTests
open Machine RecoveryTyping
open RecoveryTyping.Tests

set_option maxRecDepth 8192

/-- There is no admission restriction on arbitrary string bytes. The generic
contract, rather than this fixture's execution, discharges refusal freedom. -/
theorem arbitrary_bytes_no_refusal (bytes : GoString) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) :
    runProgramPoolOutM fuel (payloadProgram bytes) "entry" #[] ch ≠
      .error (.refusal reason, out) :=
  runProgramPool_no_refusal (checkRecovery_sound (arbitrary_byte_payload_admits bytes))
    fuel ch reason out

theorem equal_repanic_no_refusal (bytes : GoString) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) (record : Option AbortRecord) :
    runProgramPoolWithAbort fuel (repanicProgram bytes) "entry" #[] ch ≠
      (.error (.refusal reason, out), record) :=
  runProgramPoolWithAbort_no_refusal (checkRecovery_sound (equal_repanic_admits bytes))
    fuel ch reason out record

def invalidBytes : GoString := ⟨#[255, 128, 0, 1, 9, 10, 13]⟩
def multilineBytes : GoString := ⟨#[104, 10, 116, 97, 105, 108]⟩

theorem invalid_utf8_terminal_has_complete_bytes :
    runProgramPoolWithAbort 16 (payloadProgram invalidBytes) "entry" #[] [7, 3] =
      (.error (.panic (stringPanicHead invalidBytes false), GoString.empty),
        some ⟨invalidBytes, false, []⟩) := by
  with_unfolding_all rfl

theorem multiline_terminal_retains_tail_bytes :
    runProgramPoolWithAbort 16 (payloadProgram multilineBytes) "entry" #[] [7, 3] =
      (.error (.panic "h", GoString.empty), some ⟨multilineBytes, false, []⟩) := by
  with_unfolding_all rfl

/-- Equal repanic preserves the older recovered entry in the complete chain;
the selected first-line member does not erase the observation metadata. -/
theorem equal_repanic_records_recovered_tail :
    runProgramPoolWithAbort 50 (repanicProgram invalidBytes) "entry" #[] [7, 3] =
      (.error (.panic (stringPanicHead invalidBytes true), GoString.empty),
        some ⟨invalidBytes, true, [⟨invalidBytes, false⟩]⟩) := by
  with_unfolding_all rfl

theorem zero_fuel_is_exhaustion (bytes : GoString) (ch : Choices) :
    runProgramPoolWithAbort 0 (payloadProgram bytes) "entry" #[] ch =
      (.error (.fuelOut, GoString.empty), none) := by
  with_unfolding_all rfl

def zeroResult : Program := { funcs := #[{
  id := ⟨"entry"⟩, args := #[], results := #[⟨"result", .bool⟩],
  body := .block #[] #[.returnStmt] }] }

theorem zero_result_admitted : checkRecovery zeroResult "entry" #[] = .ok () := by
  with_unfolding_all rfl

theorem normal_readout_is_initialized_false (ch : Choices) :
    runProgramPoolWithAbort 8 zeroResult "entry" #[] ch =
      (.ok {values := #[.bool false], output := GoString.empty}, none) := by
  with_unfolding_all rfl

/-- The typed theorem also retains a caller's arbitrary output prefix and
unchanged choice stream at the generic singleton-pool seam. -/
theorem singleton_observer_preserves_prefix {p ps roots s c}
    (inv : Inv p ps roots s c) (fuel : Nat) (ch : Choices)
    (rs : RaceState) (prefix : GoString) :
    (execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ rs ch prefix).1.1 = prefix := by
  rw [inv.pool_observation_eq]

end GoLean.GoCore.RecoveryRuntime.TerminalTests
