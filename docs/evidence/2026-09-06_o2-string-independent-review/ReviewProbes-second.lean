import GoLean.Interface
import Tests.RecoveryTerminalAudit

namespace O2StringIndependentReview
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.RecoveryRuntime

-- Broader input: a string head with a non-string tail has a terminal member,
-- but the complete-string-chain observer must withhold a record.
theorem mixed_tail_withholds_record (bytes : GoString) (recovered : Bool)
    (s : ExecState) (ch : Choices) (out : GoString) :
    execPoolWithAbort 1
      ⟨#[.running (.panicking
        [⟨.interface .string (.string bytes), recovered⟩, ⟨.bool true, false⟩] .stop) none], s, 0⟩
      {} ch out = ((out, .error (.panic (stringPanicHead bytes recovered))), none) := by
  rw [singleton_observer_string_abort 0 s _ _ bytes rfl]
  simp [abortRecord?, Config.abort?, stringPanicEntry?, stringPanicEntries?]

theorem zero_fuel_does_not_read_abort (bytes : GoString) (recovered : Bool)
    (s : ExecState) (ch : Choices) (out : GoString) :
    execPoolWithAbort 0
      ⟨#[.running (.panicking [⟨.interface .string (.string bytes), recovered⟩] .stop) none], s, 0⟩
      {} ch out = ((out, .error .fuelOut), none) := by
  rfl

-- No admission premise is needed to exclude spurious metadata on nonpanic
-- outcomes. The premise is the actual observer computation in both claims.
theorem normal_cannot_have_record {fuel p name args ch value record}
    (observed : runProgramPoolWithAbort fuel p name args ch = (.ok value, some record)) : False := by
  obtain ⟨out, h⟩ := runProgramPoolWithAbort_member observed
  contradiction

theorem fuel_cannot_have_record {fuel p name args ch out record}
    (observed : runProgramPoolWithAbort fuel p name args ch =
      (.error (.fuelOut, out), some record)) : False := by
  obtain ⟨actualOut, h⟩ := runProgramPoolWithAbort_member observed
  contradiction

#print axioms mixed_tail_withholds_record
#print axioms zero_fuel_does_not_read_abort
#print axioms normal_cannot_have_record
#print axioms fuel_cannot_have_record
#eval RecoveryTerminalAudit.run
end O2StringIndependentReview
