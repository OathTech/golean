import GoLeanIris.SharedDriver
import GoLean.Interface

/-! Both live customers consume terminal and metadata contracts through the
experimental facade. Functional results still come from their Iris proofs. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryTyping

theorem observed_normal_of_program {p : Program} {name : String}
    {args : Array GoValue} {fuel ch result}
    (admitted : RecoveryAdmission p name args)
    (run : runProgramPoolOutM fuel p name args ch = .ok result) :
    RecoveryRuntime.runProgramPoolWithAbort fuel p name args ch = (.ok result, none) := by
  obtain ⟨_, _, outcome⟩ := RecoveryRuntime.runProgramPoolWithAbort_typed admitted fuel ch
  have erase := RecoveryRuntime.runProgramPoolWithAbort_erasure fuel p name args ch
  rw [run] at erase
  rcases outcome with ⟨_, _, _, _, observed⟩ | ⟨_, observed⟩ | observed
  · rw [observed] at erase
    have result_eq := Except.ok.inj erase
    simpa only [result_eq] using observed
  · rw [observed] at erase; contradiction
  · rw [observed] at erase; contradiction

theorem recovered_observed_all_choices (ch : Choices) :
    RecoveryRuntime.runProgramPoolWithAbort 60 recoveryProgram "Recovered" #[] ch =
      (.ok {values := #[.bool true], output := GoString.empty}, none) :=
  observed_normal_of_program recovery_admitted (recovered_program_all_choices ch)

theorem normal_observed_all_choices (ch : Choices) :
    RecoveryRuntime.runProgramPoolWithAbort 60 recoveryProgram "Normal" #[] ch =
      (.ok {values := #[.bool true], output := GoString.empty}, none) :=
  observed_normal_of_program normal_admitted (normal_program_all_choices ch)

theorem shared_observed_all_choices (b : Bool) (ch : Choices) :
    RecoveryRuntime.runProgramPoolWithAbort 200 sharedProgram "Shared" #[.bool b] ch =
      (.ok {values := #[.bool (!b)], output := GoString.empty}, none) :=
  observed_normal_of_program (shared_admitted b) (shared_program_all_choices b ch)

/-- The existing uncaught semantic control obtains computed metadata from
the generic admitted-program theorem; no Iris NotStuck claim is made. -/
theorem uncaught_has_actual_record :
    ∃ record, RecoveryRuntime.runProgramPoolWithAbort 60 recoveryProgram "Uncaught" #[] [] =
      (.error (.panic "customer panic", GoString.empty), some record) ∧
      "customer panic" = stringPanicHead record.bytes record.recovered :=
  (RecoveryRuntime.runProgramPoolWithAbort_panic_iff uncaught_admitted 60 [] "customer panic").mp
    uncaught_program

theorem a2_entries_no_refusal (fuel : Nat) (ch : Choices) (reason : Refusal) (out : GoString) :
    runProgramPoolOutM fuel recoveryProgram "Recovered" #[] ch ≠ .error (.refusal reason, out) ∧
    runProgramPoolOutM fuel recoveryProgram "Normal" #[] ch ≠ .error (.refusal reason, out) ∧
    runProgramPoolOutM fuel recoveryProgram "Uncaught" #[] ch ≠ .error (.refusal reason, out) :=
  ⟨RecoveryRuntime.runProgramPool_no_refusal recovery_admitted fuel ch reason out,
   RecoveryRuntime.runProgramPool_no_refusal normal_admitted fuel ch reason out,
   RecoveryRuntime.runProgramPool_no_refusal uncaught_admitted fuel ch reason out⟩

theorem shared_no_refusal (b : Bool) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) :
    runProgramPoolOutM fuel sharedProgram "Shared" #[.bool b] ch ≠ .error (.refusal reason, out) :=
  RecoveryRuntime.runProgramPool_no_refusal (shared_admitted b) fuel ch reason out

end GoLean.IrisCustomer
