import GoLean.GoCore.StringPanic
import GoLean.GoCore.RecoveryProgramObservation

namespace R1Independent
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.RecoveryRuntime

def state : ExecState := { types := TypeEnv.reserved }
def original : GoString := ⟨#[255, 0, 10, 65]⟩
def head : PanicEntry := ⟨.interface .string (.string original), true⟩
def tail : PanicEntry := ⟨.interface .string (.string ⟨#[0, 66]⟩), false⟩
def record : AbortRecord := ⟨original, true, [⟨⟨#[0, 66]⟩, false⟩]⟩
def priorOutput : GoString := ⟨#[255, 10, 0]⟩
def before : MultiConfig := ⟨#[.running (.panicking [head, tail] .stop) none], state, 0⟩

theorem direct_nul_is_preserved :
    (renderStringMember ⟨#[0, 65]⟩).toUTF8.data = #[0, 65] := by decide +kernel

theorem first_lf_can_hide_recovered_suffix :
    stringPanicHead ⟨#[10, 65]⟩ true = "" := by decide +kernel

theorem invalid_tail_after_lf_forces_complete_escape :
    stringPanicHead ⟨#[10, 255]⟩ true = "\"\\x0a\\xff\" [recovered]" := by decide +kernel

theorem malformed_surrogate_is_preserved_as_bytes :
    renderStringMember ⟨#[237, 160, 128]⟩ = "\"\\xed\\xa0\\x80\"" := by decide +kernel

theorem full_chain_records_unrendered_tail :
    abortRecord? (.panicking [head, tail] .stop) = some record := by rfl

theorem renderable_head_does_not_certify_integer_tail :
    abortRecord? (.panicking [head, ⟨.interface (.int .int) (.int 1 .int), false⟩] .stop) =
      none := by rfl

theorem zero_fuel_keeps_prefix_and_has_no_record (ch : Choices) :
    execPoolWithAbort 0 before {} ch priorOutput = ((priorOutput, .error .fuelOut), none) := by
  with_unfolding_all rfl

theorem one_real_pool_abort_keeps_prefix_and_full_chain (ch : Choices) :
    execPoolWithAbort 1 before {} ch priorOutput =
      ((priorOutput, .error (.panic "\"\\xff\\x00\\x0a\\x41\" [recovered]")), some record) := by
  with_unfolding_all rfl

theorem all_input_driver_erasure_includes_output_and_errors
    (fuel : Nat) (p : Program) (name : String) (args : Array Int) (ch : Choices) :
    (runProgramPoolWithAbortInts fuel p name args ch).1 =
      runProgramPoolOutIntsM fuel p name args ch :=
  runProgramPoolWithAbortInts_erasure fuel p name args ch

end R1Independent
