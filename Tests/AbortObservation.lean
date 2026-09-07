import GoLean.GoCore.RecoveryProgramObservation

namespace GoLean.GoCore.RecoveryRuntime.Tests
open Machine RecoveryTyping

set_option maxRecDepth 8192

def text : GoString := ⟨#[104, 101, 97, 100]⟩
def later : GoString := ⟨#[255, 0, 10, 9]⟩
def entries : List PanicEntry :=
  [⟨.interface .string (.string text), false⟩,
   ⟨.interface .string (.string later), true⟩]
def record : AbortRecord := ⟨text, false, [⟨later, true⟩]⟩
def abortConfig : Config := .panicking entries .stop
def state : ExecState := {types := TypeEnv.reserved}
def beforePool : MultiConfig := ⟨#[.running abortConfig none], state, 0⟩
def afterPool : MultiConfig := ⟨#[.aborted "head"], state, 0⟩
def prefixBytes : GoString := ⟨#[0, 10, 255]⟩

theorem complete_chain_bytes_and_flags : abortRecord? abortConfig = some record := by rfl

theorem nonstring_tail_rejected :
    abortRecord? (.panicking
      [⟨.interface .string (.string text), false⟩, ⟨.interface .bool (.bool true), false⟩] .stop) = none := by rfl

theorem recovered_transient_rejected :
    abortRecord? (.panicking entries (.frame [] [] [] [] .stop false)) = none := by rfl

theorem positive_frontier_record :
    stepAbortRecord? beforePool afterPool ⟨0, .aborted, [], []⟩ "head" = some record := by
  with_unfolding_all rfl

theorem wrong_event_rejected :
    stepAbortRecord? beforePool afterPool ⟨0, .privateStep, [], []⟩ "head" = none := by rfl

theorem wrong_selected_thread_rejected :
    stepAbortRecord? beforePool afterPool ⟨1, .aborted, [], []⟩ "head" = none := by rfl

theorem wrong_tombstone_text_rejected :
    stepAbortRecord? beforePool afterPool ⟨0, .aborted, [], []⟩ "forged" = none := by
  with_unfolding_all rfl

theorem wrong_renderer_text_rejected :
    stepAbortRecord? beforePool ⟨#[.aborted "forged"], state, 0⟩
      ⟨0, .aborted, [], []⟩ "forged" = none := by with_unfolding_all rfl

theorem supplied_tombstone_is_not_provenance :
    execPoolWithAbort 1 afterPool {} [] prefixBytes = ((prefixBytes, .error (.panic "head")), none) := by
  with_unfolding_all rfl

theorem zero_fuel_has_no_record :
    execPoolWithAbort 0 beforePool {} [] prefixBytes = ((prefixBytes, .error .fuelOut), none) := by
  with_unfolding_all rfl

set_option maxRecDepth 8192 in
theorem actual_pool_transition_records_whole_chain :
    execPoolWithAbort 1 beforePool {} [] prefixBytes =
      ((prefixBytes, .error (.panic "head")), some record) := by
  with_unfolding_all rfl

theorem actual_pool_record_has_source_bound_witness :
    PoolAbortWitness 1 beforePool {} [] prefixBytes (prefixBytes, .error (.panic "head")) record :=
  execPoolWithAbort_witness actual_pool_transition_records_whole_chain

def workerPool : MultiConfig :=
  ⟨#[.running (.next .stop) none, .running abortConfig none], state, 0⟩

set_option maxRecDepth 8192 in
theorem main_exit_pick_keeps_worker_alive :
    execPoolWithAbort 1 workerPool {} [1] prefixBytes =
      ((prefixBytes, .error (.panic "head")), some record) := by
  with_unfolding_all rfl

theorem main_exit_pick_can_finish_without_record :
    execPoolWithAbort 1 workerPool {} [0] prefixBytes = ((prefixBytes, .ok (state, [])), none) := by
  with_unfolding_all rfl

theorem generic_erasure_keeps_exact_original_choices (fuel : Nat) (ch : Choices) :
    (execPoolWithAbort fuel workerPool {} ch prefixBytes).1 =
      execProgLoopOut fuel workerPool {} ch prefixBytes :=
  execPoolWithAbort_erasure fuel workerPool {} ch prefixBytes

def nullaryProgram : Program := { funcs := #[{
  id := ⟨"entry"⟩, args := #[], results := #[],
  body := .panicStmt (.toInterface (.interface ⟨"any"⟩) .string (.stringLit text)) }] }

theorem actual_checker_admits_nullary_subject :
    checkRecovery nullaryProgram "entry" #[] = .ok () := by
  with_unfolding_all rfl

theorem checked_program_records_actual_panic :
    checkedRunProgramPoolWithAbortInts 12 nullaryProgram "entry" #[] [7, 3] =
      .ok (.error (.panic "head", GoString.empty), some ⟨text, false, []⟩) := by
  with_unfolding_all rfl

theorem checked_program_zero_fuel_is_not_terminal :
    checkedRunProgramPoolWithAbortInts 0 nullaryProgram "entry" #[] [7, 3] =
      .ok (.error (.fuelOut, GoString.empty), none) := by with_unfolding_all rfl

def integerProgram : Program := { funcs := #[{
  id := ⟨"integer"⟩, args := #[⟨"x", .int .int⟩], results := #[],
  body := .seqn #[] }] }

theorem broader_integer_entry_still_runs :
    runProgramPoolWithAbortInts 5 integerProgram "integer" #[19] [7, 3] =
      (.ok {values := #[], output := GoString.empty}, none) := by
  with_unfolding_all rfl

theorem broader_entry_does_not_gain_admission :
    ¬ RecoveryAdmission integerProgram "integer" #[.int 19] := by
  intro admitted
  have checked := checkRecovery_complete admitted
  contradiction

theorem integer_wrapper_retains_shipped_meaning (fuel : Nat) (ch : Choices) :
    (runProgramPoolWithAbortInts fuel integerProgram "integer" #[19] ch).1 =
      runProgramPoolOutIntsM fuel integerProgram "integer" #[19] ch :=
  runProgramPoolWithAbortInts_erasure fuel integerProgram "integer" #[19] ch

end GoLean.GoCore.RecoveryRuntime.Tests
