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

def frontier (bytes : GoString) (recovered : Bool) (tail : List AbortHead) : Config :=
  .panicking (AbortRecord.mk bytes recovered tail).chain .stop

theorem actual_pool_string_frontier (bytes : GoString) (recovered : Bool)
    (tail : List AbortHead) (s : ExecState) (ch : Choices) (out : GoString) :
    execPoolWithAbort 1 ⟨#[.running (frontier bytes recovered tail) none], s, 0⟩ {} ch out =
      ((out, .error (.panic (stringPanicHead bytes recovered))),
        some ⟨bytes, recovered, tail⟩) := by
  rw [show frontier bytes recovered tail =
    .panicking ((AbortHead.mk bytes recovered).entry :: tail.map AbortHead.entry) .stop from rfl]
  rw [singleton_observer_string_abort 0 s _ _ bytes rfl]
  have ht : stringPanicEntries? (tail.map AbortHead.entry) = some tail := by
    induction tail with
    | nil => rfl
    | cons head tail ih =>
        cases head
        simp [stringPanicEntries?, stringPanicEntry?, AbortHead.entry, ih]
  simp [abortRecord?, Config.abort?, stringPanicEntry?, AbortHead.entry, ht]

theorem invalid_utf8_terminal_has_complete_bytes :
    execPoolWithAbort 1
      ⟨#[.running (frontier invalidBytes false []) none], {}, 0⟩ {} [7, 3] GoString.empty =
      ((GoString.empty, .error (.panic (stringPanicHead invalidBytes false))),
        some ⟨invalidBytes, false, []⟩) :=
  actual_pool_string_frontier _ _ _ _ _ _

theorem multiline_terminal_retains_tail_bytes :
    execPoolWithAbort 1
      ⟨#[.running (frontier multilineBytes false []) none], {}, 0⟩ {} [7, 3] GoString.empty =
      ((GoString.empty, .error (.panic (stringPanicHead multilineBytes false))),
        some ⟨multilineBytes, false, []⟩) :=
  actual_pool_string_frontier _ _ _ _ _ _

/-- Equal repanic preserves the older recovered entry in the complete chain;
the selected first-line member does not erase the observation metadata. -/
theorem equal_repanic_records_recovered_tail :
    execPoolWithAbort 1
      ⟨#[.running (frontier invalidBytes true [⟨invalidBytes, false⟩]) none], {}, 0⟩
      {} [7, 3] GoString.empty =
      ((GoString.empty, .error (.panic (stringPanicHead invalidBytes true))),
        some ⟨invalidBytes, true, [⟨invalidBytes, false⟩]⟩) :=
  actual_pool_string_frontier _ _ _ _ _ _

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
    (rs : RaceState) (outputPrefix : GoString) :
    (execPoolWithAbort fuel ⟨#[.running c none], s, 0⟩ rs ch outputPrefix).1.1 = outputPrefix := by
  rw [inv.pool_observation_eq]

/-- Executable full-driver challenges supplement the kernel contracts. Each
checks exact output, complete payload bytes, flags and tail on the actual
program path. They are tests, not additional kernel theorems. -/
def checkPanic (label : String) (p : Program) (fuel : Nat) (message : String)
    (bytes : GoString) (recovered : Bool) (tail : List (GoString × Bool)) : IO Unit := do
  match runProgramPoolWithAbort fuel p "entry" #[] [7, 3] with
  | (.error (.panic actual, out), some record) =>
      unless actual == message && out == GoString.empty && record.bytes == bytes &&
          record.recovered == recovered && record.tail.map (fun h => (h.bytes, h.recovered)) == tail do
        throw <| IO.userError s!"terminal challenge {label}: wrong member/output/record"
  | _ => throw <| IO.userError s!"terminal challenge {label}: expected actual panic record"

#eval checkPanic "invalid UTF-8" (payloadProgram invalidBytes) 16
  (stringPanicHead invalidBytes false) invalidBytes false []
#eval checkPanic "multiline" (payloadProgram multilineBytes) 16 "h" multilineBytes false []
#eval checkPanic "equal repanic" (repanicProgram invalidBytes) 50
  (stringPanicHead invalidBytes true) invalidBytes true [(invalidBytes, false)]

end GoLean.GoCore.RecoveryRuntime.TerminalTests
