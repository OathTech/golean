import GoLean.GoCore.RecoveryPoolObservationTyped
import Tests.RecoveryTyping

/-! The recovery profile's terminal classification, exercised (landing chunk
L3; the sprint's `Tests/RecoveryTerminal` of `7bd32ad6`, RESTATED over the
`repanicCollapse` tape and the D5 refusal). What changed and why: the sprint's
`*_no_refusal` challenges assumed a total renderer; an admitted program
whose string literal's first line is not valid UTF-8 REFUSES, by name, and
the challenges below say so. The equal re-panic program is the first TYPED
two-outcome driver demonstration: the same admitted program, the same fuel,
two streams, two abort texts. -/
namespace GoLean.GoCore.RecoveryRuntime.TerminalTests
open Machine RecoveryTyping
open RecoveryTyping.Tests

set_option maxRecDepth 8192

/-- Any refusal an admitted arbitrary-bytes payload program reaches is the
named invalid-first-line one (D5) — the generic contract, for every byte
string, fuel and stream. -/
theorem arbitrary_bytes_refusal_named (bytes : GoString) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString)
    (run : runProgramPoolOutM fuel (payloadProgram bytes) "entry" #[] ch =
      .error (.refusal reason, out)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes' : GoString),
      first.value = .interface .string (.string bytes') ∧
      stringFirstLine? bytes'.bytes = none ∧
      reason = .unsupported (abortRefusal t first) ∧ out = GoString.empty :=
  runProgramPool_refusal_named (checkRecovery_sound (arbitrary_byte_payload_admits bytes))
    fuel ch reason out run

theorem equal_repanic_refusal_named (bytes : GoString) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) (record : Option AbortRecord)
    (observed : runProgramPoolWithAbort fuel (repanicProgram bytes) "entry" #[] ch =
      (.error (.refusal reason, out), record)) :
    ∃ (t : ExecState) (first : PanicEntry) (bytes' : GoString),
      first.value = .interface .string (.string bytes') ∧
      stringFirstLine? bytes'.bytes = none ∧
      reason = .unsupported (abortRefusal t first) ∧ out = GoString.empty ∧ record = none :=
  runProgramPoolWithAbort_refusal_named (checkRecovery_sound (equal_repanic_admits bytes))
    fuel ch reason out record observed

def invalidBytes : GoString := ⟨#[255, 128, 0, 1, 9, 10, 13]⟩
def multilineBytes : GoString := ⟨#[104, 10, 116, 97, 105, 108]⟩
def validBytes : GoString := ⟨#[104, 105]⟩

def frontier (bytes : GoString) (recovered : Bool) (tail : List AbortHead) : Config :=
  .panicking (AbortRecord.mk bytes recovered tail).chain .stop

theorem stringPanicEntries?_map_entry (tail : List AbortHead) :
    stringPanicEntries? (tail.map AbortHead.entry) = some tail := by
  induction tail with
  | nil => rfl
  | cons head tail ih =>
      cases head
      simp [stringPanicEntries?, stringPanicEntry?, AbortHead.entry, ih]

/-- The pool observer at a string abort frontier WITH a member: the member the
stream's pick selects, and the whole chain in the record. -/
theorem actual_pool_string_frontier (bytes : GoString) (recovered : Bool)
    (tail : List AbortHead) (s : ExecState) (ch : Choices) (out : GoString) (msg : String)
    (hm : stringPanicHead bytes recovered
      (collapseBit (AbortHead.mk bytes recovered).entry (tail.map AbortHead.entry)
        (abortConsult (AbortHead.mk bytes recovered).entry (tail.map AbortHead.entry) ch).1)
      = some msg) :
    execPoolWithAbort 1 ⟨#[.running (frontier bytes recovered tail) none], s, 0⟩ {} ch out =
      ((out, .error (.panic msg)), some ⟨bytes, recovered, tail⟩) := by
  rw [show frontier bytes recovered tail =
    .panicking ((AbortHead.mk bytes recovered).entry :: tail.map AbortHead.entry) .stop from rfl]
  rw [singleton_observer_string_abort 0 s _ _ bytes msg rfl ch {} out hm]
  simp [abortRecord?, Config.abort?, stringPanicEntry?, AbortHead.entry,
    stringPanicEntries?_map_entry]

/-- …and WITHOUT one (the first line is not valid UTF-8): the named refusal,
no record, whatever the stream. -/
theorem actual_pool_string_frontier_refused (bytes : GoString) (recovered : Bool)
    (tail : List AbortHead) (s : ExecState) (ch : Choices) (out : GoString)
    (hm : stringPanicHead bytes recovered
      (collapseBit (AbortHead.mk bytes recovered).entry (tail.map AbortHead.entry)
        (abortConsult (AbortHead.mk bytes recovered).entry (tail.map AbortHead.entry) ch).1)
      = none) :
    execPoolWithAbort 1 ⟨#[.running (frontier bytes recovered tail) none], s, 0⟩ {} ch out =
      ((out, .error (.unsupported (abortRefusal s (AbortHead.mk bytes recovered).entry))), none) := by
  rw [show frontier bytes recovered tail =
    .panicking ((AbortHead.mk bytes recovered).entry :: tail.map AbortHead.entry) .stop from rfl]
  exact singleton_observer_string_abort_refused 0 s _ _ bytes rfl ch {} out hm

/-- D5 at the pool frontier: an invalid first line refuses by name, with no
record — on both picks of the equal re-panic shape. -/
theorem invalid_utf8_frontier_refused :
    execPoolWithAbort 1
      ⟨#[.running (frontier invalidBytes true [⟨invalidBytes, false⟩]) none], {}, 0⟩ {} [0] GoString.empty =
      ((GoString.empty, .error (.unsupported (abortRefusal {} (AbortHead.mk invalidBytes true).entry))), none) ∧
    execPoolWithAbort 1
      ⟨#[.running (frontier invalidBytes true [⟨invalidBytes, false⟩]) none], {}, 0⟩ {} [1] GoString.empty =
      ((GoString.empty, .error (.unsupported (abortRefusal {} (AbortHead.mk invalidBytes true).entry))), none) :=
  ⟨actual_pool_string_frontier_refused _ _ _ _ _ _ (by decide +kernel),
   actual_pool_string_frontier_refused _ _ _ _ _ _ (by decide +kernel)⟩

/-- A multi-line payload's first line, with the tail bytes retained in the
record. -/
theorem multiline_terminal_retains_tail_bytes :
    execPoolWithAbort 1
      ⟨#[.running (frontier multilineBytes false []) none], {}, 0⟩ {} [7, 3] GoString.empty =
      ((GoString.empty, .error (.panic "h")), some ⟨multilineBytes, false, []⟩) :=
  actual_pool_string_frontier _ _ _ _ _ _ _ (by decide +kernel)

/-- THE TWO MEMBERS at the pool frontier of an equal re-panic: the empty
stream collapses, the stream `[1]` selects the two-line form; the record
keeps the recovered head and the tail entry either way. -/
theorem equal_repanic_two_members_at_frontier :
    execPoolWithAbort 1
      ⟨#[.running (frontier validBytes true [⟨validBytes, false⟩]) none], {}, 0⟩ {} [] GoString.empty =
      ((GoString.empty, .error (.panic "hi [recovered, repanicked]")),
        some ⟨validBytes, true, [⟨validBytes, false⟩]⟩) ∧
    execPoolWithAbort 1
      ⟨#[.running (frontier validBytes true [⟨validBytes, false⟩]) none], {}, 0⟩ {} [1] GoString.empty =
      ((GoString.empty, .error (.panic "hi [recovered]")),
        some ⟨validBytes, true, [⟨validBytes, false⟩]⟩) :=
  ⟨actual_pool_string_frontier _ _ _ _ _ _ _ (by decide +kernel),
   actual_pool_string_frontier _ _ _ _ _ _ _ (by decide +kernel)⟩

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

/-- Executable whole-program challenges through the actual pool observer
(tests, not kernel theorems): the D5 refusal by name, the multi-line first
line, and the equal re-panic's TWO members from two streams — the typed
two-outcome demonstration on an admitted program. -/
def checkPanic (label : String) (p : Program) (fuel : Nat) (ch : Choices) (message : String)
    (bytes : GoString) (recovered : Bool) (tail : List (GoString × Bool)) : IO Unit := do
  match runProgramPoolWithAbort fuel p "entry" #[] ch with
  | (.error (.panic actual, out), some record) =>
      unless actual == message && out == GoString.empty && record.bytes == bytes &&
          record.recovered == recovered && record.tail.map (fun h => (h.bytes, h.recovered)) == tail do
        throw <| IO.userError s!"terminal challenge {label}: wrong member/output/record: {actual}"
  | _ => throw <| IO.userError s!"terminal challenge {label}: expected actual panic record"

def checkRefused (label : String) (p : Program) (fuel : Nat) (ch : Choices) : IO Unit := do
  match runProgramPoolWithAbort fuel p "entry" #[] ch with
  | (.error (.unsupported reason, out), none) =>
      unless out == GoString.empty &&
          reason.startsWith "panic abort rendering: the string payload's first line is not valid UTF-8" do
        throw <| IO.userError s!"terminal challenge {label}: refusal did not name its cause: {reason}"
  | _ => throw <| IO.userError s!"terminal challenge {label}: expected the named D5 refusal"

#eval checkRefused "invalid UTF-8 first line (D5)" (payloadProgram invalidBytes) 16 [7, 3]
#eval checkRefused "invalid UTF-8 equal re-panic, pick 0" (repanicProgram invalidBytes) 50 [0]
#eval checkRefused "invalid UTF-8 equal re-panic, pick 1" (repanicProgram invalidBytes) 50 [1]
#eval checkPanic "multiline" (payloadProgram multilineBytes) 16 [7, 3] "h" multilineBytes false []
#eval checkPanic "equal re-panic, slot 0 (collapse)" (repanicProgram validBytes) 50 []
  "hi [recovered, repanicked]" validBytes true [(validBytes, false)]
#eval checkPanic "equal re-panic, slot 1 (two-line form)" (repanicProgram validBytes) 50 [1]
  "hi [recovered]" validBytes true [(validBytes, false)]

end GoLean.GoCore.RecoveryRuntime.TerminalTests
