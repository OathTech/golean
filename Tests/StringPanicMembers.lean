import GoLean.GoCore.StringPanic

/-! The explicit-string member function at the machine's abort (landing chunk
L3; the sprint's `Tests/StringPanicMembers` of `819182b5`, RESTATED over the
`repanicCollapse` tape and the D5 refusal: the escape member is gone, the
collapse is a pick, the refusal is a named `.unsupported`). -/
namespace GoLean.StringPanicMembersTests
open GoCore GoCore.Machine

def state : ExecState := { types := TypeEnv.reserved }
def entry (bytes : Array UInt8) (recovered := false) : PanicEntry :=
  ⟨.interface .string (.string ⟨bytes⟩), recovered⟩

theorem invalid_first_line_refused :
    renderPanicHead state (entry #[0xff]) [] 0 = none ∧
    renderPanicHead state (entry #[0xff, 0x5a, 0x0a, 0x59]) [] 0 = none ∧
    stringPanicHead ⟨#[0xff, 0x5a]⟩ true true = none ∧
    stringPanicHead ⟨#[0xff, 0x5a]⟩ true false = none := by
  decide +kernel

theorem invalid_after_lf_member :
    renderPanicHead state (entry #[0x61, 0x0a, 0xff]) [] 0 = some "a" ∧
    stringPanicHead ⟨#[0x61, 0x0a, 0xff]⟩ true true = some "a" := by
  decide +kernel

theorem equal_repanic_members :
    renderPanicHead state (entry #[0x61] true) [entry #[0x61]] 0 = some "a [recovered, repanicked]" ∧
    renderPanicHead state (entry #[0x61] true) [entry #[0x61]] 1 = some "a [recovered]" ∧
    stringPanicHead ⟨#[0x61]⟩ true true = some "a [recovered, repanicked]" ∧
    stringPanicHead ⟨#[0x61]⟩ true false = some "a [recovered]" ∧
    stringPanicHead ⟨#[0x61]⟩ false true = some "a" := by
  decide +kernel

/-- The member function IS the renderer on string payloads, at the pick's
collapse bit (an instance of `renderPanicHead_string`). -/
theorem member_is_renderer (bytes : Array UInt8) (recovered : Bool)
    (rest : List PanicEntry) (pick : Nat) :
    renderPanicHead state (entry bytes recovered) rest pick =
      stringPanicHead ⟨bytes⟩ recovered (collapseBit (entry bytes recovered) rest pick) :=
  renderPanicHead_string state _ rest ⟨bytes⟩ pick rfl

/-- The actual abort step is the member the STREAM's pick selects, or the
named refusal — for every byte string, flag, tail, stream and fuel. -/
theorem generic_actual_abort (bytes : Array UInt8) (recovered : Bool)
    (rest : List PanicEntry) (choices : Choices) (fuel : Nat) (msg : String)
    (hm : stringPanicHead ⟨bytes⟩ recovered
      (collapseBit (entry bytes recovered) rest (abortConsult (entry bytes recovered) rest choices).1)
      = some msg) :
    runConfig (fuel + 1) state (.panicking (entry bytes recovered :: rest) .stop) choices =
      .error (.panic msg) :=
  runConfig_string_abort fuel state (.panicking (entry bytes recovered :: rest) .stop)
    choices (entry bytes recovered) rest ⟨bytes⟩ msg rfl rfl hm

theorem generic_actual_abort_refused (bytes : Array UInt8) (recovered : Bool)
    (rest : List PanicEntry) (choices : Choices) (fuel : Nat)
    (hm : stringPanicHead ⟨bytes⟩ recovered
      (collapseBit (entry bytes recovered) rest (abortConsult (entry bytes recovered) rest choices).1)
      = none) :
    runConfig (fuel + 1) state (.panicking (entry bytes recovered :: rest) .stop) choices =
      .error (.unsupported (abortRefusal state (entry bytes recovered))) :=
  runConfig_string_abort_refused fuel state (.panicking (entry bytes recovered :: rest) .stop)
    choices (entry bytes recovered) rest ⟨bytes⟩ rfl rfl hm

theorem abort_zero_fuel :
    runConfig 0 state (.panicking [entry #[0xff]] .stop) [] = .error .fuelOut := by
  rfl

/-- The two members at the machine's own abort: the empty stream (slot 0)
collapses, the stream `[1]` selects the two-line form. -/
theorem actual_abort_pin_collapse :
    runConfig 1 state (.panicking [entry #[0x61] true, entry #[0x61]] .stop) [] =
      .error (.panic "a [recovered, repanicked]") := by
  rw [runConfig_string_abort 0 state _ [] _ _ ⟨#[0x61]⟩ "a [recovered, repanicked]" rfl rfl
    (by decide +kernel)]

theorem actual_abort_pin_two_line :
    runConfig 1 state (.panicking [entry #[0x61] true, entry #[0x61]] .stop) [1] =
      .error (.panic "a [recovered]") := by
  rw [runConfig_string_abort 0 state _ [1] _ _ ⟨#[0x61]⟩ "a [recovered]" rfl rfl
    (by decide +kernel)]

/-- Outside the recovered-equal shape the pick is inert: the stream `[1]`
renders the forced ` [recovered]` too. -/
theorem actual_abort_unequal_inert :
    runConfig 1 state (.panicking [entry #[0x61] true, entry #[0x62]] .stop) [1] =
      .error (.panic "a [recovered]") := by
  rw [runConfig_string_abort 0 state _ [1] _ _ ⟨#[0x61]⟩ "a [recovered]" rfl rfl
    (by decide +kernel)]

/-- The D5 refusal at the machine's own abort, by name, under both picks. -/
theorem actual_abort_refused :
    runConfig 1 state (.panicking [entry #[0xff, 0x5a] true, entry #[0xff, 0x5a]] .stop) [] =
      .error (.unsupported (abortRefusal state (entry #[0xff, 0x5a] true))) ∧
    runConfig 1 state (.panicking [entry #[0xff, 0x5a] true, entry #[0xff, 0x5a]] .stop) [1] =
      .error (.unsupported (abortRefusal state (entry #[0xff, 0x5a] true))) :=
  ⟨runConfig_string_abort_refused 0 state _ [] _ _ ⟨#[0xff, 0x5a]⟩ rfl rfl (by decide +kernel),
   runConfig_string_abort_refused 0 state _ [1] _ _ ⟨#[0xff, 0x5a]⟩ rfl rfl (by decide +kernel)⟩

end GoLean.StringPanicMembersTests
