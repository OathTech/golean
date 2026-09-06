import GoLean.GoCore.StringPanic

namespace GoLean.StringPanicMembersTests
open GoCore GoCore.Machine
def state : ExecState := { types := TypeEnv.reserved }
def entry (bytes : Array UInt8) (recovered := false) : PanicEntry :=
  ⟨.interface .string (.string ⟨bytes⟩), recovered⟩

theorem invalid_before_lf : renderPanicHead state (entry #[0xff]) [] = some "\"\\xff\"" := by
  decide +kernel
theorem invalid_after_lf : renderPanicHead state (entry #[0x61, 0x0a, 0xff]) [] =
    some "\"\\x61\\x0a\\xff\"" := by
  decide +kernel
theorem equal_repanic : renderPanicHead state (entry #[0x61] true) [entry #[0x61]] =
    some "a [recovered]" := by
  decide +kernel
theorem invalid_recovered :
    renderPanicHead state (entry #[0xff, 0x00, 0x5c, 0x0a] true)
      [entry #[0xff, 0x00, 0x5c, 0x0a]] =
      some "\"\\xff\\x00\\x5c\\x0a\" [recovered]" := by
  decide +kernel

theorem non_string_boundary :
    renderPanicHead state ⟨.interface .bool (.bool true), true⟩
      [⟨.interface .bool (.bool true), false⟩] = none := by
  decide +kernel

theorem exact_roundtrip (bytes : Array UInt8) :
    PanicText.decodeEscapedBytes (PanicText.escapeAllBytes ⟨bytes⟩) = some ⟨bytes⟩ :=
  PanicText.decodeEscapedBytes_escapeAllBytes _

theorem malformed_escape_rejected :
    ["\"\\xfg\"", "\"\\xff\"extra", "\"\\x0\"", "\\xff", "\"\\xff", "\"\\xĀ0\""].all
      (fun text => (PanicText.decodeEscapedBytes text).isNone) = true := by
  decide +kernel

/-- R-1 text is not a semantic value encoding. A valid literal may spell
the selected escape syntax; the actual chain bytes must remain evidence. -/
theorem rendered_text_does_not_identify_bytes :
    renderStringMember ⟨#[0xff]⟩ =
      renderStringMember (GoString.fromLeanString "\"\\xff\"") ∧
    (#[0xff] : Array UInt8) ≠ (GoString.fromLeanString "\"\\xff\"").bytes := by
  decide +kernel

theorem generic_actual_abort (bytes : Array UInt8) (recovered : Bool)
    (rest : List PanicEntry) (choices : Choices) (fuel : Nat) :
    runConfig (fuel + 1) state (.panicking (entry bytes recovered :: rest) .stop) choices =
      .error (.panic (stringPanicHead ⟨bytes⟩ recovered)) :=
  runConfig_string_abort fuel state (.panicking (entry bytes recovered :: rest) .stop)
    choices (entry bytes recovered) rest ⟨bytes⟩ rfl rfl

theorem abort_zero_fuel :
    runConfig 0 state (.panicking [entry #[0xff]] .stop) [] = .error .fuelOut := by
  rfl

theorem actual_abort_pin :
    runConfig 1 state (.panicking [entry #[0xff] true, entry #[0xff]] .stop) [] =
      .error (.panic "\"\\xff\" [recovered]") := by
  rw [runConfig_string_abort 0 state _ [] _ _ ⟨#[0xff]⟩ rfl rfl]
  have hm : stringPanicHead ⟨#[0xff]⟩ true = "\"\\xff\" [recovered]" := by
    decide +kernel
  exact congrArg (fun msg => Except.error (Stop.panic msg)) hm
end GoLean.StringPanicMembersTests
