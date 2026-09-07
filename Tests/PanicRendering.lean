import GoLean.Interface

/-! Kernel regressions for the first-panic-line observation boundary over the
`repanicCollapse` tape (landing chunk L3, `docs/2026-09-07_land-panic-text-tape.md`;
the sprint's `Tests/PanicRendering` of `ff7173dd`/`819182b5`, RESTATED
choice-indexed). Every claim below is against the gc witness table
(`docs/evidence/2026-09-07_land-panic-text-tape/witness/table.tsv`): valid
UTF-8 first lines render byte-exactly; a multi-line payload's first line
carries no suffix; the equal re-panic collapse is a two-member PICK; a
first line that is not valid UTF-8 has no member (the D5 refusal) — no
`"\xHH"` form is ever produced. -/
namespace GoLean.PanicRenderingTests
open GoCore GoCore.Machine

def state : ExecState := { types := TypeEnv.reserved }
def entry (text : String) (recovered := false) : PanicEntry :=
  ⟨.interface .string (.string (GoString.fromLeanString text)), recovered⟩
def rawEntry (bytes : Array UInt8) (recovered := false) : PanicEntry :=
  ⟨.interface .string (.string ⟨bytes⟩), recovered⟩

/-- Witness w12: `aé界😀z` renders verbatim (a correctly encoded U+FFFD is
kept — it is three bytes, not the decoder's width-1 sentinel). -/
theorem unicode_widths :
    renderPanicHead state (entry "aé界😀�z") [] 0 = some "aé界😀�z" := by
  decide +kernel

/-- Witness w13-shape: the first line stops at the first LF. -/
theorem unicode_newline :
    renderPanicHead state (entry "é\n界") [] 0 = some "é" := by
  decide +kernel

theorem first_line_boundaries :
    renderPanicHead state (entry "") [] 0 = some "" ∧
    renderPanicHead state (entry "\nsecond") [] 0 = some "" ∧
    renderPanicHead state (entry "first\n") [] 0 = some "first" := by
  decide +kernel

/-- Witnesses w14/w15: gc writes the suffix after the WHOLE payload, so a
multi-line payload's first line carries none — under either pick. -/
theorem recovered_multiline_no_suffix :
    renderPanicHead state (entry "first\nsecond" true) [entry "other"] 0 = some "first" ∧
    renderPanicHead state (entry "é\n界" true) [] 0 = some "é" ∧
    renderPanicHead state (entry "first\nsecond" true) [entry "first\nsecond"] 0 = some "first" ∧
    renderPanicHead state (entry "first\nsecond" true) [entry "first\nsecond"] 1 = some "first" := by
  decide +kernel

/-- Unequal adjacent payloads: ` [recovered]` is FORCED (width 1) — the pick
is inert. -/
theorem recovered_single_line_forced :
    renderPanicHead state (entry "é" true) [entry "other"] 0 = some "é [recovered]" ∧
    renderPanicHead state (entry "é" true) [entry "other"] 1 = some "é [recovered]" ∧
    renderPanicHead state (entry "first" true) [] 0 = some "first [recovered]" ∧
    repanicCollapseWidth (entry "é" true) [entry "other"] = 1 ∧
    repanicCollapseWidth (entry "first" true) [] = 1 := by
  decide +kernel

theorem runtime_error_newline :
    renderPanicHead state (panicEntry "é\n界") [] 0 = some "é" := by
  decide +kernel

/-- THE SITE (witnesses w01 vs w03): an equal re-panic of a recovered head is
a two-member envelope — slot 0 collapses, slot 1 is the two-line form's
first line; the width is 2 exactly there and 1 for an unrecovered head. -/
theorem equal_repanic_members :
    renderPanicHead state (entry "same" true) [entry "same"] 0 = some "same [recovered, repanicked]" ∧
    renderPanicHead state (entry "same" true) [entry "same"] 1 = some "same [recovered]" ∧
    repanicCollapseWidth (entry "same" true) [entry "same"] = 2 ∧
    repanicCollapseWidth (entry "same") [entry "same"] = 1 ∧
    renderPanicHead state (entry "same") [entry "same"] 0 = some "same" ∧
    renderPanicHead state (entry "same") [entry "same"] 1 = some "same" := by
  decide +kernel

/-- The site is uniform across payload families (w08, w27, w22, w31): bool,
defined-free int, the `panic(nil)` runtime error and a runtime fault all
render both members. -/
theorem equal_repanic_other_families :
    renderPanicHead state ⟨.interface .bool (.bool true), true⟩
      [⟨.interface .bool (.bool true), false⟩] 0 = some "true [recovered, repanicked]" ∧
    renderPanicHead state ⟨.interface .bool (.bool true), true⟩
      [⟨.interface .bool (.bool true), false⟩] 1 = some "true [recovered]" ∧
    renderPanicHead state ⟨.interface (.int .int) (.int 7 .int), true⟩
      [⟨.interface (.int .int) (.int 7 .int), false⟩] 0 = some "7 [recovered, repanicked]" ∧
    renderPanicHead state ⟨.interface (.int .int) (.int 7 .int), true⟩
      [⟨.interface (.int .int) (.int 7 .int), false⟩] 1 = some "7 [recovered]" ∧
    renderPanicHead state ⟨panicPayload .nil, true⟩ [⟨panicPayload .nil, false⟩] 0
      = some "panic called with nil argument [recovered, repanicked]" ∧
    renderPanicHead state ⟨panicPayload .nil, true⟩ [⟨panicPayload .nil, false⟩] 1
      = some "panic called with nil argument [recovered]" ∧
    renderPanicHead state ⟨runtimeErrorValue nilDerefPanicText, true⟩
      [⟨runtimeErrorValue nilDerefPanicText, false⟩] 0
      = some (nilDerefPanicText ++ " [recovered, repanicked]") := by
  decide +kernel

/-- D5 (witnesses w17/w35/w37): a first line that is not valid UTF-8 has NO
member — every invalid-encoding class refuses, under either pick, and no
`"\xHH"` form is produced. -/
theorem invalid_utf8_first_line_refused :
    [#[0xff], #[0x80], #[0xc0, 0x80], #[0xe0, 0x80, 0x80],
      #[0xed, 0xa0, 0x80], #[0xe2, 0x82], #[0xf0, 0x80, 0x80, 0x80],
      #[0xf4, 0x90, 0x80, 0x80], #[0xff, 0x5a, 0x0a, 0x59]].all
      (fun bytes => (renderPanicHead state (rawEntry bytes) [] 0).isNone
        && (renderPanicHead state (rawEntry bytes true) [rawEntry bytes] 0).isNone
        && (renderPanicHead state (rawEntry bytes true) [rawEntry bytes] 1).isNone) = true := by
  decide +kernel

/-- Witness w16: a valid FIRST line renders even when a later line is not
valid UTF-8 — the observation is the first line, and its bytes are gc's. -/
theorem invalid_after_lf_renders :
    renderPanicHead state (rawEntry #[0x61, 0x0a, 0xff]) [] 0 = some "a" ∧
    renderPanicHead state (rawEntry #[0xc3, 0xa9, 0x0a, 0xff]) [] 0 = some "é" := by
  decide +kernel

/-- The strict decoder round-trips: a `some` answer's UTF-8 bytes are the
payload bytes (the theorem `utf8String?_bytes`, here at one instance). -/
theorem decoder_bytes_exact :
    (utf8String? #[0x61, 0xc3, 0xa9]).map (·.toUTF8.data) = some #[0x61, 0xc3, 0xa9] := by
  decide +kernel

/-- The refusal names its cause (fail closed BY NAME). -/
theorem refusal_names_the_cause :
    (abortRefusal state (rawEntry #[0xff, 0x5a])).startsWith
      "panic abort rendering: the string payload's first line is not valid UTF-8" = true := by
  decide +kernel

end GoLean.PanicRenderingTests
