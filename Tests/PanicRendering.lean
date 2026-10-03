import GoLean.GoCore.Machine

/-! Re-homed 2026-09-16 (`docs/2026-09-16_typed-profiles-parked.md` §3): the import was the
parked facade `GoLean.Interface`; every name below is the CORE renderer's (`GoLean/GoCore/Machine.lean`,
`Ops.lean`), so the module now imports it directly. Content unchanged.

Kernel regressions for the first-panic-line observation boundary over the
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

/-- The renderers' fixture: a CONTEXT since B7 (the old `{ types := TypeEnv.reserved }`
state; every renderer under test reads the context only). -/
def state : ProgramCtx := ProgramCtx.ofTables (types := TypeEnv.reserved)
def entry (text : String) (recovered := false) : PanicEntry :=
  { value := .interface .string (.string (GoString.fromLeanString text)), recovered }
def rawEntry (bytes : Array UInt8) (recovered := false) : PanicEntry :=
  { value := .interface .string (.string ⟨bytes⟩), recovered }
/-- An un-rewritten entry of any payload (the value arms' families). -/
def plain (v : GoValue) (recovered := false) : PanicEntry := { value := v, recovered }

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
    renderPanicHead state (plain (.interface .bool (.bool true)) true)
      [plain (.interface .bool (.bool true))] 0 = some "true [recovered, repanicked]" ∧
    renderPanicHead state (plain (.interface .bool (.bool true)) true)
      [plain (.interface .bool (.bool true))] 1 = some "true [recovered]" ∧
    renderPanicHead state (plain (.interface (.int .int) (.int 7 .int)) true)
      [plain (.interface (.int .int) (.int 7 .int))] 0 = some "7 [recovered, repanicked]" ∧
    renderPanicHead state (plain (.interface (.int .int) (.int 7 .int)) true)
      [plain (.interface (.int .int) (.int 7 .int))] 1 = some "7 [recovered]" ∧
    renderPanicHead state (plain (panicPayload .nil) true) [plain (panicPayload .nil)] 0
      = some "panic called with nil argument [recovered, repanicked]" ∧
    renderPanicHead state (plain (panicPayload .nil) true) [plain (panicPayload .nil)] 1
      = some "panic called with nil argument [recovered]" ∧
    renderPanicHead state (plain (runtimeErrorValue nilDerefPanicText) true)
      [plain (runtimeErrorValue nilDerefPanicText)] 0
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

/-! ## Unit 6b (BUG-004 item 4): the REWRITTEN payload and the phase's records -/

/-- A defined-type box (index 7 — any index other than the twin's) whose rewrite is
owed, done, or unrecorded. -/
def boxed (rewrite : Rewrite) (recovered := false) (repanicked := false) : PanicEntry :=
  { value := .interface (.defined 7) (.int 9 .int), recovered, rewrite, repanicked }

/-- The stored text prints as a string payload: first line, suffix by the flags
(the phase's `repanicked` record selects ` [recovered, repanicked]` on a
recovered head with NO abort-time draw); a `.pending`/`.unrecorded` entry has
no member (fail closed by name). -/
theorem rewritten_text_renders :
    renderPanicHead state (boxed (.done (GoString.fromLeanString "boom"))) [] 0 = some "boom" ∧
    renderPanicHead state (boxed (.done (GoString.fromLeanString "line-one\nline-two"))) [] 0
      = some "line-one" ∧
    renderPanicHead state (boxed (.done (GoString.fromLeanString "same")) true true) [] 1
      = some "same [recovered, repanicked]" ∧
    renderPanicHead state (boxed (.done (GoString.fromLeanString "same")) true false) [] 0
      = some "same [recovered]" ∧
    renderPanicHead state (boxed (.done (GoString.fromLeanString "same")) false true) [] 0
      = some "same" ∧
    (renderPanicHead state (boxed (.pending ⟨"Error", ""⟩)) [] 0).isNone ∧
    (renderPanicHead state (boxed .unrecorded) [] 0).isNone ∧
    (renderPanicHead state (boxed (.done ⟨#[0xff]⟩)) [] 0).isNone := by
  decide +kernel

/-- A rewritten head draws nothing at the abort even beside an equal successor
(`repanicEqualNext` requires an un-rewritten head): width 1, the suffix from
the phase's record alone. -/
theorem rewritten_head_no_abort_draw :
    repanicCollapseWidth (boxed (.done (GoString.fromLeanString "x")) true)
      [boxed (.done (GoString.fromLeanString "x"))] = 1 ∧
    repanicEqualNext (boxed (.done (GoString.fromLeanString "x")) true)
      [boxed (.done (GoString.fromLeanString "x"))] = false := by
  decide +kernel

/-- The phase's cursor and collapse: the newest pending entry is split out
(the settled `newer` suffix kept), a collision marks the older entry and drops
the newer; the abort is `none` while a rewrite is owed. -/
theorem phase_cursor_and_collapse :
    (splitNewestPending? [boxed (.pending ⟨"Error", ""⟩) true, boxed (.pending ⟨"Error", ""⟩),
        boxed (.done (GoString.fromLeanString "t"))]
      == some ([boxed (.pending ⟨"Error", ""⟩) true], boxed (.pending ⟨"Error", ""⟩),
          [boxed (.done (GoString.fromLeanString "t"))])) = true ∧
    (splitNewestPending? [boxed (.done (GoString.fromLeanString "t")), entry "s"]).isNone = true ∧
    preprintCollide [boxed (.pending ⟨"Error", ""⟩) true] (boxed (.pending ⟨"Error", ""⟩)) = true ∧
    preprintCollide [entry "s"] (boxed (.pending ⟨"Error", ""⟩)) = false ∧
    (preprintDrop [boxed (.pending ⟨"Error", ""⟩) true] [entry "s"]
      == [boxed (.pending ⟨"Error", ""⟩) true true, entry "s"]) = true ∧
    (Config.abort? (.panicking [boxed (.pending ⟨"Error", ""⟩)] .stop)).isNone = true ∧
    (Config.abort? (.panicking [boxed (.done (GoString.fromLeanString "t"))] .stop)
      == some (boxed (.done (GoString.fromLeanString "t")), [])) = true := by
  decide +kernel

/-- The fatal text (decision 4): exact for a string payload's first line; a
runtime-error payload is refused by name (BUG-099). -/
theorem preprint_fatal_text :
    (preprintFatalStop state [entry "inner-string"]
      == .fatal "panic while printing panic value: inner-string") = true ∧
    (preprintFatalStop state [entry "a\nb"] == .fatal "panic while printing panic value: a") = true ∧
    (match preprintFatalStop state [panicEntry nilDerefPanicText] with
      | .unsupported _ => true
      | _ => false) = true := by
  decide +kernel

end GoLean.PanicRenderingTests
