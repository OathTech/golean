import GoLean.Interface

/-! Kernel regressions for the first-panic-line observation boundary and
R-1's explicit-string members. Invalid bytes remain exact semantic bytes;
their reversible rendered member is not claimed to equal gc's raw text. -/
namespace GoLean.PanicRenderingTests
open GoCore GoCore.Machine

def state : ExecState := { types := TypeEnv.reserved }
def entry (text : String) (recovered := false) : PanicEntry :=
  ⟨.interface .string (.string (GoString.fromLeanString text)), recovered⟩
def rawEntry (bytes : Array UInt8) : PanicEntry :=
  ⟨.interface .string (.string ⟨bytes⟩), false⟩

theorem unicode_widths :
    renderPanicHead state (entry "aé界😀�z") [] = some "aé界😀�z" := by
  decide +kernel

theorem unicode_newline :
    renderPanicHead state (entry "é\n界") [] = some "é" := by
  decide +kernel

theorem first_line_boundaries :
    renderPanicHead state (entry "") [] = some "" ∧
    renderPanicHead state (entry "\nsecond") [] = some "" ∧
    renderPanicHead state (entry "first\n") [] = some "first" := by
  decide +kernel

theorem recovered_newline_suffix :
    renderPanicHead state (entry "first\nsecond" true) [entry "other"] = some "first" ∧
    renderPanicHead state (entry "é\n界" true) [] = some "é" := by
  decide +kernel

theorem recovered_single_line :
    renderPanicHead state (entry "é" true) [entry "other"] = some "é [recovered]" ∧
    renderPanicHead state (entry "first" true) [] = some "first [recovered]" := by
  decide +kernel

theorem runtime_error_newline :
    renderPanicHead state (panicEntry "é\n界") [] = some "é" := by
  decide +kernel

/-- The selected R-1 suffix is formatted before first-line projection. -/
theorem equal_repanic_member :
    renderPanicHead state (entry "first\nsecond" true) [entry "first\nsecond"] = some "first" ∧
    renderPanicHead state (entry "same" true) [entry "same"] = some "same [recovered]" := by
  decide +kernel

/-- Invalid bytes are escaped in full, including bytes after the newline.
U+FFFD encoded correctly is covered above and is not confused with ff. -/
theorem invalid_utf8_member :
    [#[0xff], #[0x80], #[0xc0, 0x80], #[0xe0, 0x80, 0x80],
      #[0xed, 0xa0, 0x80], #[0xe2, 0x82], #[0xf0, 0x80, 0x80, 0x80],
      #[0xf4, 0x90, 0x80, 0x80], #[0x61, 0x0a, 0xff]].all
      (fun bytes => renderPanicHead state (rawEntry bytes) [] ==
        some (PanicText.escapeAllBytes ⟨bytes⟩)) = true := by
  decide +kernel

end GoLean.PanicRenderingTests
