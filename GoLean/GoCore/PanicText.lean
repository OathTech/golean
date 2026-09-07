import GoLean.GoCore.Value

/-! Constructive first-line text helpers for the abort renderer (landed by
chunk L1 consumer-free; the renderer itself projects the first line at the
BYTE level — `Machine.stringFirstLine?` — and these String-level helpers
are the proved bridge between the two projections). The `escapeAllBytes`
half this module carried on the sprint branch — a quoted `"\xHH"` rendering
of invalid UTF-8 that no Go toolchain prints — was DELETED at landing chunk
L3 (`docs/2026-09-07_land-panic-text-tape.md` §2.3, decision D5: the
escape form is never a member; invalid first-line bytes REFUSE by name).
These operations do not change Go string values or recovery semantics. -/
namespace GoLean.GoCore.PanicText

private theorem utf8EncodeChar_no_lf (c : Char) (hc : c ≠ '\n') :
    ∀ b ∈ String.utf8EncodeChar c, b != (10 : UInt8) := by
  have hn : c.val.toNat ≠ 10 := by
    intro h
    apply hc
    apply Char.ext
    exact UInt32.toNat_inj.mp h
  intro b hb
  simp only [bne_iff_ne]
  intro he
  subst b
  simp only [String.utf8EncodeChar] at hb
  split at hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false,
      ← UInt8.toNat_inj, UInt8.toNat_ofNat', UInt8.reduceToNat] at hb
    omega
  · split at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false,
        ← UInt8.toNat_inj, UInt8.toNat_ofNat', UInt8.reduceToNat] at hb
      omega
    · split at hb <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false,
          ← UInt8.toNat_inj, UInt8.toNat_ofNat', UInt8.reduceToNat] at hb <;>
        omega

theorem utf8_firstLine_list (chars : List Char) :
    (chars.takeWhile (· != '\n')).flatMap String.utf8EncodeChar =
      (chars.flatMap String.utf8EncodeChar).takeWhile (· != (10 : UInt8)) := by
  induction chars with
  | nil => rfl
  | cons c rest ih =>
      by_cases hc : c = '\n'
      · subst c
        simp [List.takeWhile, String.utf8EncodeChar, List.flatMap_cons]
      · rw [List.takeWhile_cons_of_pos (by simpa using hc), List.flatMap_cons,
          List.flatMap_cons, List.takeWhile_append_of_pos (utf8EncodeChar_no_lf c hc), ih]

theorem lfPrefix_valid (bytes : ByteArray) (h : bytes.IsValidUTF8) :
    (ByteArray.mk (bytes.data.takeWhile (· != 10))).IsValidUTF8 := by
  obtain ⟨chars, rfl⟩ := h
  refine ⟨chars.takeWhile (· != '\n'), ?_⟩
  apply ByteArray.ext
  simp only [List.utf8Encode,
    List.data_toByteArray, ← List.takeWhile_toArray, utf8_firstLine_list]

/-- Project a valid Lean string before its first LF. The prefix is proved
valid constructively, then wrapped without decoding or replacement. -/
def firstLine (text : String) : String :=
  String.ofByteArray ⟨text.toUTF8.data.takeWhile (· != 10)⟩
    (lfPrefix_valid text.toUTF8 text.isValidUTF8)

theorem firstLine_bytes (text : String) :
    (firstLine text).toUTF8.data = text.toUTF8.data.takeWhile (· != 10) := rfl

end GoLean.GoCore.PanicText
