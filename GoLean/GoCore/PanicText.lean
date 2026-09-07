import GoLean.GoCore.Value

/-! Total text operations for the explicit-string panic member authorized by
R-1. These operations do not change Go string values or recovery semantics. -/
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

/-- The escape grammar is ASCII. Non-ASCII input bytes cannot become a
quote, backslash, x or hex digit through this byte-preserving projection. -/
def asciiChars (text : String) : List Char :=
  text.toUTF8.data.toList.map fun b => Char.ofNat b.toNat

private theorem ascii_decode_encode (chars : List Char)
    (h : ∀ c ∈ chars, c.toNat < 128) :
    (chars.flatMap String.utf8EncodeChar).map (fun b => Char.ofNat b.toNat) = chars := by
  induction chars with
  | nil => rfl
  | cons c rest ih =>
      have hc := h c (by simp)
      have hr : ∀ d ∈ rest, d.toNat < 128 := by
        intro d hd
        exact h d (by simp [hd])
      have he : String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
        have hc' : c.val.toNat < 128 := hc
        simp only [String.utf8EncodeChar, if_pos (show c.val.toNat ≤ 127 from by omega)]
        rfl
      simp [List.flatMap_cons, he, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : c.toNat < 256),
        ih hr]

theorem asciiChars_ofList (chars : List Char) (h : ∀ c ∈ chars, c.toNat < 128) :
    asciiChars (String.ofList chars) = chars := by
  simp only [asciiChars, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    List.utf8Encode, List.data_toByteArray, List.toList_toArray]
  exact ascii_decode_encode chars h

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 87 + n)

def hexValue : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

def escapeByte (b : UInt8) : List Char :=
  ['\\', 'x', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- Every byte is encoded, so literal backslashes cannot collide with
escape syntax. Quotes are part of this selected rendered member. -/
def escapeAllBytes (s : GoString) : String :=
  String.ofList ('"' :: s.bytes.toList.flatMap escapeByte ++ ['"'])

def decodeBody : List Char → Option (List UInt8)
  | ['"'] => some []
  | '\\' :: 'x' :: hi :: lo :: rest => do
      let h ← hexValue hi
      let l ← hexValue lo
      let tail ← decodeBody rest
      return UInt8.ofNat (16 * h + l) :: tail
  | _ => none

def decodeEscapedBytes (text : String) : Option GoString :=
  match asciiChars text with
  | '"' :: rest => (decodeBody rest).map fun bytes => ⟨bytes.toArray⟩
  | _ => none

private theorem byte_digits (n : Fin 256) :
    hexValue (hexDigit (n.val / 16)) = some (n.val / 16) ∧
    hexValue (hexDigit (n.val % 16)) = some (n.val % 16) := by
  have all : ∀ i : Fin 256,
      hexValue (hexDigit (i.val / 16)) = some (i.val / 16) ∧
      hexValue (hexDigit (i.val % 16)) = some (i.val % 16) := by
    decide +kernel
  exact all n

private theorem escapeByte_ascii (b : UInt8) :
    ∀ c ∈ escapeByte b, c.toNat < 128 := by
  have all : ∀ i : Fin 256, ∀ c ∈ escapeByte (UInt8.ofNat i.val), c.toNat < 128 := by
    decide +kernel
  simpa using all ⟨b.toNat, b.toNat_lt⟩

theorem escapeChars_ascii (bytes : List UInt8) :
    ∀ c ∈ ('"' :: bytes.flatMap escapeByte ++ ['"']), c.toNat < 128 := by
  intro c hc
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | ⟨b, _, hc⟩ | rfl
  · decide
  · exact escapeByte_ascii b c hc
  · decide

theorem decodeBody_escape (bytes : List UInt8) :
    decodeBody (bytes.flatMap escapeByte ++ ['"']) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
      have h := byte_digits ⟨b.toNat, b.toNat_lt⟩
      have hv : UInt8.ofNat (16 * (b.toNat / 16) + b.toNat % 16) = b := by
        have hn : 16 * (b.toNat / 16) + b.toNat % 16 = b.toNat := by omega
        rw [hn, UInt8.ofNat_toNat]
      simp only [List.flatMap_cons, escapeByte, List.cons_append, List.nil_append,
        decodeBody, h.1, h.2, ih]
      change some (UInt8.ofNat (16 * (b.toNat / 16) + b.toNat % 16) :: rest) = _
      rw [hv]

theorem decodeEscapedBytes_escapeAllBytes (s : GoString) :
    decodeEscapedBytes (escapeAllBytes s) = some s := by
  cases s with
  | mk bytes =>
      simp only [decodeEscapedBytes, escapeAllBytes,
        asciiChars_ofList _ (escapeChars_ascii bytes.toList)]
      simp [decodeBody_escape]

theorem escapeAllBytes_injective {a b : GoString}
    (h : escapeAllBytes a = escapeAllBytes b) : a = b := by
  have := congrArg decodeEscapedBytes h
  simpa [decodeEscapedBytes_escapeAllBytes] using this

end GoLean.GoCore.PanicText
