import GoLean.GoCore.StepFn

/-! Total terminal text readout for a boxed-string panic head. The premise
identifies the actual semantic payload; it does not assume renderability,
infer dynamic type from text, or restrict the bytes/recovered flag/tail. -/
namespace GoLean.GoCore.Machine

theorem firstPanicLine_total (text : String) :
    firstPanicLine? text = some (PanicText.firstLine text) := rfl

theorem firstPanicLine_bytes {text line : String}
    (h : firstPanicLine? text = some line) :
    line.toUTF8.data = text.toUTF8.data.takeWhile (· != 10) := by
  cases Option.some.inj h
  exact PanicText.firstLine_bytes text

theorem renderStringMember_of_utf8 {s : GoString} {text : String}
    (h : utf8String? s.bytes = some text) (hb : text.toUTF8.data = s.bytes) :
    renderStringMember s = text := by
  change text.toByteArray.data = s.bytes at hb
  simp [renderStringMember, h, hb]

theorem renderStringMember_of_invalid {s : GoString}
    (h : utf8String? s.bytes = none) :
    renderStringMember s = PanicText.escapeAllBytes s := by
  simp [renderStringMember, h]

/-- Every selected payload member either is exactly the original UTF-8
bytes or is the proved reversible escape member. This theorem does not
assume the custom decoder is sound or complete. -/
theorem renderStringMember_bytes_or_escape (s : GoString) :
    (renderStringMember s).toUTF8.data = s.bytes ∨
      renderStringMember s = PanicText.escapeAllBytes s := by
  cases h : utf8String? s.bytes with
  | none => simp [renderStringMember, h]
  | some text =>
      simp only [renderStringMember, h]
      split
      · rename_i hb
        exact Or.inl (by simpa using hb)
      · exact Or.inr rfl

/-- The chosen member, including the semantic recovered flag and the
reviewed first-line projection. It does not depend on tail equality. -/
def stringPanicHead (bytes : GoString) (recovered : Bool) : String :=
  PanicText.firstLine (if recovered then renderStringMember bytes ++ " [recovered]"
    else renderStringMember bytes)

theorem renderPanicHead_string (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString)
    (hv : first.value = .interface .string (.string bytes)) :
    renderPanicHead s first rest = some (stringPanicHead bytes first.recovered) := by
  cases first with
  | mk value recovered =>
      simp only at hv
      subst value
      cases recovered <;>
        simp [renderPanicHead, renderPanicPayload, stringPanicHead, firstPanicLine?]

theorem abortMsg_string (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString)
    (hv : first.value = .interface .string (.string bytes)) :
    abortMsg s first rest = .ok (stringPanicHead bytes first.recovered) := by
  simp [abortMsg, renderPanicHead_string s first rest bytes hv]

theorem abortMsg_string_total (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry)
    (hv : ∃ bytes, first.value = .interface .string (.string bytes)) :
    ∃ msg, abortMsg s first rest = .ok msg := by
  obtain ⟨bytes, hv⟩ := hv
  exact ⟨_, abortMsg_string s first rest bytes hv⟩

theorem stepFn_string_abort (s : ExecState) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes)) :
    stepFn s c choices = .error (.panic (stringPanicHead bytes first.recovered)) := by
  match c, hab with
  | .panicking (f :: r) .stop, hab =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp only [stepFn, abortMsg_string s f r bytes hv]
      rfl

/-- A positive fuel budget consumes the real abort step. Zero fuel still
reports exhaustion; the theorem does not silently classify it as panic. -/
theorem runConfig_string_abort (fuel : Nat) (s : ExecState) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes)) :
    runConfig (fuel + 1) s c choices =
      .error (.panic (stringPanicHead bytes first.recovered)) := by
  match c, hab with
  | .panicking (f :: r) .stop, hab =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp only [runConfig, stepFn_string_abort s (.panicking (f :: r) .stop)
        choices f r bytes rfl hv]
      rfl

end GoLean.GoCore.Machine
