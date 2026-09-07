import GoLean.GoCore.StepFn

/-! The explicit-string abort MEMBER function and its readout theorems, over
the `repanicCollapse` tape (landing chunk L3,
`docs/2026-09-07_land-panic-text-tape.md` §2–§3; the sprint's `StringPanic`
of `819182b5`, RESTATED: the total renderer and its unconditional
` [recovered]` member are gone — the member is now indexed by the pick the
abort draws, and a string whose FIRST LINE is not valid UTF-8 has NO member
and REFUSES by name). The premises identify the actual semantic payload;
they never infer a dynamic type from text or restrict the bytes, the
recovered flag or the tail. -/
namespace GoLean.GoCore.Machine

/-- gc's suffix as a function of the head's `recovered` flag and the
COLLAPSE bit (`renderPanicHead`'s `recoveredSuffix`, with the pick already
resolved against the chain shape). -/
def collapseSuffix (recovered collapsed : Bool) : String :=
  if !recovered then "" else if collapsed then " [recovered, repanicked]" else " [recovered]"

/-- The COLLAPSE bit a pick selects on a chain: set exactly when the head is
a recovered entry with an equal successor payload (`repanicEqualNext`) and
the pick is slot 0. -/
def collapseBit (first : PanicEntry) (rest : List PanicEntry) (pick : Nat) : Bool :=
  repanicEqualNext first rest && pick == 0

theorem recoveredSuffix_eq (first : PanicEntry) (rest : List PanicEntry) (pick : Nat) :
    recoveredSuffix first rest pick = collapseSuffix first.recovered (collapseBit first rest pick) := rfl

/-- **The member function**: the abort's first line for a string payload,
given the head's `recovered` flag and the collapse bit — `none` exactly when
the payload's FIRST LINE is not valid UTF-8 (the D5 refusal). A multi-line
payload's first line carries no suffix (gc puts it on the last line,
`stringFirstLine?`). -/
def stringPanicHead (bytes : GoString) (recovered collapsed : Bool) : Option String :=
  (stringFirstLine? bytes.bytes).map fun (line, multiline) =>
    if multiline then line else line ++ collapseSuffix recovered collapsed

theorem stringPanicHead_none_iff (bytes : GoString) (recovered collapsed : Bool) :
    stringPanicHead bytes recovered collapsed = none ↔
      utf8String? (bytes.bytes.takeWhile (· != 0x0A)) = none := by
  simp [stringPanicHead, stringFirstLine?, Option.map_eq_none_iff]

/-- The first line's UTF-8 bytes ARE the payload's bytes before its first LF
(`utf8String?_bytes`). -/
theorem stringFirstLine?_bytes {bytes : Array UInt8} {line : String} {multiline : Bool}
    (h : stringFirstLine? bytes = some (line, multiline)) :
    line.toUTF8.data = bytes.takeWhile (· != 0x0A) := by
  unfold stringFirstLine? at h
  cases hd : utf8String? (bytes.takeWhile (· != 0x0A)) with
  | none => simp [hd] at h
  | some text =>
    simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact utf8String?_bytes hd

/-- The renderer on a string payload IS the member function at the pick's
collapse bit. -/
theorem renderPanicHead_string (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat)
    (hv : first.value = .interface .string (.string bytes)) :
    renderPanicHead s first rest pick =
      stringPanicHead bytes first.recovered (collapseBit first rest pick) := by
  cases first with
  | mk value recovered =>
    simp only at hv
    subst value
    rfl

/-- The runtime-error twin: the machine's `runtime.Error` payload renders
its message through the same member function. -/
theorem renderPanicHead_runtimeError (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (msg : String) (pick : Nat)
    (hv : first.value = runtimeErrorValue msg) :
    renderPanicHead s first rest pick =
      stringPanicHead (GoString.fromLeanString msg) first.recovered (collapseBit first rest pick) := by
  cases first with
  | mk value recovered =>
    simp only at hv
    subst value
    simp [renderPanicHead, renderPanicPayload, runtimeErrorValue, stringPanicHead,
      recoveredSuffix_eq]

theorem abortMsg_string (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat) (msg : String)
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered (collapseBit first rest pick) = some msg) :
    abortMsg s first rest pick = .ok msg := by
  simp [abortMsg, renderPanicHead_string s first rest bytes pick hv, hm]

/-- The refusal, BY NAME: a string payload without a member refuses with
`abortRefusal`, whichever pick the tape holds. -/
theorem abortMsg_string_refused (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat)
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered (collapseBit first rest pick) = none) :
    abortMsg s first rest pick = .error (.unsupported (abortRefusal s first)) := by
  simp [abortMsg, renderPanicHead_string s first rest bytes pick hv, hm, throw, throwThe,
    MonadExceptOf.throw]

/-- The converse: a rendered abort of a string payload is the member function's
`some`. -/
theorem abortMsg_string_ok (s : ExecState) (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat) (msg : String)
    (hv : first.value = .interface .string (.string bytes))
    (h : abortMsg s first rest pick = .ok msg) :
    stringPanicHead bytes first.recovered (collapseBit first rest pick) = some msg := by
  unfold abortMsg at h
  rw [renderPanicHead_string s first rest bytes pick hv] at h
  cases hm : stringPanicHead bytes first.recovered (collapseBit first rest pick) with
  | none => simp [hm] at h
  | some m => simp [hm] at h; exact congrArg some h

/-- The sequential abort step on a string payload: the `panic` terminal
carrying the member the STREAM's pick selects. -/
theorem stepFn_string_abort (s : ExecState) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString) (msg : String)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg) :
    stepFn s c choices = .error (.panic msg) := by
  match c, hab with
  | .panicking (f :: r) .stop, hab =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp only [stepFn, abortMsg_string s f r bytes _ msg hv hm]
      rfl

/-- …and the refusal twin: no member, the named `.unsupported` refusal. -/
theorem stepFn_string_abort_refused (s : ExecState) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = none) :
    stepFn s c choices = .error (.unsupported (abortRefusal s first)) := by
  match c, hab with
  | .panicking (f :: r) .stop, hab =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp only [stepFn, abortMsg_string_refused s f r bytes _ hv hm]
      rfl

/-- A positive fuel budget consumes the real abort step. Zero fuel still
reports exhaustion; the theorem does not silently classify it as panic. -/
theorem runConfig_string_abort (fuel : Nat) (s : ExecState) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (msg : String)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg) :
    runConfig (fuel + 1) s c choices = .error (.panic msg) := by
  match c, hab with
  | .panicking (f :: r) .stop, hab =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp only [runConfig, stepFn_string_abort s (.panicking (f :: r) .stop)
        choices f r bytes msg rfl hv hm]
      rfl

theorem runConfig_string_abort_refused (fuel : Nat) (s : ExecState) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = none) :
    runConfig (fuel + 1) s c choices = .error (.unsupported (abortRefusal s first)) := by
  match c, hab with
  | .panicking (f :: r) .stop, hab =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp only [runConfig, stepFn_string_abort_refused s (.panicking (f :: r) .stop)
        choices f r bytes rfl hv hm]
      rfl

end GoLean.GoCore.Machine
