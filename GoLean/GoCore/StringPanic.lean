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

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)

/-- gc's suffix as a function of the head's `recovered` flag and the
COLLAPSE bit (`renderPanicHead`'s `recoveredSuffix`, with the pick already
resolved against the chain shape). -/
def collapseSuffix (recovered collapsed : Bool) : String :=
  if !recovered then "" else if collapsed then " [recovered, repanicked]" else " [recovered]"

/-- The COLLAPSE bit a pick selects on a chain: set exactly when the head
carries the preprint phase's `repanicked` record (unit 6b — the phase drew
the pair's identity at ITS `repanicCollapse` consult), or the head is a
recovered, un-rewritten entry with an equal successor payload
(`repanicEqualNext`) and the pick is slot 0. -/
def collapseBit (first : PanicEntry) (rest : List PanicEntry) (pick : Nat) : Bool :=
  first.repanicked || (repanicEqualNext first rest && pick == 0)

variable {ctx}
theorem recoveredSuffix_eq (first : PanicEntry) (rest : List PanicEntry) (pick : Nat) :
    recoveredSuffix first rest pick = collapseSuffix first.recovered (collapseBit first rest pick) := rfl

variable (ctx)
/-- **The member function**: the abort's first line for a string payload,
given the head's `recovered` flag and the collapse bit — `none` exactly when
the payload's FIRST LINE is not valid UTF-8 (the D5 refusal). A multi-line
payload's first line carries no suffix (gc puts it on the last line,
`stringFirstLine?`). -/
def stringPanicHead (bytes : GoString) (recovered collapsed : Bool) : Option String :=
  (stringFirstLine? bytes.bytes).map fun (line, multiline) =>
    if multiline then line else line ++ collapseSuffix recovered collapsed

variable {ctx}
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
theorem renderPanicHead_string (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat)
    (hv : first.value = .interface .string (.string bytes)) :
    renderPanicHead ctx first rest pick =
      stringPanicHead bytes first.recovered (collapseBit first rest pick) := by
  cases first with
  | mk value recovered rewrite repanicked =>
    simp only at hv
    subst value
    rfl

/-- The runtime-error twin: the machine's `runtime.Error` payload renders
its message through the same member function. -/
theorem renderPanicHead_runtimeError (first : PanicEntry)
    (rest : List PanicEntry) (msg : String) (pick : Nat)
    (hv : first.value = runtimeErrorValue msg) :
    renderPanicHead ctx first rest pick =
      stringPanicHead (GoString.fromLeanString msg) first.recovered (collapseBit first rest pick) := by
  cases first with
  | mk value recovered rewrite repanicked =>
    simp only at hv
    subst value
    simp [renderPanicHead, renderPanicPayload, runtimeErrorValue, stringPanicHead,
      recoveredSuffix_eq]

theorem abortMsg_string (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat) (msg : String)
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered (collapseBit first rest pick) = some msg) :
    abortMsg ctx first rest pick = .ok msg := by
  simp [abortMsg, renderPanicHead_string first rest bytes pick hv, hm]

/-- The refusal, BY NAME: a string payload without a member refuses with
`abortRefusal`, whichever pick the tape holds. -/
theorem abortMsg_string_refused (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat)
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered (collapseBit first rest pick) = none) :
    abortMsg ctx first rest pick = .error (.unsupported (abortRefusal ctx first)) := by
  simp [abortMsg, renderPanicHead_string first rest bytes pick hv, hm, throw, throwThe,
    MonadExceptOf.throw]

/-- The converse: a rendered abort of a string payload is the member function's
`some`. -/
theorem abortMsg_string_ok (first : PanicEntry)
    (rest : List PanicEntry) (bytes : GoString) (pick : Nat) (msg : String)
    (hv : first.value = .interface .string (.string bytes))
    (h : abortMsg ctx first rest pick = .ok msg) :
    stringPanicHead bytes first.recovered (collapseBit first rest pick) = some msg := by
  unfold abortMsg at h
  rw [renderPanicHead_string first rest bytes pick hv] at h
  cases hm : stringPanicHead bytes first.recovered (collapseBit first rest pick) with
  | none => simp [hm] at h
  | some m => simp [hm] at h; exact congrArg some h

/-- The sequential abort step on a string payload: the `panic` terminal
carrying the member the STREAM's pick selects. -/
theorem stepFn_string_abort (s : Store) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString) (msg : String)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg) :
    stepFn ctx s c choices = .error (.panic msg) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [stepFn, stepPanicStop, hs, abortMsg_string first rest bytes _ msg hv hm]
  rfl

/-- …and the refusal twin: no member, the named `.unsupported` refusal. -/
theorem stepFn_string_abort_refused (s : Store) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = none) :
    stepFn ctx s c choices = .error (.unsupported (abortRefusal ctx first)) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [stepFn, stepPanicStop, hs, abortMsg_string_refused first rest bytes _ hv hm]
  rfl

/-- A positive fuel budget consumes the real abort step. Zero fuel still
reports exhaustion; the theorem does not silently classify it as panic. -/
theorem runConfig_string_abort (fuel : Nat) (s : Store) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (msg : String)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg) :
    runConfig ctx (fuel + 1) s c choices = .error (.panic msg) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [runConfig, stepFn_string_abort s (.panicking (first :: rest) .stop)
    choices first rest bytes msg (Config.abort?_of_settled hs) hv hm]
  rfl

theorem runConfig_string_abort_refused (fuel : Nat) (s : Store) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (bytes : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : first.value = .interface .string (.string bytes))
    (hm : stringPanicHead bytes first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = none) :
    runConfig ctx (fuel + 1) s c choices = .error (.unsupported (abortRefusal ctx first)) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [runConfig, stepFn_string_abort_refused s (.panicking (first :: rest) .stop)
    choices first rest bytes (Config.abort?_of_settled hs) hv hm]
  rfl

/-! ## The REWRITTEN payload's member (BUG-004 item 4, window unit 6b)

The preprint phase (`Cont.preprintK`, Machine.lean) CALLED the payload's
`Error()`/`String()` and stored the returned string beside the payload
(`Rewrite.done text`); the abort then prints that text exactly as a string
payload — the same member function `stringPanicHead`, the same first-line
rule and D5 refusal, the suffix from the head's `recovered` flag and the
collapse bit (which now also reads the phase's `repanicked` record). The
premise identifies the actual semantic payload: a boxed value of a type the
phase rewrites — a DEFINED type other than the machine's `runtime.Error`
twin, or a pointer type (`*T` carries `T`'s methods) — whose entry is
`.done`. The value arms of `renderPanicPayload` never print those boxes, so
the text is what renders. -/

/-- The payload boxes the preprint phase rewrites: a defined type other than
the `runtime.Error` twin, or a pointer type. -/
def rewritableBox : GoValue → Prop
  | .interface (.defined idx) _ => idx ≠ runtimeErrorTypeIdx
  | .interface (.pointer _) _ => True
  | _ => False

-- The unused-simp-arg linter misfires on the multi-goal `cases … <;> simp only [rewritableBox] at hv`
-- (the argument is load-bearing on the boxed goals, idle on the `False`-hypothesis ones).
set_option linter.unusedSimpArgs false in
/-- The renderer on a REWRITTEN payload IS the member function on the stored
text, at the pick's collapse bit. -/
theorem renderPanicHead_text (first : PanicEntry)
    (rest : List PanicEntry) (text : GoString) (pick : Nat)
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text) :
    renderPanicHead ctx first rest pick =
      stringPanicHead text first.recovered (collapseBit first rest pick) := by
  obtain ⟨value, recovered, rewrite, repanicked⟩ := first
  simp only at hv hr
  subst hr
  unfold renderPanicHead renderPanicPayload stringPanicHead
  cases value <;> simp only [rewritableBox] at hv
  rename_i dynTy inner
  cases dynTy <;> simp only [rewritableBox] at hv
  case defined idx =>
    have hne : (idx == runtimeErrorTypeIdx) = false := beq_eq_false_iff_ne.mpr hv
    cases inner <;> simp [renderPanicRewrite, recoveredSuffix_eq, hne]
  case pointer t =>
    cases inner <;> simp [renderPanicRewrite, recoveredSuffix_eq]

theorem abortMsg_text (first : PanicEntry)
    (rest : List PanicEntry) (text : GoString) (pick : Nat) (msg : String)
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (hm : stringPanicHead text first.recovered (collapseBit first rest pick) = some msg) :
    abortMsg ctx first rest pick = .ok msg := by
  simp [abortMsg, renderPanicHead_text first rest text pick hv hr, hm]

/-- The refusal, BY NAME: a rewritten payload whose text has no member (its
first line is not valid UTF-8 — D5) refuses with `abortRefusal`. -/
theorem abortMsg_text_refused (first : PanicEntry)
    (rest : List PanicEntry) (text : GoString) (pick : Nat)
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (hm : stringPanicHead text first.recovered (collapseBit first rest pick) = none) :
    abortMsg ctx first rest pick = .error (.unsupported (abortRefusal ctx first)) := by
  simp [abortMsg, renderPanicHead_text first rest text pick hv hr, hm, throw, throwThe,
    MonadExceptOf.throw]

theorem abortMsg_text_ok (first : PanicEntry)
    (rest : List PanicEntry) (text : GoString) (pick : Nat) (msg : String)
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (h : abortMsg ctx first rest pick = .ok msg) :
    stringPanicHead text first.recovered (collapseBit first rest pick) = some msg := by
  unfold abortMsg at h
  rw [renderPanicHead_text first rest text pick hv hr] at h
  cases hm : stringPanicHead text first.recovered (collapseBit first rest pick) with
  | none => simp [hm] at h
  | some m => simp [hm] at h; exact congrArg some h

/-- The sequential abort step on a rewritten payload: the `panic` terminal
carrying the member the STREAM's pick selects. -/
theorem stepFn_text_abort (s : Store) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (text : GoString) (msg : String)
    (hab : c.abort? = some (first, rest))
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (hm : stringPanicHead text first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg) :
    stepFn ctx s c choices = .error (.panic msg) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [stepFn, stepPanicStop, hs, abortMsg_text first rest text _ msg hv hr hm]
  rfl

theorem stepFn_text_abort_refused (s : Store) (c : Config) (choices : Choices)
    (first : PanicEntry) (rest : List PanicEntry) (text : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (hm : stringPanicHead text first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = none) :
    stepFn ctx s c choices = .error (.unsupported (abortRefusal ctx first)) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [stepFn, stepPanicStop, hs, abortMsg_text_refused first rest text _ hv hr hm]
  rfl

theorem runConfig_text_abort (fuel : Nat) (s : Store) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (text : GoString)
    (msg : String)
    (hab : c.abort? = some (first, rest))
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (hm : stringPanicHead text first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = some msg) :
    runConfig ctx (fuel + 1) s c choices = .error (.panic msg) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [runConfig, stepFn_text_abort s (.panicking (first :: rest) .stop)
    choices first rest text msg (Config.abort?_of_settled hs) hv hr hm]
  rfl

theorem runConfig_text_abort_refused (fuel : Nat) (s : Store) (c : Config)
    (choices : Choices) (first : PanicEntry) (rest : List PanicEntry) (text : GoString)
    (hab : c.abort? = some (first, rest))
    (hv : rewritableBox first.value) (hr : first.rewrite = .done text)
    (hm : stringPanicHead text first.recovered
      (collapseBit first rest (abortConsult first rest choices).1) = none) :
    runConfig ctx (fuel + 1) s c choices = .error (.unsupported (abortRefusal ctx first)) := by
  obtain ⟨rfl, hs⟩ := Config.abort?_some_iff.mp hab
  simp only [runConfig, stepFn_text_abort_refused s (.panicking (first :: rest) .stop)
    choices first rest text (Config.abort?_of_settled hs) hv hr hm]
  rfl

end GoLean.GoCore.Machine
