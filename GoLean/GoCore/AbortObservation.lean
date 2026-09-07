import GoLean.GoCore.Trace

/-! Computed abort metadata from an observational replay of the actual
sequential driver. The replay uses `stepFn` unchanged, mirrors the driver's
terminal/fuel guards, and records only an actual panic error at an abort
configuration. The generic erasure theorem includes malformed inputs. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine

structure AbortHead where
  bytes : GoString
  recovered : Bool
  deriving Repr

def AbortHead.entry (head : AbortHead) : PanicEntry :=
  ⟨.interface .string (.string head.bytes), head.recovered⟩

structure AbortRecord where
  bytes : GoString
  recovered : Bool
  tail : List AbortHead
  deriving Repr

def AbortRecord.chain (record : AbortRecord) : List PanicEntry :=
  (AbortHead.mk record.bytes record.recovered).entry :: record.tail.map AbortHead.entry

def stringPanicEntry? (entry : PanicEntry) : Option AbortHead :=
  match entry.value with
  | .interface .string (.string bytes) => some ⟨bytes, entry.recovered⟩
  | _ => none

def stringPanicEntries? : List PanicEntry → Option (List AbortHead)
  | [] => some []
  | first :: rest => do
    let head ← stringPanicEntry? first
    let tail ← stringPanicEntries? rest
    return head :: tail

def abortRecord? (c : Config) : Option AbortRecord :=
  match c.abort? with
  | some (first, rest) => do
    let head ← stringPanicEntry? first
    let tail ← stringPanicEntries? rest
    return ⟨head.bytes, head.recovered, tail⟩
  | none => none

def runConfigWithAbort : Nat → ExecState → Config → Choices →
    Except Stop (ExecState × Choices) × Option AbortRecord
  | fuel, s, c, ch =>
    match c with
    | .next .stop => (.ok (s, ch), none)
    | .blockedSend .. | .blockedRecv .. | .blockedSelect .. | .blockedSync .. =>
      (.error .deadlock, none)
    | c =>
      match fuel with
      | 0 => (.error .fuelOut, none)
      | fuel + 1 =>
        match stepFn s c ch with
        | .ok (next, t, ch') => runConfigWithAbort fuel t next ch'
        | .error (.panic message) => (.error (.panic message), abortRecord? c)
        | .error e => (.error e, none)

/-- Exact erasure for every input: no typing premise, weakened outcome
classification, changed fuel or reselected choice stream. -/
theorem runConfigWithAbort_erasure (fuel : Nat) (s : ExecState) (c : Config) (ch : Choices) :
    (runConfigWithAbort fuel s c ch).1 = runConfig fuel s c ch := by
  fun_induction runConfigWithAbort fuel s c ch <;>
    simp_all [runConfig, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem stringPanicEntry?_some {entry : PanicEntry} {head : AbortHead}
    (h : stringPanicEntry? entry = some head) : entry = head.entry := by
  unfold stringPanicEntry? at h
  split at h
  · rename_i bytes hv
    cases h
    cases entry
    simp only at hv
    cases hv
    rfl
  · contradiction

theorem stringPanicEntries?_some {entries : List PanicEntry} {heads : List AbortHead}
    (h : stringPanicEntries? entries = some heads) : entries = heads.map AbortHead.entry := by
  induction entries generalizing heads with
  | nil => cases h; rfl
  | cons first rest ih =>
    cases hh : stringPanicEntry? first with
    | none => simp [stringPanicEntries?, hh] at h
    | some head =>
      cases ht : stringPanicEntries? rest with
      | none => simp [stringPanicEntries?, hh, ht] at h
      | some tail =>
        have he : head :: tail = heads := by simpa [stringPanicEntries?, hh, ht] using h
        subst heads
        simp only [List.map_cons, ← stringPanicEntry?_some hh, ← ih ht]

theorem stringPanicEntries?_typed (entries : List PanicEntry)
    (h : ∀ e ∈ entries, ∃ bytes, e.value = .interface .string (.string bytes)) :
    ∃ heads, stringPanicEntries? entries = some heads := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨bytes, value⟩ := h first (by simp)
    obtain ⟨tail, ht⟩ := ih (fun e he => h e (by simp [he]))
    exact ⟨⟨bytes, first.recovered⟩ :: tail, by
      simp [stringPanicEntries?, stringPanicEntry?, value, ht]⟩

theorem abortRecord?_some {c : Config} {head : AbortRecord} (h : abortRecord? c = some head) :
    ∃ first rest, c.abort? = some (first, rest) ∧
      first.value = .interface .string (.string head.bytes) ∧ first.recovered = head.recovered ∧
      first :: rest = head.chain := by
  unfold abortRecord? at h
  split at h
  · rename_i first rest hc
    cases he : stringPanicEntry? first with
    | none => simp [he] at h
    | some entry =>
      cases ht : stringPanicEntries? rest with
      | none => simp [he, ht] at h
      | some tail =>
        have hr : AbortRecord.mk entry.bytes entry.recovered tail = head := by
          simpa [he, ht] using h
        subst head
        have hfirst := stringPanicEntry?_some he
        have hrest := stringPanicEntries?_some ht
        exact ⟨first, rest, hc, by rw [hfirst]; rfl, by rw [hfirst]; rfl,
          by simp [AbortRecord.chain, hfirst, hrest]⟩
  · contradiction

/-- Every computed metadata record comes from an actual panic error, at a
strictly positive-fuel abort frontier reached on the original choice stream.
Even malformed inputs cannot fabricate metadata from a transient panic. -/
theorem runConfigWithAbort_witness {fuel s c ch result head}
    (h : runConfigWithAbort fuel s c ch = (result, some head)) :
    ∃ (n : Nat) (t : ExecState) (terminal : Config) (residual : Choices) (message : String),
      n < fuel ∧ GoLean.Semantics.Trace n s c ch t terminal residual ∧
      abortRecord? terminal = some head ∧
      stepFn t terminal residual = .error (.panic message) ∧ result = .error (.panic message) := by
  fun_induction runConfigWithAbort fuel s c ch with
  | case1 => simp at h
  | case2 => simp at h
  | case3 => simp at h
  | case4 => simp at h
  | case5 => simp at h
  | case6 => simp at h
  | case7 =>
    rename_i fuel s ch c _ _ _ _ _ next t residual step ih
    obtain ⟨n, terminalState, terminal, finalCh, message, hn, trace, hhead, hstep, hresult⟩ := ih h
    exact ⟨n + 1, terminalState, terminal, finalCh, message, Nat.succ_lt_succ hn,
      .step step trace, hhead, hstep, hresult⟩
  | case8 =>
    rename_i message step
    obtain ⟨hr, hm⟩ := Prod.mk.inj h
    exact ⟨0, _, _, _, message, Nat.zero_lt_succ _, .done, hm, step, hr.symm⟩
  | case9 => simp at h

end GoLean.GoCore.RecoveryRuntime
