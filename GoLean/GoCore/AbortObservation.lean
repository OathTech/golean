import GoLean.GoCore.Trace

/-! Computed abort metadata from an observational replay of the actual
sequential driver. The replay uses `stepFn` unchanged, mirrors the driver's
terminal/fuel guards, and records only an actual panic error at an abort
configuration. The generic erasure theorem includes malformed inputs. -/
namespace GoLean.GoCore.RecoveryRuntime

-- B7 (2026-09-17): the program context is the first explicit parameter of
-- every definition below that reads it; theorems take it implicitly
-- (`variable {ctx}` toggles).
variable (ctx : ProgramCtx)
open Machine

structure AbortHead where
  bytes : GoString
  recovered : Bool
  deriving Repr

def AbortHead.entry (head : AbortHead) : PanicEntry :=
  { value := .interface .string (.string head.bytes), recovered := head.recovered }

structure AbortRecord where
  bytes : GoString
  recovered : Bool
  tail : List AbortHead
  deriving Repr

def AbortRecord.chain (record : AbortRecord) : List PanicEntry :=
  (AbortHead.mk record.bytes record.recovered).entry :: record.tail.map AbortHead.entry

/-- The record of a STRING chain entry: its bytes and `recovered` flag. Unit 6b: only an
UN-PHASED entry (`rewrite = .none`, `repanicked = false` — every raised string entry; the
preprint phase never marks a string, which is never pending) has a record, so the record
reconstructs the entry exactly (`stringPanicEntry?_some`). -/
def stringPanicEntry? (entry : PanicEntry) : Option AbortHead :=
  match entry.value, entry.rewrite, entry.repanicked with
  | .interface .string (.string bytes), .none, false => some ⟨bytes, entry.recovered⟩
  | _, _, _ => none

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

def runConfigWithAbort : Nat → Store → Config → Choices →
    Except Stop (Store × Choices) × Option AbortRecord
  | fuel, s, c, ch =>
    match c with
    | .next .stop => (.ok (s, ch), none)
    | .blockedSend .. | .blockedRecv .. | .blockedSelect .. | .blockedSync .. =>
      (.error .deadlock, none)
    | c =>
      match fuel with
      | 0 => (.error .fuelOut, none)
      | fuel + 1 =>
        match stepFn ctx s c ch with
        | .ok (next, t, ch', _) => runConfigWithAbort fuel t next ch'
        | .error (.panic message) => (.error (.panic message), abortRecord? c)
        | .error e => (.error e, none)

variable {ctx}
/-- Exact erasure for every input: no typing premise, weakened outcome
classification, changed fuel or reselected choice stream. -/
theorem runConfigWithAbort_erasure (fuel : Nat) (s : Store) (c : Config) (ch : Choices) :
    (runConfigWithAbort ctx fuel s c ch).1 = runConfig ctx fuel s c ch := by
  fun_induction runConfigWithAbort ctx fuel s c ch <;>
    simp_all [runConfig, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem stringPanicEntry?_some {entry : PanicEntry} {head : AbortHead}
    (h : stringPanicEntry? entry = some head) : entry = head.entry := by
  unfold stringPanicEntry? at h
  split at h
  · rename_i bytes hv hw hp
    cases h
    cases entry
    simp only at hv hw hp
    cases hv; cases hw; cases hp
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

/-- A chain of UN-PHASED string entries has a record (unit 6b: the rewrite and
collapse records are part of the premise — every raised string entry carries
`.none` / `false`). -/
theorem stringPanicEntries?_typed (entries : List PanicEntry)
    (h : ∀ e ∈ entries, (∃ bytes, e.value = .interface .string (.string bytes))
      ∧ e.rewrite = .none ∧ e.repanicked = false) :
    ∃ heads, stringPanicEntries? entries = some heads := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨⟨bytes, value⟩, hw, hp⟩ := h first (by simp)
    obtain ⟨tail, ht⟩ := ih (fun e he => h e (by simp [he]))
    exact ⟨⟨bytes, first.recovered⟩ :: tail, by
      simp [stringPanicEntries?, stringPanicEntry?, value, hw, hp, ht]⟩

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
    (h : runConfigWithAbort ctx fuel s c ch = (result, some head)) :
    ∃ (n : Nat) (t : Store) (terminal : Config) (residual : Choices) (message : String),
      n < fuel ∧ GoLean.Semantics.Trace ctx n s c ch t terminal residual ∧
      abortRecord? terminal = some head ∧
      stepFn ctx t terminal residual = .error (.panic message) ∧ result = .error (.panic message) := by
  fun_induction runConfigWithAbort ctx fuel s c ch with
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
