import GoLean.GoCore.AbortObservation
import GoLean.GoCore.RecoverySuccessfulRuns

/-! Typed provenance and completeness for the generic computed abort observer. -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine

theorem Control.abort_chain {world fs c first rest} (control : Control world fs c)
    (query : c.abort? = some (first, rest)) : ChainTyped (first :: rest) := by
  cases control <;> try (simp [Config.abort?] at query)
  case panicking chain k typed hk =>
    cases k <;> try (simp at query)
    cases chain with
    | nil => exact False.elim (typed.1 rfl)
    | cons head tail =>
      have he : head = first ∧ tail = rest := by simpa [Config.abort?] using query
      obtain ⟨rfl, rfl⟩ := he
      exact typed

theorem Inv.trace_choices {p ps roots s c ch n t terminal residual}
    (inv : Inv p ps roots s c)
    (trace : GoLean.Semantics.Trace n s c ch t terminal residual) : residual = ch := by
  induction trace with
  | done => rfl
  | step step trace ih =>
    obtain ⟨_, heap, control, _⟩ := inv.typed
    obtain ⟨_, _, _, hch⟩ := control_stepFn inv.program inv.sameContext heap control step
    exact (ih (inv.step (stepFn_sound step))).trans hch

/-- In the admitted runtime domain the computed head is backed by the
entire typed panic chain of this reached state, with the original stream
retained in the trace and actual abort query. -/
theorem Inv.observed_abort {p ps roots fuel s c ch result head}
    (inv : Inv p ps roots s c)
    (h : runConfigWithAbort fuel s c ch = (result, some head)) :
    ∃ (n : Nat) (t : ExecState) (terminal : Config) (residual : Choices)
      (message : String) (first : PanicEntry) (rest : List PanicEntry),
      n < fuel ∧ GoLean.Semantics.Trace n s c ch t terminal residual ∧ residual = ch ∧
      terminal.abort? = some (first, rest) ∧ ChainTyped (first :: rest) ∧
      first.value = .interface .string (.string head.bytes) ∧ first.recovered = head.recovered ∧
      first :: rest = head.chain ∧
      stepFn t terminal residual = .error (.panic message) ∧ result = .error (.panic message) := by
  obtain ⟨n, t, terminal, residual, message, hn, trace, hhead, step, result⟩ :=
    runConfigWithAbort_witness h
  obtain ⟨first, rest, query, value, recovered, chain⟩ := abortRecord?_some hhead
  obtain ⟨_, _, control, _⟩ := (inv.steps trace.erase).typed
  exact ⟨n, t, terminal, residual, message, first, rest, hn, trace, inv.trace_choices trace, query,
    control.abort_chain query, value, recovered, chain, step, result⟩

theorem Inv.panic_error_head {p ps roots s c ch message}
    (inv : Inv p ps roots s c) (step : stepFn s c ch = .error (.panic message)) :
    ∃ head, abortRecord? c = some head := by
  obtain ⟨world, heap, control, _⟩ := inv.typed
  rcases control_progress inv.program inv.sameContext heap control with rfl | abort | advance
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at step
  · obtain ⟨first, rest, rfl⟩ := abort
    have typed := control.abort_chain (show Config.abort? (.panicking (first :: rest) .stop) =
      some (first, rest) from rfl)
    obtain ⟨bytes, value⟩ := typed.2 first (by simp)
    obtain ⟨tail, htail⟩ := stringPanicEntries?_typed rest (fun e he => typed.2 e (by simp [he]))
    exact ⟨⟨bytes, first.recovered, tail⟩, by
      simp [abortRecord?, Config.abort?, stringPanicEntry?, value, htail]⟩
  · obtain ⟨_, _, _, run, _⟩ := advance ch
    rw [run] at step
    contradiction

/-- Every actual panic result in the typed domain receives metadata; the
caller supplies admission/setup through `Inv`, not a proposed abort head. -/
theorem Inv.observation_complete {p ps roots fuel s c ch message}
    (inv : Inv p ps roots s c) (run : runConfig fuel s c ch = .error (.panic message)) :
    ∃ head, runConfigWithAbort fuel s c ch = (.error (.panic message), some head) := by
  have erase := runConfigWithAbort_erasure fuel s c ch
  rw [run] at erase
  clear run
  revert inv
  fun_induction runConfigWithAbort fuel s c ch with
  | case1 => simp at erase
  | case2 => simp at erase
  | case3 => simp at erase
  | case4 => simp at erase
  | case5 => simp at erase
  | case6 => simp at erase
  | case7 =>
    rename_i step ih
    intro inv
    exact ih erase (inv.step (stepFn_sound step))
  | case8 =>
    rename_i message' step
    intro inv
    have he : message' = message := by simpa using erase
    subst message'
    obtain ⟨head, hm⟩ := inv.panic_error_head step
    exact ⟨head, by simp [hm]⟩
  | case9 =>
    simp_all

end GoLean.GoCore.RecoveryRuntime
