import GoLean.Relational

/-! Facade-only clients of the complete local outcome interface. The symbolic
clients use coverage, realization and exclusion without evaluator case analysis.
Small malformed-state controls separately exercise consultation provenance. -/
namespace Tests.RelationalOutcomes
open GoLean GoLean.GoCore GoLean.GoCore.Relational Local

theorem classify (mode : Mode) (ctx : ProgramCtx) (budget : Nat) (a : State) (ch : Choices) :
    ∃ ls b records o cost suffix,
      Local.Execution mode ctx budget a ls b records o cost ∧
      cost ≤ budget ∧ Run ctx a ls b ∧
      Correspondence.driver mode ctx budget a ch = Correspondence.observe o b suffix := by
  have hc : Correspondence.Coverage mode := by
    cases mode
    · exact Correspondence.main_coverage
    · exact Correspondence.initialization_coverage
  obtain ⟨ls, b, records, o, cost, middle, suffix, hx, _, _, he⟩ := hc ctx budget a ch
  exact ⟨ls, b, records, o, cost, suffix, hx, hx.within_budget, hx.prefix.erase, he⟩

theorem selected_path_realizes (mode : Mode) (ctx : ProgramCtx) (budget : Nat)
    (a b : State) (ls : List StepLabel) (records : List PickRecord) (o : Outcome) (cost : Nat)
    (h : Local.Execution mode ctx budget a ls b records o cost) (suffix : Choices) :
    ∃ ch middle,
      ExecutionStatement.Prefix ctx ls.length a.store a.control ch ls b.store b.control middle ∧
      ExecutionStatement.replays records middle suffix ∧
      Correspondence.driver mode ctx budget a ch = Correspondence.observe o b suffix := by
  cases mode
  · exact Correspondence.main_realization ctx budget a ls b records o cost h suffix
  · exact Correspondence.initialization_realization ctx budget a ls b records o cost h suffix

theorem safe_from_refusal (mode : Mode) (ctx : ProgramCtx) (a : State)
    (avoid : Avoids mode ctx a Outcome.isRefusal) (budget : Nat) (ch : Choices) (r : Refusal) :
    Correspondence.driver mode ctx budget a ch ≠ .error (.refusal r) := by
  cases mode
  · exact Correspondence.main_refusal_exclusion ctx a avoid budget ch r
  · exact Correspondence.initialization_refusal_exclusion ctx a avoid budget ch r

theorem safe_from_fatal (mode : Mode) (ctx : ProgramCtx) (a : State)
    (avoid : Avoids mode ctx a Outcome.isFatal) (budget : Nat) (ch : Choices) (message : String) :
    Correspondence.driver mode ctx budget a ch ≠ .error (.terminal (.fatal message)) := by
  cases mode
  · exact Correspondence.main_fatal_exclusion ctx a avoid budget ch message
  · exact Correspondence.initialization_fatal_exclusion ctx a avoid budget ch message

theorem normal_at_zero (mode : Mode) (ctx : ProgramCtx) (s : Store) :
    Local.Execution mode ctx 0 (resumed Continuation.halt s) [] (resumed Continuation.halt s)
      [] (.boundary .normal) 0 :=
  .finished (.boundary .normal (.inl rfl)) (Nat.le_refl _)

theorem initialization_print_at_zero (ctx : ProgramCtx) (a : State) (bytes : GoString)
    (hp : Machine.printOut? a.control = some bytes) :
    Local.Execution .initialization ctx 0 a [] a [] (.initializationPrint bytes) 0 :=
  .finished (.initializationPrint rfl hp) (Nat.le_refl _)

theorem initialization_print_refuses (ctx : ProgramCtx) (a : State) (bytes : GoString)
    (hp : Machine.printOut? a.control = some bytes) (ch : Choices) :
    Correspondence.driver .initialization ctx 0 a ch = .error initializationStop := by
  obtain ⟨ls, b, records, o, cost, middle, suffix, hx, _, _, he⟩ :=
    Correspondence.initialization_coverage ctx 0 a ch
  cases hx with
  | exhausted _ admit => simp [Admitted, hp] at admit
  | finished hf enough =>
    cases hf with
    | boundary hb _ =>
      have hc : cost = 0 := Nat.eq_zero_of_le_zero enough
      subst cost
      cases hb <;> cases hp
    | operation => omega
    | initializationPrint _ _ => exact he

-- Unsupported expressions admit no invented consultation record, even though
-- a cause-only replay theorem alone would not rule one out.
theorem unsupported_records (ctx : ProgramCtx) (s : Store) (env : LocalEnv)
    (k : Continuation) (why : String) (rs : List PickRecord) (cause : FailureCause)
    (h : OperationFailure ctx (expression (.unsupported why) env k s) rs cause) : rs = [] := by
  cases cause <;> cases h <;> rfl

theorem unsupported_failure (ctx : ProgramCtx) (s : Store) (env : LocalEnv)
    (k : Continuation) (why : String) :
    OperationFailure ctx (expression (.unsupported why) env k s) []
      (.refusal (.unsupported why)) := .failed

theorem empty_panic_chain (ctx : ProgramCtx) (s : Store) :
    OperationFailure ctx ⟨.panicking [] .stop, s⟩ [] (.refusal (.internal "empty panic chain at stop")) :=
  .failed

theorem fatal_is_not_refusal (message : String) :
    ¬ Outcome.isRefusal (.failed (.fatal message)) := by
  simp [Outcome.isRefusal, Outcome.stop?, FailureCause.stop]

theorem refusal_is_not_fatal (reason : Refusal) :
    ¬ Outcome.isFatal (.failed (.refusal reason)) := by
  simp [Outcome.isFatal, Outcome.stop?, FailureCause.stop]

private def guardGraph : UnseqGraph :=
  { cells := [⟨0, .bool⟩]
    occs := [⟨"producer", .eval 0 (.boolLit true), [], none⟩,
      ⟨"consumer", .eval 1 (.var 0), [], none⟩,
      ⟨"ready1", .eval 2 (.boolLit true), [], none⟩,
      ⟨"ready2", .eval 3 (.boolLit true), [], none⟩] }

private def guardStatus : List UnseqStatus := [.skipped, .active, .active, .active]

set_option maxRecDepth 3000 in
theorem skipped_dependency_before_choice (ctx : ProgramCtx) (s : Store) :
    OperationFailure ctx
      ⟨.next (.unseqK guardGraph (.seqn #[]) guardStatus [] [] .pick .stop), s⟩ []
      (.refusal (.stuck "unseq: occurrence 'consumer' value-depends on '0', confined to a skipped region (no valid join) — malformed graph")) :=
  .failed

theorem rand_validation_before_choice :
    (OperationCheck.Correspondence.run
      (FailureChecks.statementOperation ProgramCtx.ofTables {} .randIntn
        [.bool true, .int 4 .int]) [3, 7]).2 = ([3, 7], []) := rfl

theorem rand_commit_after_choice :
    (OperationCheck.Correspondence.run
      (FailureChecks.statementOperation ProgramCtx.ofTables {} .randIntn
        [.addr (.base ⟨99⟩), .int 4 .int]) [3, 7]).2 =
      ([7], [⟨.intn, 4, 3⟩]) := rfl

#print axioms Correspondence.operation_failure_coverage
#print axioms Correspondence.operation_failure_replay
#print axioms Correspondence.operation_failure_selections
#print axioms Correspondence.main_coverage
#print axioms Correspondence.main_realization
#print axioms Correspondence.main_refusal_exclusion
#print axioms Correspondence.main_fatal_exclusion
#print axioms Correspondence.initialization_coverage
#print axioms Correspondence.initialization_realization
#print axioms Correspondence.initialization_refusal_exclusion
#print axioms Correspondence.initialization_fatal_exclusion
#print axioms classify
#print axioms selected_path_realizes
#print axioms safe_from_refusal
#print axioms safe_from_fatal

end Tests.RelationalOutcomes
