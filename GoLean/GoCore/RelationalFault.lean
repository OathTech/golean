import GoLean.GoCore.RelationalControl

/-!
# Refusal contracts for the first construct views

These rules retain the actual cause at unsupported statements, declaration
entry, local reads/addresses and Boolean branch selection. They are complete
for those failure sites, not a complete refusal relation for the language.
In particular, absence of `LocalFault` is not a safety predicate.
-/

namespace GoLean.GoCore.Relational

open Machine

inductive LocalFault (ctx : ProgramCtx) : State → Stop → Prop where
  | unsupported {reason env k s} :
      LocalFault ctx (statement (.unsupported reason) env k s) (.unsupported reason)
  | declarations {decls body env k s e} :
      allocDecls ctx env.pushScope s decls.toList = .error e →
      LocalFault ctx (statement (.block decls body) env k s) e
  | unboundValue {id env k s} : LocalEnv.lookup env id = none →
      LocalFault ctx (expression (.var id) env k s) (.stuck s!"unbound GoCore variable address: {id}")
  | unboundAddress {id env k s} : LocalEnv.lookup env id = none →
      LocalFault ctx (expression (.ref id) env k s) (.stuck s!"unbound GoCore variable address: {id}")
  | binding {id env k s loc e} : LocalEnv.lookup env id = some loc →
      loadRoot ctx s loc = .error e → LocalFault ctx (expression (.var id) env k s) e
  | condition {v yes no env k s e} : valueAsBool v = .error e →
      LocalFault ctx (returned v (branch yes no env k) s) e

/-- These faults are tape-independent. Other failure sites may have choice
alternatives and must not inherit this statement by analogy. -/
theorem LocalFault.on_any_tape {ctx : ProgramCtx} {a : State} {e : Stop}
    (h : LocalFault ctx a e) (ch : Choices) : stepFn ctx a.store a.control ch = .error e := by
  cases h with
  | unsupported => rfl
  | declarations he => simp [statement, stepFn, he, Bind.bind, Except.bind]
  | unboundValue he => simp [expression, stepFn, he, throw, throwThe, MonadExceptOf.throw]
  | unboundAddress he => simp [expression, stepFn, he, throw, throwThe, MonadExceptOf.throw]
  | binding hl he => simp [expression, stepFn, hl, Mem.loadBindingFor, he, Bind.bind, Except.bind]
  | condition he => simp [returned, branch, stepFn, he, Bind.bind, Except.bind]

theorem LocalFault.no_successor {ctx : ProgramCtx} {a b : State} {l : StepLabel} {e : Stop}
    (h : LocalFault ctx a e) : ¬ Transition ctx a l b := by
  intro hs
  obtain ⟨ch, tail, he⟩ := step_complete hs
  rw [h.on_any_tape ch] at he
  cases he

/-- A pure contract excludes every stopping alternative on every tape. -/
theorem Pure.excludes_stop {ctx : ProgramCtx} {a b : State} (h : Pure ctx a b)
    (ch : Choices) (e : Stop) : stepFn ctx a.store a.control ch ≠ .error e := by
  rw [h.1.on_any_tape rfl ch]
  intro impossible
  cases impossible

/-- A useful sufficient progress domain: every reachable point is normal
completion or has a pick-free transition. The pick-free condition is
essential; existence of an arbitrary successor does not exclude refusals.
This is an incremental deterministic-fragment capability, not the general
refusal-sensitive safety contract for choiceful programs. -/
def PickFreeProgress (ctx : ProgramCtx) (a : State) : Prop :=
  ∀ ls b, Run ctx a ls b → b.control = .next .stop ∨
    ∃ l c, Transition ctx b l c ∧ l.picks = []

theorem PickFreeProgress.after {ctx : ProgramCtx} {a b : State} {l : StepLabel}
    (h : PickFreeProgress ctx a) (hs : Transition ctx a l b) : PickFreeProgress ctx b :=
  fun ls c hr => h (l :: ls) c (.cons hs hr)

/-- Relational progress in this domain rules out all executable stopping
errors on every tape, without an added machine-well-formedness premise. -/
theorem PickFreeProgress.run {ctx : ProgramCtx} {a : State} (h : PickFreeProgress ctx a)
    (fuel : Nat) (ch : Choices) :
    (∃ s tail, execStmtLoop ctx fuel a.store a.control ch = .ok (s, tail)) ∨
      execStmtLoop ctx fuel a.store a.control ch = .error .fuelOut := by
  induction fuel generalizing a with
  | zero =>
    rcases h [] a .refl with ht | ⟨l, b, hs, hp⟩
    · left
      exact ⟨a.store, ch, by rw [ht, execStmtLoop_unfold]⟩
    · right
      rw [ExecutionStatement.execStmtLoop_nonZero
        (ExecutionStatement.stepFn_zeroCost_not_ok (hs.on_any_tape hp ch))]
  | succ fuel ih =>
    rcases h [] a .refl with ht | ⟨l, b, hs, hp⟩
    · left
      exact ⟨a.store, ch, by rw [ht, execStmtLoop_unfold]⟩
    · have he := hs.on_any_tape hp ch
      rw [ExecutionStatement.execStmtLoop_nonZero (ExecutionStatement.stepFn_zeroCost_not_ok he), he]
      exact ih (h.after hs)

end GoLean.GoCore.Relational
