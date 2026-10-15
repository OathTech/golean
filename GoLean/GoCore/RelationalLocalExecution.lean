import GoLean.GoCore.RelationalOperationFailure

/-! Bounded local sequential outcomes for arbitrary supplied states.
Semantic carriers are independent of tapes and drivers; executable projections
and exact correspondence statements live in `Correspondence`. -/
namespace GoLean.GoCore.Relational.Local
open Machine

inductive Mode where
  | main
  | initialization

def Admitted : Mode → State → Prop
  | .main, _ => True
  | .initialization, a => printOut? a.control = none

def ZeroCost (ctx : ProgramCtx) (a : State) : Prop :=
  ∃ ending, Boundary ctx a [] ending 0

inductive Outcome where
  | boundary (ending : Ending)
  | failed (cause : FailureCause)
  | initializationPrint (bytes : GoString)
  | exhausted

/-- The exact existing diagnostic; projection agreement with the guard is
checked below. No error branch pretends to return a store, tape or label. -/
def initializationStop : Stop := .unsupported
  "print/println during package initialization: the init phase runs on the sequential driver, which has no output event channel (the pool driver folds StepEvent.out) — refused rather than dropping the bytes (stdlib slice 3; row builtins/print/in-init)"

def Outcome.stop? : Outcome → Option Stop
  | .boundary .normal => none
  | .boundary .deadlock => some (.terminal .deadlock)
  | .boundary (.panic _ _ text) => some (.terminal (.panic text))
  | .boundary (.renderingRefusal _ _ reason) => some (.refusal reason)
  | .failed cause => some cause.stop
  | .initializationPrint _ => some initializationStop
  | .exhausted => some .fuelOut

def Outcome.isRefusal (o : Outcome) : Prop := ∃ r, o.stop? = some (.refusal r)
def Outcome.isFatal (o : Outcome) : Prop := ∃ m, o.stop? = some (.terminal (.fatal m))

/-- Local finishing rules. Operation failures cost one step and cannot
bypass normal/deadlock or initialization-print priority. -/
inductive Finish (mode : Mode) (ctx : ProgramCtx) :
    State → List PickRecord → Outcome → Nat → Prop where
  | boundary {a records ending cost} :
      Boundary ctx a records ending cost →
      (cost = 0 ∨ Admitted mode a) → Finish mode ctx a records (.boundary ending) cost
  | operation {a records cause} :
      ¬ ZeroCost ctx a → a.control.abort? = none → Admitted mode a →
      OperationFailure ctx a records cause → Finish mode ctx a records (.failed cause) 1
  | initializationPrint {a bytes} :
      mode = .initialization → printOut? a.control = some bytes →
      Finish mode ctx a [] (.initializationPrint bytes) 0

/-- Successful prefixes retain the actual mode guard at each traversed source. -/
inductive Prefix (mode : Mode) (ctx : ProgramCtx) : State → List StepLabel → State → Prop where
  | refl {a} : Prefix mode ctx a [] a
  | step {a b c l ls} : Admitted mode a → Transition ctx a l b →
      Prefix mode ctx b ls c → Prefix mode ctx a (l :: ls) c

theorem Prefix.erase {mode ctx a b ls} (h : Prefix mode ctx a ls b) : Run ctx a ls b := by
  induction h with
  | refl => exact .refl
  | step _ hs _ ih => exact .cons hs ih

/-- Bounded selected execution. The last field is actual cost, not the input
budget. Exhaustion requires exactly the available number of successful steps. -/
inductive Execution (mode : Mode) (ctx : ProgramCtx) :
    Nat → State → List StepLabel → State → List PickRecord → Outcome → Nat → Prop where
  | finished {budget a records ending cost} : Finish mode ctx a records ending cost →
      cost ≤ budget → Execution mode ctx budget a [] a records ending cost
  | exhausted {a} : ¬ ZeroCost ctx a → Admitted mode a →
      Execution mode ctx 0 a [] a [] .exhausted 0
  | step {budget a b c l ls records ending cost} : Admitted mode a → Transition ctx a l b →
      Execution mode ctx budget b ls c records ending cost →
      Execution mode ctx (budget + 1) a (l :: ls) c records ending (cost + 1)

theorem Execution.prefix {mode ctx budget a b ls rs o cost}
    (h : Execution mode ctx budget a ls b rs o cost) : Prefix mode ctx a ls b := by
  induction h with
  | finished => exact .refl
  | exhausted => exact .refl
  | step ha hs _ ih => exact .step ha hs ih

theorem Execution.within_budget {mode ctx budget a b ls rs o cost}
    (h : Execution mode ctx budget a ls b rs o cost) : cost ≤ budget := by
  induction h with
  | finished _ enough => exact enough
  | exhausted => exact Nat.le_refl _
  | step _ _ _ ih => exact Nat.succ_le_succ ih

/-- Exhaustion uses every unit of the selected budget, with no finishing
consultation. This does not exclude a different path finishing earlier. -/
theorem Execution.exhaustion_length {mode ctx budget a b ls rs cost}
    (h : Execution mode ctx budget a ls b rs .exhausted cost) :
    ls.length = budget ∧ cost = budget ∧ rs = [] := by
  generalize he : Outcome.exhausted = o at h
  induction h with
  | finished hf _ => cases hf <;> cases he
  | exhausted => exact ⟨rfl, rfl, rfl⟩
  | step _ _ _ ih =>
    obtain ⟨hl, hc, hr⟩ := ih he
    exact ⟨by simp [hl], by omega, hr⟩

/-- Each result is a finish after its prefix, with its exact finishing cost,
or exhaustion. It cannot manufacture a final failed-step label. -/
theorem Execution.finish_or_exhausted {mode ctx budget a b ls rs o cost}
    (h : Execution mode ctx budget a ls b rs o cost) :
    (∃ finishCost, Finish mode ctx b rs o finishCost ∧
      cost = ls.length + finishCost) ∨ o = .exhausted := by
  induction h with
  | finished hf _ => exact .inl ⟨_, hf, by simp⟩
  | exhausted => exact .inr rfl
  | step _ _ _ ih =>
    rcases ih with ⟨fc, hf, hc⟩ | ho
    · exact .inl ⟨fc, hf, by simp only [List.length_cons]; omega⟩
    · exact .inr ho

/-- Exclusion quantifies over all reachable alternatives, including rendering
and initialization guards. Fatal exclusion is deliberately a separate predicate. -/
def Avoids (mode : Mode) (ctx : ProgramCtx) (a : State)
    (bad : Outcome → Prop) : Prop :=
  ∀ ls b, Prefix mode ctx a ls b → ∀ records o cost,
    Finish mode ctx b records o cost → ¬ bad o

/-! Executable projections and correspondence statements. Their closed proofs
are exported by `RelationalLocalExecutionSound`. -/
namespace Correspondence
open ExecutionStatement

def driver (mode : Mode) (ctx : ProgramCtx) (budget : Nat) (a : State) (ch : Choices) :=
  match mode with
  | .main => execStmtLoop ctx budget a.store a.control ch
  | .initialization => runInitConfig ctx budget a.store a.control ch

def observe (o : Outcome) (b : State) (tail : Choices) : Except Stop (Store × Choices) :=
  match o.stop? with
  | none => .ok (b.store, tail)
  | some e => .error e

/-- Complete ordinary failure coverage at every selected tape. The suffix is
only a witness to the consulted picks; stepFn returns no suffix on failure. -/
def OperationCoverage : Prop :=
  ∀ ctx a ch cause, ¬ Local.ZeroCost ctx a → a.control.abort? = none →
    stepFn ctx a.store a.control ch = .error cause.stop →
    ∃ records suffix, OperationFailure ctx a records cause ∧ replays records ch suffix

/-- Every semantic failed-operation alternative works on each tape replaying
its consultations. This may not be replaced by existence of one success. -/
def OperationReplay : Prop :=
  ∀ ctx a records cause, OperationFailure ctx a records cause → ∀ ch suffix,
    replays records ch suffix → stepFn ctx a.store a.control ch = .error cause.stop

/-- Semantic consultation witnesses must be realizable with any suffix. -/
def OperationSelections : Prop :=
  ∀ ctx a records cause, OperationFailure ctx a records cause → ∀ suffix,
    ∃ ch, replays records ch suffix

/-- Exact actual-result coverage, with no well-formedness or safety premise.
Successful labels and finishing consultations are separate; the finishing
suffix is semantic bookkeeping and is erased by every error projection. -/
def Coverage (mode : Mode) : Prop :=
  ∀ ctx budget a ch,
    ∃ ls b records o cost middle suffix,
      Execution mode ctx budget a ls b records o cost ∧
      ExecutionStatement.Prefix ctx ls.length a.store a.control ch ls b.store b.control middle ∧
      replays records middle suffix ∧ driver mode ctx budget a ch = observe o b suffix

/-- Every selected admitted relational execution is realizable at its stated
budget with arbitrary finishing suffix; no uniqueness across choices is asserted. -/
def Realization (mode : Mode) : Prop :=
  ∀ ctx budget a ls b records o cost,
    Execution mode ctx budget a ls b records o cost → ∀ suffix,
    ∃ ch middle,
      ExecutionStatement.Prefix ctx ls.length a.store a.control ch ls b.store b.control middle ∧
      replays records middle suffix ∧ driver mode ctx budget a ch = observe o b suffix

def RefusalExclusion (mode : Mode) : Prop :=
  ∀ ctx a, Avoids mode ctx a Outcome.isRefusal → ∀ budget ch reason,
    driver mode ctx budget a ch ≠ .error (.refusal reason)

def FatalExclusion (mode : Mode) : Prop :=
  ∀ ctx a, Avoids mode ctx a Outcome.isFatal → ∀ budget ch message,
    driver mode ctx budget a ch ≠ .error (.terminal (.fatal message))

/-- Once coverage is proved, relational exclusion transfers to the actual
selected driver result. This lemma does not assume coverage as an instance. -/
theorem excludes_stop_of_coverage (mode : Mode)
    (coverage : Coverage mode) (ctx : ProgramCtx) (a : State)
    (bad : Outcome → Prop) (avoid : Avoids mode ctx a bad)
    (e : Stop) (classify : ∀ o, o.stop? = some e → bad o)
    (noExhaustion : ¬ bad .exhausted) (budget : Nat) (ch : Choices) :
    driver mode ctx budget a ch ≠ .error e := by
  intro hr
  obtain ⟨ls, b, records, o, cost, middle, suffix, h, _, _, he⟩ := coverage ctx budget a ch
  have ho : o.stop? = some e := by
    rw [he] at hr
    cases hs : o.stop? with
    | none => simp [observe, hs] at hr
    | some other =>
      simp only [observe, hs, Except.error.injEq] at hr
      exact congrArg some hr
  rcases h.finish_or_exhausted with ⟨fc, hf, _⟩ | exhausted
  · exact avoid ls b h.prefix records o fc hf (classify o ho)
  · subst o
    exact noExhaustion (classify _ ho)

theorem refusal_exclusion_of_coverage (mode : Mode)
    (coverage : Coverage mode) : RefusalExclusion mode := by
  intro ctx a avoid budget ch reason
  exact excludes_stop_of_coverage mode coverage ctx a Outcome.isRefusal avoid
    (.refusal reason) (fun _ h => ⟨reason, h⟩)
    (by simp [Outcome.isRefusal, Outcome.stop?]) budget ch

theorem fatal_exclusion_of_coverage (mode : Mode)
    (coverage : Coverage mode) : FatalExclusion mode := by
  intro ctx a avoid budget ch message
  exact excludes_stop_of_coverage mode coverage ctx a Outcome.isFatal avoid
    (.terminal (.fatal message)) (fun _ h => ⟨message, h⟩)
    (by simp [Outcome.isFatal, Outcome.stop?]) budget ch

end Correspondence

end GoLean.GoCore.Relational.Local
