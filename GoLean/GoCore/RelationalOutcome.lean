import GoLean.GoCore.Relational

/-!
# Relational terminal boundaries

Completion, sequential deadlock and panic rendering are classified separately.
The panic payload chain and rendering consultation are retained, including a
rendering refusal. A refusal is not a successful value.

This first boundary relation does not classify ordinary operation refusals or
fatal failures. Absence of `Boundary` or of a successor proves neither safety
nor divergence. Executable correspondence is in `RelationalOutcomeSound`.
-/

namespace GoLean.GoCore.Relational

open Machine

/-- A semantic consultation, independent of any tape. Bounds zero and one
have exactly pick zero and produce no record. -/
def Selection (site : ChoiceSite) (bound pick : Nat) (records : List PickRecord) : Prop :=
  pick < max 1 bound ∧ records = PickRecord.ofPick site bound pick

inductive Ending where
  | normal
  | deadlock
  | panic (first : PanicEntry) (rest : List PanicEntry) (text : String)
  | renderingRefusal (first : PanicEntry) (rest : List PanicEntry) (reason : Refusal)

/-- Terminal classification with exact cost and final consultation records.
The final store is the store of the classified point. -/
inductive Boundary (ctx : ProgramCtx) : State → List PickRecord → Ending → Nat → Prop where
  | normal {s} : Boundary ctx ⟨.next .stop, s⟩ [] .normal 0
  | send {s ch v k} : Boundary ctx ⟨.blockedSend ch v k, s⟩ [] .deadlock 0
  | recv {s ch targets elem env k} :
      Boundary ctx ⟨.blockedRecv ch targets elem env k, s⟩ [] .deadlock 0
  | select {s clauses env k} : Boundary ctx ⟨.blockedSelect clauses env k, s⟩ [] .deadlock 0
  | sync {s op loc env k} : Boundary ctx ⟨.blockedSync op loc env k, s⟩ [] .deadlock 0
  | panic {a first rest pick records text} :
      a.control.abort? = some (first, rest) →
      Selection .repanicCollapse (repanicCollapseWidth first rest) pick records →
      abortMsg ctx first rest pick = .ok text →
      Boundary ctx a records (.panic first rest text) 1
  | renderingRefusal {a first rest pick records reason} :
      a.control.abort? = some (first, rest) →
      Selection .repanicCollapse (repanicCollapseWidth first rest) pick records →
      abortMsg ctx first rest pick = .error (.refusal reason) →
      Boundary ctx a records (.renderingRefusal first rest reason) 1

/-- Successful transitions followed by a terminal boundary. The labels and
the terminal records are separate, and cost includes terminal rendering. -/
def Completed (ctx : ProgramCtx) (a : State) (ls : List StepLabel) (b : State)
    (records : List PickRecord) (ending : Ending) (cost : Nat) : Prop :=
  ∃ finishCost, Run ctx a ls b ∧ Boundary ctx b records ending finishCost ∧
    cost = ls.length + finishCost

/-- Budget exhaustion is a particular prefix, not absence of a possible
completion. Normal and blocked endpoints are classified before the budget
test; panic rendering still needs one unit. -/
def Exhausted (ctx : ProgramCtx) (a : State) (ls : List StepLabel) (b : State)
    (fuel : Nat) : Prop :=
  Run ctx a ls b ∧ ls.length = fuel ∧ ¬ ∃ ending, Boundary ctx b [] ending 0

theorem Boundary.normal_iff {ctx : ProgramCtx} {a : State} {rs : List PickRecord} {cost : Nat} :
    Boundary ctx a rs .normal cost ↔ a.control = .next .stop ∧ rs = [] ∧ cost = 0 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rcases a with ⟨c, s⟩
    rintro ⟨rfl, rfl, rfl⟩
    exact .normal

end GoLean.GoCore.Relational
