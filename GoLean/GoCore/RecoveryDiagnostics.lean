import GoLean.GoCore.RecoveryGraph

/-! Scope-independent diagnostics, separate from the admission judgment.
These total surface/placement checks distinguish excluded constructor/type
families from binding, expression-sort and call-vector failures. Their
implication from `Statement` ensures they cannot narrow admitted programs. -/
namespace GoLean.GoCore.RecoveryTyping

def expressionInProfile : Expr → Bool
  | .var _ | .boolLit _ | .stringLit _ | .ref _ | .recoverCall => true
  | .nil ty => checkNilType ty
  | .not e => expressionInProfile e
  | .and e₁ e₂ | .or e₁ e₂ => expressionInProfile e₁ && expressionInProfile e₂
  | .deref e .bool => expressionInProfile e
  | .toInterface target .string e => checkType target .payload && expressionInProfile e
  | .eqCmp ty e₁ e₂ | .neqCmp ty e₁ e₂ =>
      (checkType ty .boolean ||
        (checkType ty .payload && (checkNilExpr e₁ || checkNilExpr e₂))) &&
      expressionInProfile e₁ && expressionInProfile e₂
  | _ => false

theorem ExprTyped.in_profile {Γ e sort} (h : ExprTyped Γ e sort) :
    expressionInProfile e = true := by
  induction h <;> simp_all [expressionInProfile, checkType_iff, checkNilType_iff,
    checkNilExpr_iff]

def targetInProfile : Assignee → Bool
  | .var _ => true
  | .addr e => expressionInProfile e
  | _ => false

theorem TargetTyped.in_profile {Γ a sort} (h : TargetTyped Γ a sort) :
    targetInProfile a = true := by
  cases h with
  | var => rfl
  | addr he => exact he.in_profile

def expressionsInProfile (es : List Expr) : Bool := es.all expressionInProfile
def targetsInProfile (as : List Assignee) : Bool := as.all targetInProfile
def calleeInProfile : Expr → Bool
  | .funcVal _ captures => expressionsInProfile captures.toList
  | _ => false

theorem Arguments.in_profile {Γ es ps} (h : Arguments Γ es ps) :
    expressionsInProfile es = true := by
  induction h with
  | nil => rfl
  | cons he _ ih =>
      cases he with
      | typed _ ht =>
          change (expressionInProfile _ && expressionsInProfile _) = true
          simp [ht.in_profile, ih]

theorem Targets.in_profile {Γ as ps} (h : Targets Γ as ps) :
    targetsInProfile as = true := by
  induction h with
  | nil => rfl
  | cons ha _ ih =>
      cases ha with
      | typed _ ht =>
          change (targetInProfile _ && targetsInProfile _) = true
          simp [ht.in_profile, ih]

theorem Captures.in_profile {Γ es} (h : Captures Γ es) :
    expressionsInProfile es = true := by
  induction h with
  | nil => rfl
  | cons he _ ih =>
      change (expressionInProfile _ && expressionsInProfile _) = true
      simp [he.in_profile, ih]

theorem DirectCall.in_profile {fs Γ targets fid args} (h : DirectCall fs Γ targets fid args) :
    targetsInProfile targets.toList = true ∧ expressionsInProfile args.toList = true := by
  obtain ⟨_, _, ha, ht⟩ := h
  exact ⟨ht.in_profile, ha.in_profile⟩

theorem ClosureCall.in_profile {fs Γ targets args callee}
    (h : ClosureCall fs Γ targets args callee) :
    targetsInProfile targets.toList = true ∧ calleeInProfile callee = true ∧
      expressionsInProfile args.toList = true := by
  cases h with
  | known _ hc ha ht =>
    have he := ha.in_profile
    simp only [expressionsInProfile, List.all_append, Bool.and_eq_true] at he
    exact ⟨ht.in_profile, hc.in_profile, he.2⟩

theorem DeferredCall.in_profile {fs Γ args callee} (h : DeferredCall fs Γ args callee) :
    calleeInProfile callee = true ∧ expressionsInProfile args.toList = true := by
  cases h with
  | known _ hc ha =>
    have he := ha.in_profile
    simp only [expressionsInProfile, List.all_append, Bool.and_eq_true] at he
    exact ⟨hc.in_profile, he.2⟩

def panicInProfile : Expr → Bool
  | .toInterface target .string operand =>
      checkType target .payload && expressionInProfile operand
  | _ => false

theorem PanicArgument.in_profile {Γ e} (h : PanicArgument Γ e) :
    panicInProfile e = true := by
  cases h with
  | stringBox ht he => simp [panicInProfile, checkType_complete ht, he.in_profile]

mutual
def statementInProfile : Stmt → Bool
  | .seqn ss => statementsInProfile ss.toList
  | .block ps ss => decide (StorageParams ps) && statementsInProfile ss.toList
  | .initialization p => decide (StorageType p.typ)
  | .assign a e => targetInProfile a && expressionInProfile e
  | .ifThenElse e t f => expressionInProfile e && statementInProfile t &&
      statementInProfile f && decide (declarationCount t = 0) && decide (declarationCount f = 0)
  | .call targets _ args => targetsInProfile targets.toList && expressionsInProfile args.toList
  | .callValue targets callee args => targetsInProfile targets.toList &&
      calleeInProfile callee && expressionsInProfile args.toList
  | .deferCall callee args => calleeInProfile callee && expressionsInProfile args.toList
  | .panicStmt e => panicInProfile e
  | .returnStmt => true
  | _ => false
def statementsInProfile : List Stmt → Bool
  | [] => true
  | s :: ss => statementInProfile s && statementsInProfile ss
end

theorem Statement.in_profile {fs b Γ s} (h : Statement fs b Γ s) :
    statementInProfile s = true := by
  induction h using Statement.rec
    (motive_2 := fun _ ss _ => statementsInProfile ss = true) with
  | seqn _ ih => exact ih
  | block hp _ _ ih => simp [statementInProfile, hp, ih]
  | initialization ht _ => exact decide_eq_true ht
  | assign ha =>
      cases ha with
      | typed ht he => simp [statementInProfile, ht.in_profile, he.in_profile]
  | branch he _ _ ht hf iht ihf => simp [statementInProfile, he.in_profile, iht, ihf, ht, hf]
  | call hc => simpa [statementInProfile, Bool.and_eq_true] using hc.in_profile
  | closureCall hc => simpa [statementInProfile, Bool.and_eq_true, and_assoc] using hc.in_profile
  | deferCall hc => simpa [statementInProfile, Bool.and_eq_true] using hc.in_profile
  | panic hp => exact hp.in_profile
  | ret => rfl
  | nil => rfl
  | cons _ _ ih ihs => simp [statementsInProfile, ih, ihs]

mutual
def statementPlacement (inSequence : Bool) : Stmt → Bool
  | .initialization _ => inSequence
  | .seqn ss | .block _ ss => statementsPlacement ss.toList
  | .ifThenElse _ t f => statementPlacement false t && statementPlacement false f
  | _ => true
def statementsPlacement : List Stmt → Bool
  | [] => true
  | s :: ss => statementPlacement true s && statementsPlacement ss
end

theorem Statement.placement {fs b Γ s} (h : Statement fs b Γ s) :
    statementPlacement b s = true := by
  induction h using Statement.rec
    (motive_2 := fun _ ss _ => statementsPlacement ss = true) <;>
    simp_all [statementPlacement, statementsPlacement]

end GoLean.GoCore.RecoveryTyping
