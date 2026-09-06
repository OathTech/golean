import GoLean.GoCore.RecoveryCalls

namespace GoLean.GoCore.RecoveryTyping

/-- Pointer-to-Boolean has a nil zero value, so it is not a zero-initialized
storage type in this live-root profile. It remains a checked parameter type. -/
def StorageType (ty : Ty) : Prop := TypeClass ty .boolean ∨ TypeClass ty .payload
def ParameterType (ty : Ty) : Prop := StorageType ty ∨ TypeClass ty .root
instance (ty : Ty) : Decidable (StorageType ty) := inferInstanceAs (Decidable (_ ∨ _))
instance (ty : Ty) : Decidable (ParameterType ty) := inferInstanceAs (Decidable (_ ∨ _))

def StorageParams (ps : Array Param) : Prop := ∀ p ∈ ps.toList, StorageType p.typ
def ParameterTypes (ps : Array Param) : Prop := ∀ p ∈ ps.toList, ParameterType p.typ
def DistinctParams (ps : Array Param) : Prop := (ps.toList.map Param.id).Nodup
instance (ps : Array Param) : Decidable (StorageParams ps) :=
  inferInstanceAs (Decidable (∀ p ∈ ps.toList, StorageType p.typ))
instance (ps : Array Param) : Decidable (ParameterTypes ps) :=
  inferInstanceAs (Decidable (∀ p ∈ ps.toList, ParameterType p.typ))
instance (ps : Array Param) : Decidable (DistinctParams ps) :=
  inferInstanceAs (Decidable (ps.toList.map Param.id).Nodup)

inductive Assignment (Γ : Context) : Assignee → Expr → Prop
  | typed {a e s} : TargetTyped Γ a s → ExprTyped Γ e s → Assignment Γ a e

def checkAssignment (Γ : Context) (a : Assignee) (e : Expr) : Bool :=
  (checkTarget Γ a .boolean && checkExpr Γ e .boolean) ||
  (checkTarget Γ a .root && checkExpr Γ e .root) ||
  (checkTarget Γ a .payload && checkExpr Γ e .payload) ||
  (checkTarget Γ a .string && checkExpr Γ e .string)

theorem checkAssignment_iff (Γ : Context) (a : Assignee) (e : Expr) :
    checkAssignment Γ a e = true ↔ Assignment Γ a e := by
  constructor
  · simp only [checkAssignment, Bool.or_eq_true, Bool.and_eq_true]
    rintro (((h | h) | h) | h)
    all_goals exact .typed ((checkTarget_iff _ _ _).mp h.1) ((checkExpr_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | @typed s ha he =>
        cases s <;> simp [checkAssignment, (checkTarget_iff _ _ _).mpr ha, checkExpr_complete he]

inductive PanicArgument (Γ : Context) : Expr → Prop
  | stringBox {target e} : TypeClass target .payload → ExprTyped Γ e .string →
      PanicArgument Γ (.toInterface target .string e)

def checkPanicArgument (Γ : Context) : Expr → Bool
  | .toInterface target .string e => checkType target .payload && checkExpr Γ e .string
  | _ => false

theorem checkPanicArgument_iff (Γ : Context) (e : Expr) :
    checkPanicArgument Γ e = true ↔ PanicArgument Γ e := by
  constructor
  · intro h
    cases e <;> try simp only [checkPanicArgument, Bool.false_eq_true] at h
    case toInterface target dynamic operand =>
      cases dynamic <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at h
      exact .stringBox ((checkType_iff _ _).mp h.1) ((checkExpr_iff _ _ _).mp h.2)
  · intro h; cases h <;> simp [checkPanicArgument, checkType_iff, checkExpr_iff, *]

mutual
def afterStmt (Γ : Context) : Stmt → Context
  | .initialization p => declare Γ p
  | .seqn ss => afterStmts Γ ss.toList
  | _ => Γ
def afterStmts (Γ : Context) : List Stmt → Context
  | [] => Γ
  | s :: ss => afterStmts (afterStmt Γ s) ss
end

/- Count only declarations exported into the current scope. Blocks own
their declarations; sequence lists export theirs. No type equality or name
mangling convention is used to determine the effect. -/
mutual
def declarationCount : Stmt → Nat
  | .initialization _ => 1
  | .seqn ss => declarationCounts ss.toList
  | _ => 0
def declarationCounts : List Stmt → Nat
  | [] => 0
  | s :: ss => declarationCount s + declarationCounts ss
end

mutual
theorem afterStmt_neutral (Γ : Context) (s : Stmt) (h : declarationCount s = 0) :
    afterStmt Γ s = Γ := by
  cases s <;> try rfl
  case initialization => contradiction
  case seqn ss => exact afterStmts_neutral Γ ss.toList h
termination_by structural s
theorem afterStmts_neutral (Γ : Context) (ss : List Stmt) (h : declarationCounts ss = 0) :
    afterStmts Γ ss = Γ := by
  cases ss with
  | nil => rfl
  | cons s ss =>
      have hs : declarationCount s = 0 := Nat.eq_zero_of_add_eq_zero_right h
      have ht : declarationCounts ss = 0 := Nat.eq_zero_of_add_eq_zero_left h
      simp only [afterStmts, afterStmt_neutral Γ s hs]
      exact afterStmts_neutral Γ ss ht
termination_by structural ss
end

mutual
inductive Statement (fs : Array Func) : Bool → Context → Stmt → Prop
  | seqn {inSequence Γ ss} : Statements fs Γ ss.toList → Statement fs inSequence Γ (.seqn ss)
  | block {inSequence Γ ps ss} : StorageParams ps → DistinctParams ps →
      Statements fs (push Γ ps) ss.toList → Statement fs inSequence Γ (.block ps ss)
  | initialization {Γ p} : StorageType p.typ → Fresh Γ p.id →
      Statement fs true Γ (.initialization p)
  | assign {inSequence Γ a e} : Assignment Γ a e → Statement fs inSequence Γ (.assign a e)
  | branch {inSequence Γ e t f} : ExprTyped Γ e .boolean →
      Statement fs false Γ t → Statement fs false Γ f →
      declarationCount t = 0 → declarationCount f = 0 →
      Statement fs inSequence Γ (.ifThenElse e t f)
  | call {inSequence Γ targets fid args} : DirectCall fs Γ targets fid args →
      Statement fs inSequence Γ (.call targets fid args)
  | closureCall {inSequence Γ targets callee args} : ClosureCall fs Γ targets args callee →
      Statement fs inSequence Γ (.callValue targets callee args)
  | deferCall {inSequence Γ callee args} : DeferredCall fs Γ args callee →
      Statement fs inSequence Γ (.deferCall callee args)
  | panic {inSequence Γ e} : PanicArgument Γ e → Statement fs inSequence Γ (.panicStmt e)
  | ret {inSequence Γ} : Statement fs inSequence Γ .returnStmt
inductive Statements (fs : Array Func) : Context → List Stmt → Prop
  | nil {Γ} : Statements fs Γ []
  | cons {Γ s ss} : Statement fs true Γ s → Statements fs (afterStmt Γ s) ss →
      Statements fs Γ (s :: ss)
end

mutual
def checkStmt (fs : Array Func) (inSequence : Bool) (Γ : Context) : Stmt → Bool
  | .seqn ss => checkStmts fs Γ ss.toList
  | .block ps ss => decide (StorageParams ps) && decide (DistinctParams ps) &&
      checkStmts fs (push Γ ps) ss.toList
  | .initialization p => inSequence && decide (StorageType p.typ) && decide (Fresh Γ p.id)
  | .assign a e => checkAssignment Γ a e
  | .ifThenElse e t f => checkExpr Γ e .boolean && checkStmt fs false Γ t &&
      checkStmt fs false Γ f && decide (declarationCount t = 0) && decide (declarationCount f = 0)
  | .call targets fid args => checkDirectCall fs Γ targets fid args
  | .callValue targets callee args => checkClosureCall fs Γ targets args callee
  | .deferCall callee args => checkDeferredCall fs Γ args callee
  | .panicStmt e => checkPanicArgument Γ e
  | .returnStmt => true
  | _ => false
def checkStmts (fs : Array Func) (Γ : Context) : List Stmt → Bool
  | [] => true
  | s :: ss => checkStmt fs true Γ s && checkStmts fs (afterStmt Γ s) ss
end

mutual
theorem checkStmt_sound (fs : Array Func) (b : Bool) (Γ : Context) (s : Stmt)
    (h : checkStmt fs b Γ s = true) : Statement fs b Γ s := by
  cases s <;> try simp only [checkStmt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  case seqn ss => exact .seqn (checkStmts_sound fs Γ ss.toList h)
  case block ps ss => exact .block h.1.1 h.1.2 (checkStmts_sound fs (push Γ ps) ss.toList h.2)
  case initialization p =>
    have hb := h.1.1
    subst b
    exact .initialization h.1.2 h.2
  case assign a e => exact .assign ((checkAssignment_iff _ _ _).mp h)
  case ifThenElse e t f =>
    exact .branch ((checkExpr_iff _ _ _).mp h.1.1.1.1)
      (checkStmt_sound fs false Γ t h.1.1.1.2) (checkStmt_sound fs false Γ f h.1.1.2) h.1.2 h.2
  case call targets fid args => exact .call ((checkDirectCall_iff _ _ _ _ _).mp h)
  case callValue targets callee args => exact .closureCall ((checkClosureCall_iff _ _ _ _ _).mp h)
  case deferCall callee args => exact .deferCall ((checkDeferredCall_iff _ _ _ _).mp h)
  case panicStmt e => exact .panic ((checkPanicArgument_iff _ _).mp h)
  case returnStmt => exact .ret
termination_by structural s
theorem checkStmts_sound (fs : Array Func) (Γ : Context) (ss : List Stmt)
    (h : checkStmts fs Γ ss = true) : Statements fs Γ ss := by
  cases ss with
  | nil => exact .nil
  | cons s ss =>
      simp only [checkStmts, Bool.and_eq_true] at h
      exact .cons (checkStmt_sound fs true Γ s h.1)
        (checkStmts_sound fs (afterStmt Γ s) ss h.2)
termination_by structural ss
end

theorem checkStmt_complete {fs b Γ s} (h : Statement fs b Γ s) : checkStmt fs b Γ s = true := by
  induction h using Statement.rec (motive_2 := fun Γ ss _ => checkStmts fs Γ ss = true) <;>
    simp_all [checkStmt, checkStmts, checkExpr_iff, checkAssignment_iff, checkDirectCall_iff,
      checkClosureCall_iff, checkDeferredCall_iff, checkPanicArgument_iff]

theorem checkStmts_complete {fs Γ ss} (h : Statements fs Γ ss) : checkStmts fs Γ ss = true := by
  induction h using Statements.rec (motive_1 := fun b Γ s _ => checkStmt fs b Γ s = true) <;>
    simp_all [checkStmt, checkStmts, checkExpr_iff, checkAssignment_iff, checkDirectCall_iff,
      checkClosureCall_iff, checkDeferredCall_iff, checkPanicArgument_iff]

theorem checkStmt_iff (fs : Array Func) (b : Bool) (Γ : Context) (s : Stmt) :
    checkStmt fs b Γ s = true ↔ Statement fs b Γ s :=
  ⟨checkStmt_sound fs b Γ s, checkStmt_complete⟩

theorem checkStmts_iff (fs : Array Func) (Γ : Context) (ss : List Stmt) :
    checkStmts fs Γ ss = true ↔ Statements fs Γ ss :=
  ⟨checkStmts_sound fs Γ ss, checkStmts_complete⟩

instance (fs : Array Func) (b : Bool) (Γ : Context) (s : Stmt) : Decidable (Statement fs b Γ s) :=
  decidable_of_iff (checkStmt fs b Γ s = true) (checkStmt_iff fs b Γ s)

end GoLean.GoCore.RecoveryTyping
