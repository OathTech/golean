import GoLean.GoCore.Admission

/-! Scoped typing for a Boolean GoCore profile. This module is independent of
the evaluator. A sequence preserves its declaration effects (the machine
splices same-environment sequences); only a block restores the outer scope.
`Statement true` is a statement-list element; bare initialization requires
that placement. The checker decides independent inductive judgments. -/
namespace GoLean.GoCore.BooleanTyping
open Admission

abbrev Context := List (List String)

def Bound (Γ : Context) (x : String) : Prop := ∃ scope ∈ Γ, x ∈ scope
instance (Γ : Context) (x : String) : Decidable (Bound Γ x) :=
  inferInstanceAs (Decidable (∃ scope ∈ Γ, x ∈ scope))

def Fresh (Γ : Context) (x : String) : Prop := x ∉ Γ.headD []
instance (Γ : Context) (x : String) : Decidable (Fresh Γ x) :=
  inferInstanceAs (Decidable (x ∉ Γ.headD []))

def declare : Context → String → Context
  | [], x => [[x]]
  | scope :: outer, x => (x :: scope) :: outer

def push (Γ : Context) (ps : Array Param) : Context :=
  ps.toList.map Param.id :: Γ

def initialContext (f : Func) : Context :=
  [(f.args.toList ++ f.results.toList).map Param.id]

@[simp] theorem bound_declare (Γ : Context) (x y : String) :
    Bound (declare Γ x) y ↔ y = x ∨ Bound Γ y := by
  cases Γ <;> simp [Bound, declare, eq_comm, or_assoc]

@[simp] theorem bound_push (Γ : Context) (ps : Array Param) (x : String) :
    Bound (push Γ ps) x ↔ x ∈ ps.toList.map Param.id ∨ Bound Γ x := by
  simp [Bound, push]

@[simp] theorem bound_initialContext (f : Func) (x : String) :
    Bound (initialContext f) x ↔
      x ∈ (f.args.toList ++ f.results.toList).map Param.id := by
  simp [Bound, initialContext]

inductive ExprTyped (Γ : Context) : Expr → Prop
  | var {x} : Bound Γ x → ExprTyped Γ (.var x)
  | literal (b : Bool) : ExprTyped Γ (.boolLit b)
  | not {e} : ExprTyped Γ e → ExprTyped Γ (.not e)
  | and {l r} : ExprTyped Γ l → ExprTyped Γ r → ExprTyped Γ (.and l r)
  | or {l r} : ExprTyped Γ l → ExprTyped Γ r → ExprTyped Γ (.or l r)

def checkExpr (Γ : Context) : Expr → Bool
  | .var x => decide (Bound Γ x)
  | .boolLit _ => true
  | .not e => checkExpr Γ e
  | .and l r | .or l r => checkExpr Γ l && checkExpr Γ r
  | _ => false

theorem checkExpr_sound (Γ : Context) (e : Expr)
    (h : checkExpr Γ e = true) : ExprTyped Γ e := by
  cases e <;> simp only [checkExpr, Bool.and_eq_true, Bool.false_eq_true] at h
  case var => exact .var (of_decide_eq_true h)
  case boolLit => exact .literal _
  case not e => exact .not (checkExpr_sound Γ e h)
  case and l r => exact .and (checkExpr_sound Γ l h.1) (checkExpr_sound Γ r h.2)
  case or l r => exact .or (checkExpr_sound Γ l h.1) (checkExpr_sound Γ r h.2)
termination_by structural e

theorem checkExpr_complete {Γ e} (h : ExprTyped Γ e) : checkExpr Γ e = true := by
  induction h <;> simp_all [checkExpr]

theorem checkExpr_iff (Γ : Context) (e : Expr) :
    checkExpr Γ e = true ↔ ExprTyped Γ e :=
  ⟨checkExpr_sound Γ e, checkExpr_complete⟩

instance (Γ : Context) (e : Expr) : Decidable (ExprTyped Γ e) :=
  decidable_of_iff (checkExpr Γ e = true) (checkExpr_iff Γ e)

/- Pure declaration effects, not an evaluator. Branches have no exported
bindings in this profile; typing requires each arm to have that effect. -/
mutual
def afterStmt (Γ : Context) : Stmt → Context
  | .initialization p => declare Γ p.id
  | .seqn ss => afterStmts Γ ss.toList
  | _ => Γ
def afterStmts (Γ : Context) : List Stmt → Context
  | [] => Γ
  | s :: ss => afterStmts (afterStmt Γ s) ss
end

theorem afterStmts_append (Γ : Context) (ss ts : List Stmt) :
    afterStmts Γ (ss ++ ts) = afterStmts (afterStmts Γ ss) ts := by
  induction ss generalizing Γ with
  | nil => rfl
  | cons s ss ih => exact ih (afterStmt Γ s)

def DistinctParams (ps : Array Param) : Prop := (ps.toList.map Param.id).Nodup
instance (ps : Array Param) : Decidable (DistinctParams ps) :=
  inferInstanceAs (Decidable (ps.toList.map Param.id).Nodup)

mutual
inductive Statement : Bool → Context → Stmt → Prop
  | seqn {inSequence Γ ss} : StmtsTyped Γ ss.toList →
      Statement inSequence Γ (.seqn ss)
  | block {inSequence Γ ps ss} : BoolParams ps → DistinctParams ps →
      StmtsTyped (push Γ ps) ss.toList → Statement inSequence Γ (.block ps ss)
  | initialization {Γ p} : p.typ = .bool → Fresh Γ p.id →
      Statement true Γ (.initialization p)
  | assign {inSequence Γ x e} : Bound Γ x → ExprTyped Γ e →
      Statement inSequence Γ (.assign (.var x) e)
  | branch {inSequence Γ e t f} : ExprTyped Γ e →
      Statement false Γ t → Statement false Γ f →
      afterStmt Γ t = Γ → afterStmt Γ f = Γ →
      Statement inSequence Γ (.ifThenElse e t f)
  | ret {inSequence Γ} : Statement inSequence Γ .returnStmt
inductive StmtsTyped : Context → List Stmt → Prop
  | nil {Γ} : StmtsTyped Γ []
  | cons {Γ s ss} : Statement true Γ s → StmtsTyped (afterStmt Γ s) ss →
      StmtsTyped Γ (s :: ss)
end

abbrev StmtTyped (Γ : Context) (s : Stmt) := Statement false Γ s

mutual
def checkStmt (inSequence : Bool) (Γ : Context) : Stmt → Bool
  | .seqn ss => checkStmts Γ ss.toList
  | .block ps ss => decide (BoolParams ps) && decide (DistinctParams ps) &&
      checkStmts (push Γ ps) ss.toList
  | .initialization p => inSequence && isBoolTy p.typ && decide (Fresh Γ p.id)
  | .assign (.var x) e => decide (Bound Γ x) && checkExpr Γ e
  | .ifThenElse e t f => checkExpr Γ e && checkStmt false Γ t &&
      checkStmt false Γ f && decide (afterStmt Γ t = Γ) && decide (afterStmt Γ f = Γ)
  | .returnStmt => true
  | _ => false
def checkStmts (Γ : Context) : List Stmt → Bool
  | [] => true
  | s :: ss => checkStmt true Γ s && checkStmts (afterStmt Γ s) ss
end

mutual
theorem checkStmt_sound (inSequence : Bool) (Γ : Context) (s : Stmt)
    (h : checkStmt inSequence Γ s = true) : Statement inSequence Γ s := by
  cases s <;> try simp only [checkStmt, Bool.and_eq_true, Bool.false_eq_true] at h
  case seqn ss => exact .seqn (checkStmts_sound Γ ss.toList h)
  case block ps ss =>
    exact .block (of_decide_eq_true h.1.1) (of_decide_eq_true h.1.2)
      (checkStmts_sound (push Γ ps) ss.toList h.2)
  case initialization p =>
    obtain ⟨⟨rfl, ht⟩, hf⟩ := h
    exact .initialization ((isBoolTy_iff p.typ).mp ht) (of_decide_eq_true hf)
  case assign a e =>
    cases a <;> simp only [checkStmt, Bool.and_eq_true, Bool.false_eq_true] at h
    exact .assign (of_decide_eq_true h.1) (checkExpr_sound Γ e h.2)
  case ifThenElse e t f =>
    exact .branch (checkExpr_sound Γ e h.1.1.1.1)
      (checkStmt_sound false Γ t h.1.1.1.2) (checkStmt_sound false Γ f h.1.1.2)
      (of_decide_eq_true h.1.2) (of_decide_eq_true h.2)
  case returnStmt => exact .ret
termination_by structural s
theorem checkStmts_sound (Γ : Context) (ss : List Stmt)
    (h : checkStmts Γ ss = true) : StmtsTyped Γ ss := by
  cases ss with
  | nil => exact .nil
  | cons s ss =>
    simp only [checkStmts, Bool.and_eq_true] at h
    exact .cons (checkStmt_sound true Γ s h.1)
      (checkStmts_sound (afterStmt Γ s) ss h.2)
termination_by structural ss
end

theorem checkStmt_complete {inSequence Γ s} (h : Statement inSequence Γ s) :
    checkStmt inSequence Γ s = true := by
  induction h using Statement.rec (motive_2 := fun Γ ss _ => checkStmts Γ ss = true) <;>
    simp_all [checkStmt, checkStmts, isBoolTy_iff, checkExpr_iff]

theorem checkStmts_complete {Γ ss} (h : StmtsTyped Γ ss) : checkStmts Γ ss = true := by
  induction h using StmtsTyped.rec
    (motive_1 := fun inSequence Γ s _ => checkStmt inSequence Γ s = true) <;>
    simp_all [checkStmt, checkStmts, isBoolTy_iff, checkExpr_iff]

theorem checkStmt_iff (inSequence : Bool) (Γ : Context) (s : Stmt) :
    checkStmt inSequence Γ s = true ↔ Statement inSequence Γ s :=
  ⟨checkStmt_sound inSequence Γ s, checkStmt_complete⟩

theorem checkStmts_iff (Γ : Context) (ss : List Stmt) :
    checkStmts Γ ss = true ↔ StmtsTyped Γ ss :=
  ⟨checkStmts_sound Γ ss, checkStmts_complete⟩

instance (inSequence : Bool) (Γ : Context) (s : Stmt) :
    Decidable (Statement inSequence Γ s) :=
  decidable_of_iff (checkStmt inSequence Γ s = true) (checkStmt_iff inSequence Γ s)
instance (Γ : Context) (ss : List Stmt) : Decidable (StmtsTyped Γ ss) :=
  decidable_of_iff (checkStmts Γ ss = true) (checkStmts_iff Γ ss)

theorem stmts_cons_iff {Γ s ss} :
    StmtsTyped Γ (s :: ss) ↔ Statement true Γ s ∧ StmtsTyped (afterStmt Γ s) ss := by
  constructor
  · intro h; cases h; exact ⟨‹_›, ‹_›⟩
  · rintro ⟨h, ht⟩; exact .cons h ht

theorem initialization_iff {inSequence Γ p} :
    Statement inSequence Γ (.initialization p) ↔
      inSequence = true ∧ p.typ = .bool ∧ Fresh Γ p.id := by
  constructor
  · intro h; cases h; exact ⟨rfl, ‹_›, ‹_›⟩
  · rintro ⟨rfl, ht, hf⟩; exact .initialization ht hf

theorem stmts_initialization_iff {Γ p ss} :
    StmtsTyped Γ (.initialization p :: ss) ↔
      p.typ = .bool ∧ Fresh Γ p.id ∧ StmtsTyped (declare Γ p.id) ss := by
  simp [stmts_cons_iff, initialization_iff, afterStmt, and_assoc]

@[simp] theorem stmts_nil (Γ : Context) : StmtsTyped Γ [] := .nil

/-- The premise needed when Machine.seqCont splices a same-scope list. -/
theorem stmts_append_iff (Γ : Context) (ss ts : List Stmt) :
    StmtsTyped Γ (ss ++ ts) ↔
      StmtsTyped Γ ss ∧ StmtsTyped (afterStmts Γ ss) ts := by
  induction ss generalizing Γ with
  | nil => simp [afterStmts]
  | cons s ss ih => simp [stmts_cons_iff, ih, afterStmts, and_assoc]

theorem Statement.inSequence {Γ s} (h : StmtTyped Γ s) : Statement true Γ s := by
  cases h with
  | seqn h => exact .seqn h
  | block ht hd hs => exact .block ht hd hs
  | assign hx he => exact .assign hx he
  | branch he ht hf et ef => exact .branch he ht hf et ef
  | ret => exact .ret

/- A separate diagnostic pass distinguishes unsupported control placement
from malformed bindings. Types and constructor membership are checked by
A3a first. This pass deliberately does not consult expression bindings. -/
mutual
def checkPlacement (inSequence : Bool) (Γ : Context) : Stmt → Bool
  | .seqn ss => checkPlacements Γ ss.toList
  | .block ps ss => checkPlacements (push Γ ps) ss.toList
  | .initialization _ => inSequence
  | .ifThenElse _ t f => checkPlacement false Γ t && checkPlacement false Γ f &&
      decide (afterStmt Γ t = Γ) && decide (afterStmt Γ f = Γ)
  | _ => true
def checkPlacements (Γ : Context) : List Stmt → Bool
  | [] => true
  | s :: ss => checkPlacement true Γ s && checkPlacements (afterStmt Γ s) ss
end

theorem Statement.placement {inSequence Γ s} (h : Statement inSequence Γ s) :
    checkPlacement inSequence Γ s = true := by
  induction h using Statement.rec
    (motive_2 := fun Γ ss _ => checkPlacements Γ ss = true) <;>
    simp_all [checkPlacement, checkPlacements]

private theorem placement_and_typed {Γ s} (p : Prop) :
    (checkPlacement false Γ s = true ∧ (StmtTyped Γ s ∧ p)) ↔
      StmtTyped Γ s ∧ p :=
  ⟨fun h => h.2, fun h => ⟨h.1.placement, h⟩⟩

/- The fragment of Go's terminating-statement criterion relevant here.
No definite-assignment premise: named results start at false. -/
mutual
inductive Returns : Stmt → Prop
  | ret : Returns .returnStmt
  | seqn {ss} : ReturnsList ss.toList → Returns (.seqn ss)
  | block {ps ss} : ReturnsList ss.toList → Returns (.block ps ss)
  | branch {e t f} : Returns t → Returns f → Returns (.ifThenElse e t f)
inductive ReturnsList : List Stmt → Prop
  | last {s} : Returns s → ReturnsList [s]
  | cons {s t ss} : ReturnsList (t :: ss) → ReturnsList (s :: t :: ss)
end

mutual
def checkReturns : Stmt → Bool
  | .returnStmt => true
  | .seqn ss | .block _ ss => checkReturnsList ss.toList
  | .ifThenElse _ t f => checkReturns t && checkReturns f
  | _ => false
def checkReturnsList : List Stmt → Bool
  | [] => false
  | [s] => checkReturns s
  | _ :: t :: ss => checkReturnsList (t :: ss)
end

mutual
theorem checkReturns_sound (s : Stmt) (h : checkReturns s = true) : Returns s := by
  cases s <;> simp only [checkReturns, Bool.and_eq_true, Bool.false_eq_true] at h
  case seqn ss => exact .seqn (checkReturnsList_sound ss.toList h)
  case block ps ss => exact .block (checkReturnsList_sound ss.toList h)
  case ifThenElse e t f => exact .branch (checkReturns_sound t h.1) (checkReturns_sound f h.2)
  case returnStmt => exact .ret
termination_by structural s
theorem checkReturnsList_sound (ss : List Stmt)
    (h : checkReturnsList ss = true) : ReturnsList ss := by
  cases ss with
  | nil => simp [checkReturnsList] at h
  | cons s ss =>
    cases ss with
    | nil => exact .last (checkReturns_sound s h)
    | cons t ss => exact .cons (checkReturnsList_sound (t :: ss) h)
termination_by structural ss
end

theorem checkReturns_complete {s} (h : Returns s) : checkReturns s = true := by
  induction h using Returns.rec (motive_2 := fun ss _ => checkReturnsList ss = true) <;>
    simp_all [checkReturns, checkReturnsList]

theorem checkReturnsList_complete {ss} (h : ReturnsList ss) :
    checkReturnsList ss = true := by
  induction h using ReturnsList.rec (motive_1 := fun s _ => checkReturns s = true) <;>
    simp_all [checkReturns, checkReturnsList]

theorem checkReturns_iff (s : Stmt) : checkReturns s = true ↔ Returns s :=
  ⟨checkReturns_sound s, checkReturns_complete⟩
instance (s : Stmt) : Decidable (Returns s) :=
  decidable_of_iff (checkReturns s = true) (checkReturns_iff s)

def SignatureDistinct (f : Func) : Prop :=
  ((f.args.toList ++ f.results.toList).map Param.id).Nodup
instance (f : Func) : Decidable (SignatureDistinct f) :=
  inferInstanceAs (Decidable ((f.args.toList ++ f.results.toList).map Param.id).Nodup)

def ReturnPolicy (f : Func) : Prop := f.results.size = 0 ∨ Returns f.body
instance (f : Func) : Decidable (ReturnPolicy f) :=
  inferInstanceAs (Decidable (f.results.size = 0 ∨ Returns f.body))

def FunctionTyped (f : Func) : Prop :=
  BoolParams f.args ∧ BoolParams f.results ∧ SignatureDistinct f ∧
    StmtTyped (initialContext f) f.body ∧ ReturnPolicy f
instance (f : Func) : Decidable (FunctionTyped f) :=
  inferInstanceAs (Decidable (BoolParams f.args ∧ BoolParams f.results ∧
    SignatureDistinct f ∧ StmtTyped (initialContext f) f.body ∧ ReturnPolicy f))

def ProgramTyped (p : Program) : Prop := ∀ f ∈ p.funcs.toList, FunctionTyped f
instance (p : Program) : Decidable (ProgramTyped p) :=
  inferInstanceAs (Decidable (∀ f ∈ p.funcs.toList, FunctionTyped f))

/-- Stronger, separately named boundary. A3a is preserved verbatim. -/
def TypedBooleanAdmission (p : Program) (name : String) (args : Array GoValue) : Prop :=
  BooleanAdmission p name args ∧ ProgramTyped p

inductive Error where
  | boundary (cause : Admission.Error)
  | duplicateSignatureBinding (function : FuncId)
  | unsupportedPlacement (function : FuncId)
  | scopedBody (function : FuncId)
  | missingReturn (function : FuncId)
  deriving Repr, DecidableEq

def Error.message : Error → String
  | .boundary cause => cause.message
  | .duplicateSignatureBinding f =>
      s!"function {f.key}: Boolean profile requires distinct GoCore parameter/result binding keys"
  | .unsupportedPlacement f =>
      s!"function {f.key}: Boolean profile requires declarations in statement lists and branch-local scope effects"
  | .scopedBody f =>
      s!"function {f.key}: unbound Boolean read/write or duplicate local declaration in the same GoCore scope"
  | .missingReturn f => s!"function {f.key}: result-bearing body must end in a terminating statement"

private def require (p : Prop) [Decidable p] (error : Error) : Except Error Unit :=
  if p then .ok () else .error error

@[simp] private theorem require_eq_ok (p : Prop) [Decidable p] (e : Error) :
    require p e = .ok () ↔ p := by
  by_cases h : p <;> simp [require, h]

@[simp] private theorem sequence_eq_ok (x y : Except Error Unit) :
    (x >>= fun _ => y) = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x with
  | ok u => cases u; simp [Bind.bind, Except.bind]
  | error e => simp [Bind.bind, Except.bind]

def checkFunctions : List Func → Except Error Unit
  | [] => .ok ()
  | f :: fs => do
      require (SignatureDistinct f) (.duplicateSignatureBinding f.id)
      require (checkPlacement false (initialContext f) f.body = true) (.unsupportedPlacement f.id)
      require (StmtTyped (initialContext f) f.body) (.scopedBody f.id)
      require (ReturnPolicy f) (.missingReturn f.id)
      checkFunctions fs

def checkTypedBoolean (p : Program) (name : String) (args : Array GoValue) :
    Except Error Unit := do
  match checkBoolean p name args with
  | .error e => .error (.boundary e)
  | .ok _ => checkFunctions p.funcs.toList

private theorem checkFunctions_iff (fs : List Func) :
    checkFunctions fs = .ok () ↔
      ∀ f ∈ fs, SignatureDistinct f ∧ StmtTyped (initialContext f) f.body ∧ ReturnPolicy f := by
  induction fs with
  | nil => simp [checkFunctions]
  | cons f fs ih => simp [checkFunctions, ih, and_assoc, placement_and_typed]

theorem checkTypedBoolean_iff (p : Program) (name : String) (args : Array GoValue) :
    checkTypedBoolean p name args = .ok () ↔ TypedBooleanAdmission p name args := by
  have hcheck : checkTypedBoolean p name args = .ok () ↔
      BooleanAdmission p name args ∧
        ∀ f ∈ p.funcs.toList, SignatureDistinct f ∧
          StmtTyped (initialContext f) f.body ∧ ReturnPolicy f := by
    unfold checkTypedBoolean
    cases h : checkBoolean p name args with
    | error e => simp [← checkBoolean_iff, h]
    | ok u => cases u; simp [← checkBoolean_iff, h, checkFunctions_iff]
  rw [hcheck]
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    intro f hf
    have hfsyntax := ha.2.2.2.2 f hf
    exact ⟨hfsyntax.2.2.2.1, hfsyntax.2.2.2.2.1, hs f hf⟩
  · rintro ⟨ha, hs⟩
    exact ⟨ha, fun f hf => (hs f hf).2.2⟩

theorem checkTypedBoolean_sound {p name args}
    (h : checkTypedBoolean p name args = .ok ()) : TypedBooleanAdmission p name args :=
  (checkTypedBoolean_iff p name args).mp h

theorem checkTypedBoolean_complete {p name args}
    (h : TypedBooleanAdmission p name args) : checkTypedBoolean p name args = .ok () :=
  (checkTypedBoolean_iff p name args).mpr h

theorem admitted_all_functions {p name args} (h : TypedBooleanAdmission p name args)
    {f : Func} (hf : f ∈ p.funcs.toList) : FunctionTyped f := h.2 f hf

end GoLean.GoCore.BooleanTyping
