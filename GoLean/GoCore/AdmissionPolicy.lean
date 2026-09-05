import GoLean.GoCore.AdmissionIndices

/-! The first admission policy is syntactic and intentionally small. Its
inductive judgments make the fragment independent of its Boolean checkers.
It is not lexical typing, progress, preservation, or refusal freedom. -/
namespace GoLean.GoCore.Admission

def isBoolTy : Ty → Bool
  | .bool => true
  | _ => false

theorem isBoolTy_iff (t : Ty) : isBoolTy t = true ↔ t = .bool := by
  cases t <;> simp [isBoolTy]

instance (t : Ty) : Decidable (t = .bool) :=
  decidable_of_iff (isBoolTy t = true) (isBoolTy_iff t)

/-- A small value/type judgment for entry values, not a typed store. -/
inductive InitialValueHasType : GoValue → Ty → Prop
  | boolean (b : Bool) : InitialValueHasType (.bool b) .bool

def isBoolValue : GoValue → Bool
  | .bool _ => true
  | _ => false

theorem isBoolValue_iff (v : GoValue) :
    isBoolValue v = true ↔ InitialValueHasType v .bool := by
  constructor
  · intro h
    cases v <;> simp only [isBoolValue, Bool.false_eq_true] at h
    exact .boolean _
  · intro h
    cases h
    rfl

instance (v : GoValue) : Decidable (InitialValueHasType v .bool) :=
  decidable_of_iff (isBoolValue v = true) (isBoolValue_iff v)

inductive BoolExpr : Expr → Prop
  | var (x : String) : BoolExpr (.var x)
  | literal (b : Bool) : BoolExpr (.boolLit b)
  | not {e} : BoolExpr e → BoolExpr (.not e)
  | and {l r} : BoolExpr l → BoolExpr r → BoolExpr (.and l r)
  | or {l r} : BoolExpr l → BoolExpr r → BoolExpr (.or l r)

def boolExpr : Expr → Bool
  | .var _ | .boolLit _ => true
  | .not e => boolExpr e
  | .and l r | .or l r => boolExpr l && boolExpr r
  | _ => false

theorem boolExpr_sound (e : Expr) (h : boolExpr e = true) : BoolExpr e := by
  cases e <;> simp only [boolExpr, Bool.and_eq_true, Bool.false_eq_true] at h
  case var => exact .var _
  case boolLit => exact .literal _
  case not e => exact .not (boolExpr_sound e h)
  case and l r => exact .and (boolExpr_sound l h.1) (boolExpr_sound r h.2)
  case or l r => exact .or (boolExpr_sound l h.1) (boolExpr_sound r h.2)
termination_by structural e

theorem boolExpr_complete {e : Expr} (h : BoolExpr e) : boolExpr e = true := by
  induction h <;> simp_all [boolExpr]

theorem boolExpr_iff (e : Expr) : boolExpr e = true ↔ BoolExpr e :=
  ⟨boolExpr_sound e, boolExpr_complete⟩

def BoolParams (ps : Array Param) : Prop := ∀ p ∈ ps.toList, p.typ = .bool
instance (ps : Array Param) : Decidable (BoolParams ps) :=
  inferInstanceAs (Decidable (∀ p ∈ ps.toList, p.typ = .bool))

mutual
inductive BoolStmt : Stmt → Prop
  | seqn {ss} : BoolStmts ss.toList → BoolStmt (.seqn ss)
  | block {ps ss} : BoolParams ps → BoolStmts ss.toList → BoolStmt (.block ps ss)
  | initialization {p} : p.typ = .bool → BoolStmt (.initialization p)
  | assign {x e} : BoolExpr e → BoolStmt (.assign (.var x) e)
  | branch {e t f} : BoolExpr e → BoolStmt t → BoolStmt f → BoolStmt (.ifThenElse e t f)
  | ret : BoolStmt .returnStmt
inductive BoolStmts : List Stmt → Prop
  | nil : BoolStmts []
  | cons {s ss} : BoolStmt s → BoolStmts ss → BoolStmts (s :: ss)
end

mutual
def boolStmt : Stmt → Bool
  | .seqn ss => boolStmts ss.toList
  | .block ps ss => decide (BoolParams ps) && boolStmts ss.toList
  | .initialization p => isBoolTy p.typ
  | .assign (.var _) e => boolExpr e
  | .ifThenElse e t f => boolExpr e && boolStmt t && boolStmt f
  | .returnStmt => true
  | _ => false
def boolStmts : List Stmt → Bool
  | [] => true
  | s :: ss => boolStmt s && boolStmts ss
end

mutual
theorem boolStmt_sound (s : Stmt) (h : boolStmt s = true) : BoolStmt s := by
  cases s <;> try simp only [boolStmt, Bool.and_eq_true, Bool.false_eq_true] at h
  case seqn ss => exact .seqn (boolStmts_sound ss.toList h)
  case block ps ss => exact .block (of_decide_eq_true h.1) (boolStmts_sound ss.toList h.2)
  case initialization p => exact .initialization ((isBoolTy_iff p.typ).mp h)
  case assign a e =>
    cases a <;> simp only [boolStmt, Bool.false_eq_true] at h
    exact .assign (boolExpr_sound e h)
  case ifThenElse e t f =>
    exact .branch (boolExpr_sound e h.1.1) (boolStmt_sound t h.1.2) (boolStmt_sound f h.2)
  case returnStmt => exact .ret
termination_by structural s
theorem boolStmts_sound (ss : List Stmt) (h : boolStmts ss = true) : BoolStmts ss := by
  cases ss with
  | nil => exact .nil
  | cons s ss =>
    simp only [boolStmts, Bool.and_eq_true] at h
    exact .cons (boolStmt_sound s h.1) (boolStmts_sound ss h.2)
termination_by structural ss
end

theorem boolStmt_complete {s : Stmt} (h : BoolStmt s) : boolStmt s = true := by
  induction h using BoolStmt.rec (motive_2 := fun ss _ => boolStmts ss = true) <;>
    simp_all [boolStmt, boolStmts, isBoolTy_iff, boolExpr_iff]
theorem boolStmts_complete {ss : List Stmt} (h : BoolStmts ss) : boolStmts ss = true := by
  induction h using BoolStmts.rec (motive_1 := fun s _ => boolStmt s = true) <;>
    simp_all [boolStmt, boolStmts, isBoolTy_iff, boolExpr_iff]

theorem boolStmt_iff (s : Stmt) : boolStmt s = true ↔ BoolStmt s :=
  ⟨boolStmt_sound s, boolStmt_complete⟩
instance (s : Stmt) : Decidable (BoolStmt s) :=
  decidable_of_iff (boolStmt s = true) (boolStmt_iff s)

/-- All bodies are checked, including unreachable functions. Excluding the
actual driver-recognized init function prevents hidden initialization.
Method-set and display records are unchecked metadata: no admitted syntax
performs a method/interface operation or observes a type display. -/
def BooleanSyntax (p : Program) : Prop :=
  p.globals.size = 0 ∧ p.methods.size = 0 ∧
  ∀ f ∈ p.funcs.toList,
    f.id ≠ pkgInitFuncId ∧ f.variadic = false ∧ f.wrapper = false ∧
    BoolParams f.args ∧ BoolParams f.results ∧ BoolStmt f.body

instance (p : Program) : Decidable (BooleanSyntax p) :=
  inferInstanceAs (Decidable (
    p.globals.size = 0 ∧ p.methods.size = 0 ∧
    ∀ f ∈ p.funcs.toList,
      f.id ≠ pkgInitFuncId ∧ f.variadic = false ∧ f.wrapper = false ∧
      BoolParams f.args ∧ BoolParams f.results ∧ BoolStmt f.body))

end GoLean.GoCore.Admission
