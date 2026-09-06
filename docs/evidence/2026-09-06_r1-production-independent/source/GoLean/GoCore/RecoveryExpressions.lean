import GoLean.GoCore.RecoveryTypingCore

namespace GoLean.GoCore.RecoveryTyping

inductive ExprTyped (Γ : Context) : Expr → ValueSort → Prop
  | var {name s} : Has Γ name s → ExprTyped Γ (.var name) s
  | boolean (b : Bool) : ExprTyped Γ (.boolLit b) .boolean
  | string (s : GoString) : ExprTyped Γ (.stringLit s) .string
  | nil {ty} : NilType ty → ExprTyped Γ (.nil ty) .payload
  | not {e} : ExprTyped Γ e .boolean → ExprTyped Γ (.not e) .boolean
  | and {l r} : ExprTyped Γ l .boolean → ExprTyped Γ r .boolean →
      ExprTyped Γ (.and l r) .boolean
  | or {l r} : ExprTyped Γ l .boolean → ExprTyped Γ r .boolean →
      ExprTyped Γ (.or l r) .boolean
  | ref {name} : Has Γ name .boolean → ExprTyped Γ (.ref name) .root
  | deref {e} : ExprTyped Γ e .root → ExprTyped Γ (.deref e .bool) .boolean
  | box {target e} : TypeClass target .payload → ExprTyped Γ e .string →
      ExprTyped Γ (.toInterface target .string e) .payload
  | recover : ExprTyped Γ .recoverCall .payload
  | eqBool {ty l r} : TypeClass ty .boolean →
      ExprTyped Γ l .boolean → ExprTyped Γ r .boolean →
      ExprTyped Γ (.eqCmp ty l r) .boolean
  | neqBool {ty l r} : TypeClass ty .boolean →
      ExprTyped Γ l .boolean → ExprTyped Γ r .boolean →
      ExprTyped Γ (.neqCmp ty l r) .boolean
  | eqNil {ty l r} : TypeClass ty .payload →
      ExprTyped Γ l .payload → ExprTyped Γ r .payload → (NilExpr l ∨ NilExpr r) →
      ExprTyped Γ (.eqCmp ty l r) .boolean
  | neqNil {ty l r} : TypeClass ty .payload →
      ExprTyped Γ l .payload → ExprTyped Γ r .payload → (NilExpr l ∨ NilExpr r) →
      ExprTyped Γ (.neqCmp ty l r) .boolean

def checkExpr (Γ : Context) : Expr → ValueSort → Bool
  | .var name, s => checkHas Γ name s
  | .boolLit _, .boolean | .stringLit _, .string | .recoverCall, .payload => true
  | .nil ty, .payload => checkNilType ty
  | .not e, .boolean => checkExpr Γ e .boolean
  | .and l r, .boolean | .or l r, .boolean =>
      checkExpr Γ l .boolean && checkExpr Γ r .boolean
  | .ref name, .root => checkHas Γ name .boolean
  | .deref e .bool, .boolean => checkExpr Γ e .root
  | .toInterface target .string e, .payload =>
      checkType target .payload && checkExpr Γ e .string
  | .eqCmp ty l r, .boolean | .neqCmp ty l r, .boolean =>
      (checkType ty .boolean && checkExpr Γ l .boolean && checkExpr Γ r .boolean) ||
      (checkType ty .payload && checkExpr Γ l .payload && checkExpr Γ r .payload &&
        (checkNilExpr l || checkNilExpr r))
  | _, _ => false

theorem checkExpr_sound (Γ : Context) (e : Expr) (s : ValueSort)
    (h : checkExpr Γ e s = true) : ExprTyped Γ e s := by
  cases e <;> cases s <;>
    try simp only [checkExpr, Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h
  all_goals try exact .var ((checkHas_iff _ _ _).mp h)
  case boolLit.boolean b => exact .boolean b
  case stringLit.string str => exact .string str
  case nil.payload ty => exact .nil ((checkNilType_iff ty).mp h)
  case not.boolean e => exact .not (checkExpr_sound Γ e .boolean h)
  case and.boolean l r =>
    exact .and (checkExpr_sound Γ l .boolean h.1) (checkExpr_sound Γ r .boolean h.2)
  case or.boolean l r =>
    exact .or (checkExpr_sound Γ l .boolean h.1) (checkExpr_sound Γ r .boolean h.2)
  case ref.root name => exact .ref ((checkHas_iff _ _ _).mp h)
  case deref.boolean e ty =>
    cases ty <;> simp only [checkExpr, Bool.false_eq_true] at h
    exact .deref (checkExpr_sound Γ e .root h)
  case toInterface.payload target dynamic e =>
    cases dynamic <;> simp only [checkExpr, Bool.false_eq_true, Bool.and_eq_true] at h
    exact .box ((checkType_iff _ _).mp h.1) (checkExpr_sound Γ e .string h.2)
  case recoverCall.payload => exact .recover
  case eqCmp.boolean ty l r =>
    rcases h with h | h
    · exact .eqBool ((checkType_iff _ _).mp h.1.1)
        (checkExpr_sound Γ l .boolean h.1.2) (checkExpr_sound Γ r .boolean h.2)
    · exact .eqNil ((checkType_iff _ _).mp h.1.1.1)
        (checkExpr_sound Γ l .payload h.1.1.2) (checkExpr_sound Γ r .payload h.1.2)
        (h.2.imp (checkNilExpr_iff _).mp (checkNilExpr_iff _).mp)
  case neqCmp.boolean ty l r =>
    rcases h with h | h
    · exact .neqBool ((checkType_iff _ _).mp h.1.1)
        (checkExpr_sound Γ l .boolean h.1.2) (checkExpr_sound Γ r .boolean h.2)
    · exact .neqNil ((checkType_iff _ _).mp h.1.1.1)
        (checkExpr_sound Γ l .payload h.1.1.2) (checkExpr_sound Γ r .payload h.1.2)
        (h.2.imp (checkNilExpr_iff _).mp (checkNilExpr_iff _).mp)
termination_by structural e

theorem checkExpr_complete {Γ e s} (h : ExprTyped Γ e s) : checkExpr Γ e s = true := by
  induction h <;> simp_all [checkExpr, checkHas_iff, checkType_iff, checkNilType_iff,
    checkNilExpr_iff]

theorem checkExpr_iff (Γ : Context) (e : Expr) (s : ValueSort) :
    checkExpr Γ e s = true ↔ ExprTyped Γ e s :=
  ⟨checkExpr_sound Γ e s, checkExpr_complete⟩

instance (Γ : Context) (e : Expr) (s : ValueSort) : Decidable (ExprTyped Γ e s) :=
  decidable_of_iff (checkExpr Γ e s = true) (checkExpr_iff Γ e s)

inductive ExprAt (Γ : Context) : Expr → Ty → Prop
  | typed {e ty s} : TypeClass ty s → ExprTyped Γ e s → ExprAt Γ e ty

def checkExprAt (Γ : Context) (e : Expr) (ty : Ty) : Bool :=
  (checkType ty .boolean && checkExpr Γ e .boolean) ||
  (checkType ty .root && checkExpr Γ e .root) ||
  (checkType ty .payload && checkExpr Γ e .payload) ||
  (checkType ty .string && checkExpr Γ e .string)

theorem checkExprAt_iff (Γ : Context) (e : Expr) (ty : Ty) :
    checkExprAt Γ e ty = true ↔ ExprAt Γ e ty := by
  constructor
  · simp only [checkExprAt, Bool.or_eq_true, Bool.and_eq_true]
    rintro (((h | h) | h) | h)
    all_goals exact .typed ((checkType_iff _ _).mp h.1) ((checkExpr_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | @typed s ht he =>
        cases s <;> simp [checkExprAt, checkType_complete ht, checkExpr_complete he]

instance (Γ : Context) (e : Expr) (ty : Ty) : Decidable (ExprAt Γ e ty) :=
  decidable_of_iff (checkExprAt Γ e ty = true) (checkExprAt_iff Γ e ty)

inductive TargetTyped (Γ : Context) : Assignee → ValueSort → Prop
  | var {name s} : Has Γ name s → TargetTyped Γ (.var name) s
  | addr {e} : ExprTyped Γ e .root → TargetTyped Γ (.addr e) .boolean

def checkTarget (Γ : Context) : Assignee → ValueSort → Bool
  | .var name, s => checkHas Γ name s
  | .addr e, .boolean => checkExpr Γ e .root
  | _, _ => false

theorem checkTarget_iff (Γ : Context) (a : Assignee) (s : ValueSort) :
    checkTarget Γ a s = true ↔ TargetTyped Γ a s := by
  constructor
  · intro h
    cases a <;> cases s <;> simp only [checkTarget, Bool.false_eq_true] at h
    all_goals first | exact .var ((checkHas_iff _ _ _).mp h)
                    | exact .addr ((checkExpr_iff _ _ _).mp h)
  · intro h; cases h <;> simp [checkTarget, checkHas_iff, checkExpr_iff, *]

instance (Γ : Context) (a : Assignee) (s : ValueSort) : Decidable (TargetTyped Γ a s) :=
  decidable_of_iff (checkTarget Γ a s = true) (checkTarget_iff Γ a s)

inductive TargetAt (Γ : Context) : Assignee → Ty → Prop
  | typed {a ty s} : TypeClass ty s → TargetTyped Γ a s → TargetAt Γ a ty

def checkTargetAt (Γ : Context) (a : Assignee) (ty : Ty) : Bool :=
  (checkType ty .boolean && checkTarget Γ a .boolean) ||
  (checkType ty .root && checkTarget Γ a .root) ||
  (checkType ty .payload && checkTarget Γ a .payload) ||
  (checkType ty .string && checkTarget Γ a .string)

theorem checkTargetAt_iff (Γ : Context) (a : Assignee) (ty : Ty) :
    checkTargetAt Γ a ty = true ↔ TargetAt Γ a ty := by
  constructor
  · simp only [checkTargetAt, Bool.or_eq_true, Bool.and_eq_true]
    rintro (((h | h) | h) | h)
    all_goals exact .typed ((checkType_iff _ _).mp h.1) ((checkTarget_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | @typed s ht ha =>
        cases s <;> simp [checkTargetAt, checkType_complete ht, (checkTarget_iff _ _ _).mpr ha]

instance (Γ : Context) (a : Assignee) (ty : Ty) : Decidable (TargetAt Γ a ty) :=
  decidable_of_iff (checkTargetAt Γ a ty = true) (checkTargetAt_iff Γ a ty)

end GoLean.GoCore.RecoveryTyping
