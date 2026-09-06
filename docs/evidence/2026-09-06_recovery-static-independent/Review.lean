import GoLean.GoCore.BooleanTyping
import GoLean.GoCore.Ops
import Lean


/-! Independent static type classes and first-match scoped lookup for the
recovery profile. A root-reference expression has a stronger runtime contract
than Go's pointer type: its referenced Boolean cell is live and non-null.
Only checked argument/capture construction may establish that refinement. -/
namespace GoLean.GoCore.RecoveryTyping

inductive ValueSort where
  | boolean | root | payload | string
  deriving Repr, DecidableEq, BEq

inductive TypeClass : Ty → ValueSort → Prop
  | boolean : TypeClass .bool .boolean
  | root : TypeClass (.pointer .bool) .root
  | payload {id : TypeId} : isEmptyInterfaceName id = true →
      TypeClass (.interface id) .payload
  | string : TypeClass .string .string

def checkType : Ty → ValueSort → Bool
  | .bool, .boolean | .pointer .bool, .root | .string, .string => true
  | .interface id, .payload => isEmptyInterfaceName id
  | _, _ => false

theorem checkType_sound (ty : Ty) (s : ValueSort) (h : checkType ty s = true) :
    TypeClass ty s := by
  cases ty <;> cases s <;> try simp only [checkType, Bool.false_eq_true] at h
  case bool.boolean => exact .boolean
  case string.string => exact .string
  case pointer.root ty =>
    cases ty <;> simp only [Bool.false_eq_true] at h
    exact .root
  case interface.payload id => exact .payload h

theorem checkType_complete {ty s} (h : TypeClass ty s) : checkType ty s = true := by
  cases h <;> first | assumption | rfl

theorem checkType_iff (ty : Ty) (s : ValueSort) : checkType ty s = true ↔ TypeClass ty s :=
  ⟨checkType_sound ty s, checkType_complete⟩

instance (ty : Ty) (s : ValueSort) : Decidable (TypeClass ty s) :=
  decidable_of_iff (checkType ty s = true) (checkType_iff ty s)

abbrev Scope := List (String × Ty)
abbrev Context := List Scope

def scopeLookup : Scope → String → Option Ty
  | [], _ => none
  | (name, ty) :: rest, needle =>
      if name = needle then some ty else scopeLookup rest needle

def lookup : Context → String → Option Ty
  | [], _ => none
  | scope :: rest, name =>
      match scopeLookup scope name with
      | some ty => some ty
      | none => lookup rest name

def declare (Γ : Context) (p : Param) : Context :=
  match Γ with
  | [] => [[(p.id, p.typ)]]
  | scope :: rest => ((p.id, p.typ) :: scope) :: rest

def push (Γ : Context) (ps : Array Param) : Context :=
  ps.toList.map (fun p => (p.id, p.typ)) :: Γ

def initialContext (f : Func) : Context :=
  [(f.args.toList ++ f.results.toList).map (fun p => (p.id, p.typ))]

def Fresh (Γ : Context) (name : String) : Prop := scopeLookup (Γ.headD []) name = none
instance (Γ : Context) (name : String) : Decidable (Fresh Γ name) :=
  inferInstanceAs (Decidable (scopeLookup (Γ.headD []) name = none))

/-- Existential lookup evidence specifies the first matching declaration,
not membership anywhere in a scope union. -/
def Has (Γ : Context) (name : String) (s : ValueSort) : Prop :=
  ∃ ty, lookup Γ name = some ty ∧ TypeClass ty s

def checkHas (Γ : Context) (name : String) (s : ValueSort) : Bool :=
  match lookup Γ name with
  | some ty => checkType ty s
  | none => false

theorem checkHas_iff (Γ : Context) (name : String) (s : ValueSort) :
    checkHas Γ name s = true ↔ Has Γ name s := by
  unfold checkHas Has
  cases h : lookup Γ name with
  | none => simp
  | some ty => simp [checkType_iff]

instance (Γ : Context) (name : String) (s : ValueSort) : Decidable (Has Γ name s) :=
  decidable_of_iff (checkHas Γ name s = true) (checkHas_iff Γ name s)

theorem lookup_declare (Γ : Context) (p : Param) (name : String) :
    lookup (declare Γ p) name =
      if p.id = name then some p.typ else lookup Γ name := by
  by_cases h : p.id = name <;> cases Γ <;> simp [declare, lookup, scopeLookup, h]

theorem has_declare_self (Γ : Context) (p : Param) (s : ValueSort) (ht : TypeClass p.typ s) :
    Has (declare Γ p) p.id s := ⟨p.typ, by simp [lookup_declare], ht⟩

inductive NilType : Option Ty → Prop
  | untyped : NilType none
  | typed {ty} : TypeClass ty .payload → NilType (some ty)

def checkNilType : Option Ty → Bool
  | none => true
  | some ty => checkType ty .payload

theorem checkNilType_iff (ty : Option Ty) : checkNilType ty = true ↔ NilType ty := by
  cases ty with
  | none => constructor <;> intro h
            · exact .untyped
            · rfl
  | some ty =>
      constructor
      · exact fun h => .typed ((checkType_iff ty .payload).mp h)
      · intro h; cases h with | typed ht => exact checkType_complete ht

inductive NilExpr : Expr → Prop
  | nil {ty} : NilType ty → NilExpr (.nil ty)

def checkNilExpr : Expr → Bool
  | .nil ty => checkNilType ty
  | _ => false

theorem checkNilExpr_iff (e : Expr) : checkNilExpr e = true ↔ NilExpr e := by
  cases e <;> try (constructor <;> intro h <;> cases h)
  case nil ty =>
    constructor
    · exact fun h => .nil ((checkNilType_iff ty).mp h)
    · intro h; cases h with | nil ht => exact (checkNilType_iff ty).mpr ht

end GoLean.GoCore.RecoveryTyping


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


namespace GoLean.GoCore.RecoveryTyping

inductive Arguments (Γ : Context) : List Expr → List Param → Prop
  | nil : Arguments Γ [] []
  | cons {e es p ps} : ExprAt Γ e p.typ → Arguments Γ es ps →
      Arguments Γ (e :: es) (p :: ps)

def checkArguments (Γ : Context) : List Expr → List Param → Bool
  | [], [] => true
  | e :: es, p :: ps => checkExprAt Γ e p.typ && checkArguments Γ es ps
  | _, _ => false

theorem checkArguments_iff (Γ : Context) (es : List Expr) (ps : List Param) :
    checkArguments Γ es ps = true ↔ Arguments Γ es ps := by
  constructor
  · induction es generalizing ps with
    | nil =>
        cases ps with
        | nil => exact fun _ => .nil
        | cons => simp [checkArguments]
    | cons e es ih =>
        cases ps with
        | nil => simp [checkArguments]
        | cons p ps =>
            simp only [checkArguments, Bool.and_eq_true]
            exact fun h => .cons ((checkExprAt_iff _ _ _).mp h.1) (ih _ h.2)
  · intro h; induction h <;> simp_all [checkArguments, checkExprAt_iff]

instance (Γ : Context) (es : List Expr) (ps : List Param) : Decidable (Arguments Γ es ps) :=
  decidable_of_iff (checkArguments Γ es ps = true) (checkArguments_iff Γ es ps)

theorem Arguments.length {Γ es ps} (h : Arguments Γ es ps) : es.length = ps.length := by
  induction h <;> simp_all

inductive Targets (Γ : Context) : List Assignee → List Param → Prop
  | nil : Targets Γ [] []
  | cons {a as p ps} : TargetAt Γ a p.typ → Targets Γ as ps →
      Targets Γ (a :: as) (p :: ps)

def checkTargets (Γ : Context) : List Assignee → List Param → Bool
  | [], [] => true
  | a :: as, p :: ps => checkTargetAt Γ a p.typ && checkTargets Γ as ps
  | _, _ => false

theorem checkTargets_iff (Γ : Context) (as : List Assignee) (ps : List Param) :
    checkTargets Γ as ps = true ↔ Targets Γ as ps := by
  constructor
  · induction as generalizing ps with
    | nil =>
        cases ps with
        | nil => exact fun _ => .nil
        | cons => simp [checkTargets]
    | cons a as ih =>
        cases ps with
        | nil => simp [checkTargets]
        | cons p ps =>
            simp only [checkTargets, Bool.and_eq_true]
            exact fun h => .cons ((checkTargetAt_iff _ _ _).mp h.1) (ih _ h.2)
  · intro h; induction h <;> simp_all [checkTargets, checkTargetAt_iff]

instance (Γ : Context) (as : List Assignee) (ps : List Param) : Decidable (Targets Γ as ps) :=
  decidable_of_iff (checkTargets Γ as ps = true) (checkTargets_iff Γ as ps)

theorem Targets.length {Γ as ps} (h : Targets Γ as ps) : as.length = ps.length := by
  induction h <;> simp_all

inductive Captures (Γ : Context) : List Expr → Prop
  | nil : Captures Γ []
  | cons {e es} : ExprTyped Γ e .root → Captures Γ es → Captures Γ (e :: es)

def checkCaptures (Γ : Context) : List Expr → Bool
  | [] => true
  | e :: es => checkExpr Γ e .root && checkCaptures Γ es

theorem checkCaptures_iff (Γ : Context) (es : List Expr) :
    checkCaptures Γ es = true ↔ Captures Γ es := by
  constructor
  · induction es with
    | nil => exact fun _ => .nil
    | cons e es ih =>
        simp only [checkCaptures, Bool.and_eq_true]
        exact fun h => .cons ((checkExpr_iff _ _ _).mp h.1) (ih h.2)
  · intro h; induction h <;> simp_all [checkCaptures, checkExpr_iff]

instance (Γ : Context) (es : List Expr) : Decidable (Captures Γ es) :=
  decidable_of_iff (checkCaptures Γ es = true) (checkCaptures_iff Γ es)

/-- Lookup and complete arity/type vectors for an ordinary direct call. -/
def DirectCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (fid : FuncId) (args : Array Expr) : Prop :=
  ∃ f, findFunctionIn? fs fid = some f ∧
    Arguments Γ args.toList f.args.toList ∧ Targets Γ targets.toList f.results.toList

def checkDirectCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (fid : FuncId) (args : Array Expr) : Bool :=
  match findFunctionIn? fs fid with
  | none => false
  | some f => checkArguments Γ args.toList f.args.toList &&
      checkTargets Γ targets.toList f.results.toList

theorem checkDirectCall_iff (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (fid : FuncId) (args : Array Expr) :
    checkDirectCall fs Γ targets fid args = true ↔ DirectCall fs Γ targets fid args := by
  unfold checkDirectCall DirectCall
  cases h : findFunctionIn? fs fid <;>
    simp [checkArguments_iff, checkTargets_iff]

/-- Captures are typed root expressions, occupy the actual parameter prefix,
and are prepended to explicit arguments exactly as frame entry does. -/
inductive ClosureCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (args : Array Expr) : Expr → Prop
  | known {fid caps f} : findFunctionIn? fs fid = some f → Captures Γ caps.toList →
      Arguments Γ (caps.toList ++ args.toList) f.args.toList →
      Targets Γ targets.toList f.results.toList →
      ClosureCall fs Γ targets args (.funcVal fid caps)

def checkClosureCall (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (args : Array Expr) : Expr → Bool
  | .funcVal fid caps =>
      match findFunctionIn? fs fid with
      | none => false
      | some f => checkCaptures Γ caps.toList &&
          checkArguments Γ (caps.toList ++ args.toList) f.args.toList &&
          checkTargets Γ targets.toList f.results.toList
  | _ => false

theorem checkClosureCall_iff (fs : Array Func) (Γ : Context) (targets : Array Assignee)
    (args : Array Expr) (callee : Expr) :
    checkClosureCall fs Γ targets args callee = true ↔ ClosureCall fs Γ targets args callee := by
  constructor
  · intro h
    cases callee <;> try (simp only [checkClosureCall, Bool.false_eq_true] at h)
    case funcVal fid caps =>
      split at h
      · contradiction
      · rename_i f hf
        simp only [Bool.and_eq_true] at h
        exact .known hf ((checkCaptures_iff _ _).mp h.1.1)
          ((checkArguments_iff _ _ _).mp h.1.2) ((checkTargets_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | known hf hc ha ht =>
        simp [checkClosureCall, hf, checkCaptures_iff, checkArguments_iff, checkTargets_iff,
          hc, ha, ht]

/-- Deferred invocation checks the same complete input vector, but has no
ordinary result-target constraint: Go deliberately discards deferred results. -/
inductive DeferredCall (fs : Array Func) (Γ : Context) (args : Array Expr) : Expr → Prop
  | known {fid caps f} : findFunctionIn? fs fid = some f → Captures Γ caps.toList →
      Arguments Γ (caps.toList ++ args.toList) f.args.toList →
      DeferredCall fs Γ args (.funcVal fid caps)

def checkDeferredCall (fs : Array Func) (Γ : Context) (args : Array Expr) : Expr → Bool
  | .funcVal fid caps =>
      match findFunctionIn? fs fid with
      | none => false
      | some f => checkCaptures Γ caps.toList &&
          checkArguments Γ (caps.toList ++ args.toList) f.args.toList
  | _ => false

theorem checkDeferredCall_iff (fs : Array Func) (Γ : Context) (args : Array Expr)
    (callee : Expr) :
    checkDeferredCall fs Γ args callee = true ↔ DeferredCall fs Γ args callee := by
  constructor
  · intro h
    cases callee <;> try (simp only [checkDeferredCall, Bool.false_eq_true] at h)
    case funcVal fid caps =>
      split at h
      · contradiction
      · rename_i f hf
        simp only [Bool.and_eq_true] at h
        exact .known hf ((checkCaptures_iff _ _).mp h.1) ((checkArguments_iff _ _ _).mp h.2)
  · intro h
    cases h with
    | known hf hc ha =>
        simp [checkDeferredCall, hf, checkCaptures_iff, checkArguments_iff, hc, ha]

end GoLean.GoCore.RecoveryTyping


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


namespace GoLean.GoCore.RecoveryTyping

/- Direct calls and statically known closure invocations all create edges,
including defers and syntactically unreachable branches. The grammar does
not permit function values hidden in arbitrary expressions or heap cells. -/
mutual
inductive Calls : Stmt → FuncId → Prop
  | direct {targets fid args} : Calls (.call targets fid args) fid
  | closure {targets fid caps args} : Calls (.callValue targets (.funcVal fid caps) args) fid
  | deferred {fid caps args} : Calls (.deferCall (.funcVal fid caps) args) fid
  | seqn {ss fid} : CallsList ss.toList fid → Calls (.seqn ss) fid
  | block {ps ss fid} : CallsList ss.toList fid → Calls (.block ps ss) fid
  | thenBranch {e t f fid} : Calls t fid → Calls (.ifThenElse e t f) fid
  | elseBranch {e t f fid} : Calls f fid → Calls (.ifThenElse e t f) fid
inductive CallsList : List Stmt → FuncId → Prop
  | head {s ss fid} : Calls s fid → CallsList (s :: ss) fid
  | tail {s ss fid} : CallsList ss fid → CallsList (s :: ss) fid
end

mutual
def callIds : Stmt → List FuncId
  | .call _ fid _ => [fid]
  | .callValue _ (.funcVal fid _) _ | .deferCall (.funcVal fid _) _ => [fid]
  | .seqn ss | .block _ ss => callIdsList ss.toList
  | .ifThenElse _ t f => callIds t ++ callIds f
  | _ => []
def callIdsList : List Stmt → List FuncId
  | [] => []
  | s :: ss => callIds s ++ callIdsList ss
end

mutual
theorem callIds_sound (s : Stmt) (fid : FuncId) (h : fid ∈ callIds s) : Calls s fid := by
  cases s <;> try simp only [callIds, List.mem_nil_iff, List.mem_singleton] at h
  case call targets g args => subst fid; exact .direct
  case callValue targets callee args =>
    cases callee <;> simp only [callIds, List.mem_nil_iff, List.mem_singleton] at h
    subst fid
    exact .closure
  case deferCall callee args =>
    cases callee <;> simp only [callIds, List.mem_nil_iff, List.mem_singleton] at h
    subst fid
    exact .deferred
  case seqn ss => exact .seqn (callIdsList_sound ss.toList fid h)
  case block ps ss => exact .block (callIdsList_sound ss.toList fid h)
  case ifThenElse e t f =>
    rcases List.mem_append.mp h with h | h
    · exact .thenBranch (callIds_sound t fid h)
    · exact .elseBranch (callIds_sound f fid h)
termination_by structural s
theorem callIdsList_sound (ss : List Stmt) (fid : FuncId) (h : fid ∈ callIdsList ss) :
    CallsList ss fid := by
  cases ss with
  | nil => contradiction
  | cons s ss =>
      rcases List.mem_append.mp h with h | h
      · exact .head (callIds_sound s fid h)
      · exact .tail (callIdsList_sound ss fid h)
termination_by structural ss
end

theorem callIds_complete {s fid} (h : Calls s fid) : fid ∈ callIds s := by
  induction h using Calls.rec (motive_2 := fun ss fid _ => fid ∈ callIdsList ss) <;>
    simp_all [callIds, callIdsList]

theorem callIds_iff (s : Stmt) (fid : FuncId) : fid ∈ callIds s ↔ Calls s fid :=
  ⟨callIds_sound s fid, callIds_complete⟩

/-- A structural call-tree certificate. Depth counts function nodes, not
execution steps or allocations. The program checker uses its function count;
it imposes no source/function-table ordering. -/
inductive CallDepth (fs : Array Func) : Nat → FuncId → Prop
  | node {n fid f} : findFunctionIn? fs fid = some f →
      (∀ g, Calls f.body g → CallDepth fs n g) → CallDepth fs (n + 1) fid

def checkCallDepth (fs : Array Func) : Nat → FuncId → Bool
  | 0, _ => false
  | n + 1, fid =>
      match findFunctionIn? fs fid with
      | none => false
      | some f => (callIds f.body).all (checkCallDepth fs n)

theorem checkCallDepth_iff (fs : Array Func) (n : Nat) (fid : FuncId) :
    checkCallDepth fs n fid = true ↔ CallDepth fs n fid := by
  induction n generalizing fid with
  | zero =>
      constructor
      · intro h; contradiction
      · intro h; cases h
  | succ n ih =>
      constructor
      · intro h
        unfold checkCallDepth at h
        split at h
        · contradiction
        · rename_i f hf
          refine .node hf (fun g hg => (ih g).mp ?_)
          exact List.all_eq_true.mp h g (callIds_complete hg)
      · intro h
        cases h with
        | node hf hh =>
            simp only [checkCallDepth, hf]
            exact List.all_eq_true.mpr (fun g hg => (ih g).mpr (hh g (callIds_sound _ _ hg)))

instance (fs : Array Func) (n : Nat) (fid : FuncId) : Decidable (CallDepth fs n fid) :=
  decidable_of_iff (checkCallDepth fs n fid = true) (checkCallDepth_iff fs n fid)

theorem CallDepth.down {fs n fid f g} (h : CallDepth fs (n + 1) fid)
    (hf : findFunctionIn? fs fid = some f) (hg : Calls f.body g) : CallDepth fs n g := by
  cases h with
  | node hf' hh =>
      rw [hf] at hf'
      cases hf'
      exact hh _ hg

theorem no_self_call {fs n fid f} (h : CallDepth fs n fid)
    (hf : findFunctionIn? fs fid = some f) : ¬ Calls f.body fid := by
  intro hself
  induction n with
  | zero => cases h
  | succ n ih => exact ih (h.down hf hself)

def CallEdge (fs : Array Func) (fid g : FuncId) : Prop :=
  ∃ f, findFunctionIn? fs fid = some f ∧ Calls f.body g

inductive CallPath (fs : Array Func) : FuncId → FuncId → Prop
  | single {f g} : CallEdge fs f g → CallPath fs f g
  | cons {f g h} : CallEdge fs f g → CallPath fs g h → CallPath fs f h

theorem CallDepth.edge {fs n f g} (h : CallDepth fs n f) (he : CallEdge fs f g) :
    ∃ m, m < n ∧ CallDepth fs m g := by
  obtain ⟨func, hf, hg⟩ := he
  cases n with
  | zero => cases h
  | succ n => exact ⟨n, Nat.lt_succ_self n, h.down hf hg⟩

theorem CallDepth.path {fs n f g} (h : CallDepth fs n f) (hp : CallPath fs f g) :
    ∃ m, m < n ∧ CallDepth fs m g := by
  induction hp generalizing n with
  | single he => exact h.edge he
  | cons he _ ih =>
      obtain ⟨m, hm, hd⟩ := h.edge he
      obtain ⟨k, hk, hd'⟩ := ih hd
      exact ⟨k, Nat.lt_trans hk hm, hd'⟩

theorem CallDepth.no_cycle {fs} (n : Nat) (f : FuncId) (h : CallDepth fs n f) :
    ¬ CallPath fs f f := by
  intro hp
  obtain ⟨m, hm, hd⟩ := h.path hp
  exact CallDepth.no_cycle m f hd hp
termination_by n

def FiniteCalls (fs : Array Func) : Prop :=
  ∀ f ∈ fs.toList, CallDepth fs fs.size f.id

instance (fs : Array Func) : Decidable (FiniteCalls fs) :=
  inferInstanceAs (Decidable (∀ f ∈ fs.toList, CallDepth fs fs.size f.id))

end GoLean.GoCore.RecoveryTyping


/-! The second, independently checked static profile. This file establishes
admission only, not setup, runtime refusal freedom, terminal renderability,
termination or Iris ownership. A3a and O1 retain their separate predicates. -/
namespace GoLean.GoCore.RecoveryTyping
open Admission

mutual
inductive Returns : Stmt → Prop
  | ret : Returns .returnStmt
  | panic {e} : Returns (.panicStmt e)
  | seqn {ss} : ReturnsList ss.toList → Returns (.seqn ss)
  | block {ps ss} : ReturnsList ss.toList → Returns (.block ps ss)
  | branch {e t f} : Returns t → Returns f → Returns (.ifThenElse e t f)
inductive ReturnsList : List Stmt → Prop
  | last {s} : Returns s → ReturnsList [s]
  | cons {s t ss} : ReturnsList (t :: ss) → ReturnsList (s :: t :: ss)
end

mutual
def checkReturns : Stmt → Bool
  | .returnStmt | .panicStmt _ => true
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
  case panicStmt => exact .panic
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

theorem checkReturns_iff (s : Stmt) : checkReturns s = true ↔ Returns s :=
  ⟨checkReturns_sound s, checkReturns_complete⟩

instance (s : Stmt) : Decidable (Returns s) :=
  decidable_of_iff (checkReturns s = true) (checkReturns_iff s)

def FunctionFlags (f : Func) : Prop :=
  f.id ≠ pkgInitFuncId ∧ f.variadic = false ∧ f.wrapper = false
def SignatureDistinct (f : Func) : Prop :=
  ((f.args.toList ++ f.results.toList).map Param.id).Nodup
def ReturnPolicy (f : Func) : Prop := f.results.size = 0 ∨ Returns f.body
def FunctionTyped (fs : Array Func) (f : Func) : Prop :=
  FunctionFlags f ∧ ParameterTypes f.args ∧ StorageParams f.results ∧
    SignatureDistinct f ∧ Statement fs false (initialContext f) f.body ∧ ReturnPolicy f

instance (f : Func) : Decidable (FunctionFlags f) :=
  inferInstanceAs (Decidable (f.id ≠ pkgInitFuncId ∧ f.variadic = false ∧ f.wrapper = false))
instance (f : Func) : Decidable (SignatureDistinct f) :=
  inferInstanceAs (Decidable ((f.args.toList ++ f.results.toList).map Param.id).Nodup)
instance (f : Func) : Decidable (ReturnPolicy f) :=
  inferInstanceAs (Decidable (f.results.size = 0 ∨ Returns f.body))

def ProgramTyped (p : Program) : Prop :=
  p.globals.size = 0 ∧ p.methods.size = 0 ∧
    (∀ f ∈ p.funcs.toList, FunctionTyped p.funcs f) ∧ FiniteCalls p.funcs

def RecoveryAdmission (p : Program) (name : String) (args : Array GoValue) : Prop :=
  IndexStructure p ∧ Entry p name args ∧ ProgramTyped p

inductive Error where
  | boundary (cause : Admission.Error)
  | globalsOrMethods
  | functionFlags (fid : FuncId)
  | parameterProfile (fid : FuncId)
  | resultProfile (fid : FuncId)
  | signatureBindingKeys (fid : FuncId)
  | body (fid : FuncId)
  | missingReturn (fid : FuncId)
  | recursiveOrUnresolvedGraph
  deriving Repr, DecidableEq

def Error.message : Error → String
  | .boundary e => e.message
  | .globalsOrMethods => "recovery profile excludes globals, package initialization and methods"
  | .functionFlags f => s!"{f.key}: recovery profile excludes initializers, variadics and wrapper functions"
  | .parameterProfile f => s!"{f.key}: parameters must be Boolean, empty-interface payload, or checked Boolean-root reference"
  | .resultProfile f => s!"{f.key}: zero-initialized results must be Boolean or empty-interface payload (pointer zero does not provide a live root)"
  | .signatureBindingKeys f => s!"{f.key}: duplicate argument/result storage keys are outside this scoped profile; this is not a claim that repeated blank Go parameters are invalid source"
  | .body f => s!"{f.key}: body fails scoped recovery typing: check bindings, declaration placement, expression/target sorts, known callee and capture/argument/result vectors, or an unsupported profile constructor"
  | .missingReturn f => s!"{f.key}: a result-bearing function requires a terminating return/panic statement or terminating branches"
  | .recursiveOrUnresolvedGraph => "recovery profile requires a finite call/defer dependency graph; a recursive cycle or unresolved target has no certificate"

def require (p : Prop) [Decidable p] (e : Error) : Except Error Unit :=
  if p then .ok () else .error e

@[simp] theorem require_eq_ok (p : Prop) [Decidable p] (e : Error) :
    require p e = .ok () ↔ p := by
  by_cases h : p <;> simp [require, h]

@[simp] theorem sequence_eq_ok (x y : Except Error Unit) :
    (x >>= fun _ => y) = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x with
  | ok u => cases u; simp [Bind.bind, Except.bind]
  | error e => simp [Bind.bind, Except.bind]

def checkFunction (fs : Array Func) (f : Func) : Except Error Unit := do
  require (FunctionFlags f) (.functionFlags f.id)
  require (ParameterTypes f.args) (.parameterProfile f.id)
  require (StorageParams f.results) (.resultProfile f.id)
  require (SignatureDistinct f) (.signatureBindingKeys f.id)
  require (Statement fs false (initialContext f) f.body) (.body f.id)
  require (ReturnPolicy f) (.missingReturn f.id)

theorem checkFunction_iff (fs : Array Func) (f : Func) :
    checkFunction fs f = .ok () ↔ FunctionTyped fs f := by
  simp only [checkFunction, sequence_eq_ok, require_eq_ok, FunctionTyped]

def checkFunctions (fs : Array Func) : List Func → Except Error Unit
  | [] => .ok ()
  | f :: rest => do checkFunction fs f; checkFunctions fs rest

theorem checkFunctions_iff (fs : Array Func) (functions : List Func) :
    checkFunctions fs functions = .ok () ↔ ∀ f ∈ functions, FunctionTyped fs f := by
  induction functions with
  | nil => simp [checkFunctions]
  | cons f rest ih => simp [checkFunctions, sequence_eq_ok, checkFunction_iff, ih]

def checkRecovery (p : Program) (name : String) (args : Array GoValue) : Except Error Unit := do
  (Admission.checkIndices p).mapError .boundary
  (Admission.checkEntry p name args).mapError .boundary
  require (p.globals.size = 0 ∧ p.methods.size = 0) .globalsOrMethods
  checkFunctions p.funcs p.funcs.toList
  require (FiniteCalls p.funcs) .recursiveOrUnresolvedGraph

private theorem boundary_ok (x : Except Admission.Error Unit) :
    x.mapError Error.boundary = .ok () ↔ x = .ok () := by
  cases x <;> simp [Except.mapError]

theorem checkRecovery_iff (p : Program) (name : String) (args : Array GoValue) :
    checkRecovery p name args = .ok () ↔ RecoveryAdmission p name args := by
  simp only [checkRecovery, sequence_eq_ok, boundary_ok, require_eq_ok,
    Admission.checkIndices_iff, Admission.checkEntry_iff, checkFunctions_iff,
    RecoveryAdmission, ProgramTyped, and_assoc]

theorem checkRecovery_sound {p name args} (h : checkRecovery p name args = .ok ()) :
    RecoveryAdmission p name args := (checkRecovery_iff p name args).mp h

theorem checkRecovery_complete {p name args} (h : RecoveryAdmission p name args) :
    checkRecovery p name args = .ok () := (checkRecovery_iff p name args).mpr h

theorem admitted_all_bodies {p name args} (h : RecoveryAdmission p name args)
    {f : Func} (hf : f ∈ p.funcs.toList) : Statement p.funcs false (initialContext f) f.body :=
  (h.2.2.2.2.1 f hf).2.2.2.2.1

theorem admitted_no_cycle {p name args} (h : RecoveryAdmission p name args)
    {f : Func} (hf : f ∈ p.funcs.toList) : ¬ CallPath p.funcs f.id f.id :=
  (h.2.2.2.2.2 f hf).no_cycle

end GoLean.GoCore.RecoveryTyping

namespace GoLean.GoCore.RecoveryTyping.IndependentReview

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def anyTy : Ty := .interface ⟨"any"⟩
def unitFn (name : String) (body : Stmt := .block #[] #[]) : Func :=
  { id := ⟨name⟩, args := #[], results := #[], body := body }

-- The first binding also matters inside one scope, not only between scopes.
theorem first_match_inside_scope :
    checkExpr [[("p", anyTy), ("p", .pointer .bool)]] (.var "p") .root = false := by
  with_unfolding_all rfl

-- Reassigning a refined pointer parameter cannot erase its live-root fact.
theorem pointer_cannot_receive_nil :
    checkAssignment [[("p", .pointer .bool)]] (.var "p") (.nil none) = false := by
  with_unfolding_all rfl

-- A live root alias can be reassigned to another live Boolean cell.
theorem pointer_can_receive_live_alias :
    checkAssignment [[("p", .pointer .bool), ("b", .bool)]]
      (.var "p") (.ref "b") = true := by
  with_unfolding_all rfl

theorem pointer_result_default_rejects :
    checkFunction #[] { (unitFn "f" .returnStmt) with
      results := #[⟨"p", .pointer .bool⟩] } = .error (.resultProfile ⟨"f"⟩) := by
  with_unfolding_all rfl

-- Payload results have an admitted zero value, and recovering need not occur
-- directly in a deferred handler for the expression to be statically legal.
theorem payload_result_and_nested_recovery_admit :
    checkRecovery { funcs := #[{
      id := ⟨"entry"⟩, args := #[], results := #[⟨"r", anyTy⟩],
      body := .block #[] #[
        .ifThenElse (.and (.boolLit true) (.eqCmp anyTy .recoverCall (.nil none)))
          (.assign (.var "r") .recoverCall) (.seqn #[]), .returnStmt] }] }
      "entry" #[] = .ok () := by
  with_unfolding_all rfl

-- Both ordinary and deferred signatures are checked even where a Boolean
-- guard makes the malformed callee unreachable in execution.
theorem unreachable_missing_callee_rejects :
    checkRecovery { funcs := #[unitFn "entry"
      (.ifThenElse (.boolLit false)
        (.deferCall (.funcVal ⟨"missing"⟩ #[]) #[]) (.seqn #[]))] }
      "entry" #[] = .error (.body ⟨"entry"⟩) := by
  with_unfolding_all rfl

def mixedCycle : Program := { funcs := #[
  unitFn "entry" (.call #[] ⟨"helper"⟩ #[]),
  unitFn "helper" (.ifThenElse (.boolLit false)
    (.deferCall (.funcVal ⟨"entry"⟩ #[]) #[]) (.seqn #[]))] }

theorem unreachable_mixed_cycle_rejects :
    checkRecovery mixedCycle "entry" #[] = .error .recursiveOrUnresolvedGraph := by
  with_unfolding_all rfl

-- The table-size bound handles a maximal-length chain in reverse table order.
def reversedChain : Program := { funcs := #[
  unitFn "leaf",
  unitFn "middle" (.deferCall (.funcVal ⟨"leaf"⟩ #[]) #[]),
  unitFn "entry" (.callValue #[] (.funcVal ⟨"middle"⟩ #[]) #[])] }

theorem mixed_chain_accepts_at_table_bound :
    checkRecovery reversedChain "entry" #[] = .ok () := by
  with_unfolding_all rfl

theorem duplicate_functions_reject_before_graph :
    checkRecovery { funcs := #[unitFn "entry", unitFn "entry"] } "entry" #[] =
      .error (.boundary .duplicateFunctionKey) := by
  with_unfolding_all rfl

theorem external_pointer_parameter_is_not_an_initial_root :
    checkRecovery { funcs := #[{ (unitFn "entry") with
      args := #[⟨"p", .pointer .bool⟩] }] } "entry" #[.bool true] =
      .error (.boundary .entryParameterTypes) := by
  with_unfolding_all rfl

theorem block_restores_hidden_payload_binding :
    checkStmts #[] [[("x", anyTy)]] [
      .block #[⟨"x", .bool⟩] #[.assign (.var "x") (.boolLit true)],
      .assign (.var "x") .recoverCall] = true := by
  with_unfolding_all rfl

-- Every byte array is accepted in an explicit boxed panic, without running
-- an evaluator or depending on a renderer result.
theorem all_payload_bytes_admit (bytes : Array UInt8) :
    checkRecovery { funcs := #[unitFn "entry"
      (.panicStmt (.toInterface anyTy .string (.stringLit ⟨bytes⟩)))] }
      "entry" #[] = .ok () := by
  with_unfolding_all rfl

-- Review finding: a valid Go panic with an out-of-profile payload and a
-- malformed unbound write currently produce exactly the same diagnostic.
theorem unsupported_and_malformed_body_diagnostics_coincide :
    checkRecovery { funcs := #[unitFn "entry"
      (.panicStmt (.toInterface anyTy .bool (.boolLit true)))] } "entry" #[] =
      .error (.body ⟨"entry"⟩) ∧
    checkRecovery { funcs := #[unitFn "entry"
      (.assign (.var "missing") (.boolLit true))] } "entry" #[] =
      .error (.body ⟨"entry"⟩) := by
  constructor <;> with_unfolding_all rfl

end GoLean.GoCore.RecoveryTyping.IndependentReview

open Lean in
def independentRecoveryAudit : CoreM Unit := do
  let env ← getEnv
  let ours := env.header.moduleNames.map fun n =>
    n.toString.startsWith "GoLean." || n.toString.startsWith "Tests."
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? name with
      | some i => ours[i.toNat]!
      | none => true
    unless localModule do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "independent recovery audit: {name} depends on forbidden axiom {ax}"
    checked := checked + 1
  logInfo s!"Independent recovery static source/probes: {checked} local declarations audited"

#eval independentRecoveryAudit
