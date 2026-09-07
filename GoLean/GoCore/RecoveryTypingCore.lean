import GoLean.GoCore.Admission
import GoLean.GoCore.Ops

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
