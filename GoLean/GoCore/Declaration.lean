import GoLean.GoCore.Value

/-! Positive closed Go declaration identities, independent of executable
value representation. No constructor promises a layout, default value,
comparability, callable body, reflection operation or allocation permission.
Nominal recursion is represented by TypeId references and explicit arguments;
declaration lookup and validity belong to the separate declaration context.
-/
namespace GoLean.GoCore.Declaration

inductive Basic where
  | boolean
  | string
  | int
  | uint
  | int8
  | uint8
  | int16
  | uint16
  | int32
  | uint32
  | int64
  | uint64
  | uintptr
  | float (kind : FloatKind)
  | complex64
  | complex128
  | unsafePointer
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Go member identity: the defining package distinguishes unexported names.
The frontend resolves this fact; semantic equality does not parse source
names or infer package identity from a display string. -/
structure MemberId where
  name : String
  «package» : String
  deriving Repr, BEq, DecidableEq, Inhabited

mutual

inductive Ty where
  | basic (kind : Basic)
  | named (id : TypeId) (arguments : List Ty)
  | pointer (elem : Ty)
  | slice (elem : Ty)
  | array (length : Nat) (elem : Ty)
  | map (key elem : Ty)
  | chan (direction : ChanDir) (elem : Ty)
  | function (params results : List Ty) (variadic : Bool)
  | structureType (fields : List Field)
  /-- Complete unique method set, stored in canonical order of the exact
  package/name pair. The validity boundary enforces that normalization;
  arbitrary permutations of raw constructors are not canonical identities. -/
  | interfaceType (methods : List Method)
  deriving Repr, Inhabited

inductive Field where
  | mk (id : MemberId) (type : Ty) (embedded : Bool) (tagBytes : Array UInt8)
  deriving Repr, Inhabited

/-- A method signature does not contain receiver or binding names. A
concrete method declaration will carry receiver/dispatch facts separately. -/
inductive Method where
  | mk (id : MemberId) (params results : List Ty) (variadic : Bool)
  deriving Repr, Inhabited

end

/-! Transparent structural equality is required for kernel-checked queries.
No fuel bound or opaque derived equality over the nested type structure. -/
mutual

def Ty.eqb : Ty → Ty → Bool
  | .basic a, .basic b => decide (a = b)
  | .named i as, .named j bs => i == j && typesEq as bs
  | .pointer a, .pointer b | .slice a, .slice b => Ty.eqb a b
  | .array n a, .array m b => n == m && Ty.eqb a b
  | .map k a, .map l b => Ty.eqb k l && Ty.eqb a b
  | .chan d a, .chan e b => decide (d = e) && Ty.eqb a b
  | .function ps rs v, .function qs ss w =>
      v == w && typesEq ps qs && typesEq rs ss
  | .structureType fs, .structureType gs => fieldsEq fs gs
  | .interfaceType ms, .interfaceType ns => methodsEq ms ns
  | _, _ => false

def typesEq : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.eqb a b && typesEq as bs
  | _, _ => false

def Field.eqb : Field → Field → Bool
  | .mk i a e t, .mk j b f u => decide (i = j) && Ty.eqb a b && e == f && t == u

def fieldsEq : List Field → List Field → Bool
  | [], [] => true
  | a :: as, b :: bs => Field.eqb a b && fieldsEq as bs
  | _, _ => false

def Method.eqb : Method → Method → Bool
  | .mk i ps rs v, .mk j qs ss w =>
      decide (i = j) && typesEq ps qs && typesEq rs ss && v == w

def methodsEq : List Method → List Method → Bool
  | [], [] => true
  | a :: as, b :: bs => Method.eqb a b && methodsEq as bs
  | _, _ => false

end

instance : BEq Ty := ⟨Ty.eqb⟩
instance : BEq Field := ⟨Field.eqb⟩
instance : BEq Method := ⟨Method.eqb⟩

/-- Exact equality for the finite positive representation, including nested
signatures, field tags and type arguments. This is not an equivalence theorem
between unchecked representations and arbitrary source-level Go types. -/
theorem equality_exact :
    (∀ a b : Ty, Ty.eqb a b = true ↔ a = b) ∧
    (∀ a b : List Method, methodsEq a b = true ↔ a = b) ∧
    (∀ a b : Method, Method.eqb a b = true ↔ a = b) ∧
    (∀ a b : List Ty, typesEq a b = true ↔ a = b) ∧
    (∀ a b : List Field, fieldsEq a b = true ↔ a = b) ∧
    (∀ a b : Field, Field.eqb a b = true ↔ a = b) := by
  apply Ty.eqb.mutual_induct
  all_goals intros
  all_goals simp_all [Ty.eqb, typesEq, Field.eqb, fieldsEq, Method.eqb, methodsEq,
    and_assoc, and_left_comm, and_comm]
  case case11 =>
    rename_i a b h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    intro h
    subst b
    cases a <;> simp_all
    case named =>
      rename_i id args
      exact h2 id args id args rfl rfl rfl rfl
    case array =>
      rename_i length elem
      exact h5 length elem length elem rfl rfl rfl rfl
    case map =>
      rename_i key elem
      exact h6 key elem key elem rfl rfl rfl rfl
    case chan =>
      rename_i direction elem
      exact h7 direction elem direction elem rfl rfl rfl rfl
    case function =>
      rename_i params results variadic
      obtain ⟨hf, ht⟩ := h8 params results
      cases variadic with
      | false => exact hf params results rfl rfl rfl rfl rfl
      | true => exact ht params results rfl rfl rfl rfl rfl
  case case14 =>
    rename_i a b h1 h2
    intro h
    subst b
    cases a <;> simp_all
    rename_i head tail
    exact h2 head tail head tail rfl rfl rfl rfl
  case case18 =>
    rename_i a b h1 h2
    intro h
    subst b
    cases a <;> simp_all
    rename_i head tail
    exact h2 head tail head tail rfl rfl rfl rfl
  case case21 =>
    rename_i a b h1 h2
    intro h
    subst b
    cases a <;> simp_all
    rename_i head tail
    exact h2 head tail head tail rfl rfl rfl rfl

instance : LawfulBEq Ty where
  eq_of_beq h := (equality_exact.1 _ _).mp h
  rfl := (equality_exact.1 _ _).mpr rfl

instance : LawfulBEq Field where
  eq_of_beq h := (equality_exact.2.2.2.2.2 _ _).mp h
  rfl := (equality_exact.2.2.2.2.2 _ _).mpr rfl

instance : LawfulBEq Method where
  eq_of_beq h := (equality_exact.2.2.1 _ _).mp h
  rfl := (equality_exact.2.2.1 _ _).mpr rfl

end GoLean.GoCore.Declaration
