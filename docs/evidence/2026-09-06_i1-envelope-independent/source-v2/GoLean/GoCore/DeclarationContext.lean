import GoLean.GoCore.Declaration

/-! Positive declaration queries. These records contain no executable body,
layout, refusal, support flag or frontend construction role. The frontend
validates canonical types, nominal references and unique table identities.
-/
namespace GoLean.GoCore.Declaration

structure Signature where
  params : List Ty
  results : List Ty
  variadic : Bool
  deriving Repr

def Signature.eqb (a b : Signature) : Bool :=
  a.params == b.params && a.results == b.results && a.variadic == b.variadic

instance : BEq Signature := ⟨Signature.eqb⟩

def Signature.type (s : Signature) : Ty := .function s.params s.results s.variadic

theorem Signature.equality_exact (a b : Signature) :
    (a == b) = true ↔ a = b := by
  change (a.params == b.params && a.results == b.results && a.variadic == b.variadic) = true ↔ _
  cases a
  cases b
  simp [and_assoc]

instance : LawfulBEq Signature where
  eq_of_beq h := (Signature.equality_exact _ _).mp h
  rfl := (Signature.equality_exact _ _).mpr rfl

structure FunctionDeclaration where
  id : FuncId
  signature : Signature
  deriving Repr

structure MethodDeclaration where
  funcId : FuncId
  member : MemberId
  receiver : Ty
  signature : Signature
  deriving Repr

structure InterfaceDeclaration where
  id : TypeId
  methods : List Method
  deriving Repr

structure Context where
  functions : Array FunctionDeclaration
  methods : Array MethodDeclaration
  interfaces : Array InterfaceDeclaration
  deriving Repr

def Context.functionSignature? (c : Context) (id : FuncId) : Option Signature :=
  ((c.functions.toList.find? fun f => f.id == id).map FunctionDeclaration.signature)

def Context.methodSignature? (c : Context) (id : FuncId) : Option Signature :=
  ((c.methods.toList.find? fun m => m.funcId == id).map MethodDeclaration.signature)

/-- Lookup and signature identity need no executable definition. Missing
metadata remains missing; no default signature is inserted. -/
def Context.methodMatches (c : Context) (id : FuncId) (required : Signature) : Bool :=
  match c.methodSignature? id with
  | some signature => signature == required
  | none => false

theorem Context.methodMatches_exact (c : Context) (id : FuncId) (required : Signature) :
    c.methodMatches id required = true ↔ c.methodSignature? id = some required := by
  unfold methodMatches
  cases h : c.methodSignature? id <;> simp

/- The inventory follows nominal references, not underlying layouts. Mutual
structural descent retains references inside nested fields, methods and type
arguments without a fuel cutoff. -/
mutual

def Ty.nominalRefs : Ty → List TypeId
  | .basic _ => []
  | .named id args => id :: typesNominalRefs args
  | .pointer t | .slice t | .array _ t | .chan _ t => t.nominalRefs
  | .map k v => k.nominalRefs ++ v.nominalRefs
  | .function ps rs _ => typesNominalRefs ps ++ typesNominalRefs rs
  | .structureType fs => fieldsNominalRefs fs
  | .interfaceType ms => methodsNominalRefs ms

def typesNominalRefs : List Ty → List TypeId
  | [] => []
  | t :: ts => t.nominalRefs ++ typesNominalRefs ts

def fieldsNominalRefs : List Field → List TypeId
  | [] => []
  | .mk _ t _ _ :: fs => t.nominalRefs ++ fieldsNominalRefs fs

def methodsNominalRefs : List Method → List TypeId
  | [] => []
  | .mk _ ps rs _ :: ms => typesNominalRefs ps ++ typesNominalRefs rs ++ methodsNominalRefs ms

end

end GoLean.GoCore.Declaration
