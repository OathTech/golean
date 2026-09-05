import GoLean.GoCore.AdmissionPolicy

/-! Experimental first admission boundary. `checkBoolean` checks exactly
`BooleanAdmission`, not Go typing or refusal freedom. No interpreter or
frontend imports are needed, and acceptance is independent of execution.
See `docs/2026-09-05_a3-admission-design.md` for the deliberately small scope.
-/
namespace GoLean.GoCore.Admission

/-- The exact reserved entries, inspected structurally so proof computation
does not depend on the logically opaque derived `BEq TypeDef`. -/
def ReservedPrefix (types : TypeEnv) : Prop :=
  match types.toList with
  | (id₀, .struct fields) :: (id₁, .opaqueDecl reason) :: _ =>
      id₀ = emptyStructTypeId ∧ fields.size = 0 ∧
      id₁ = runtimeErrorTypeId ∧ reason = runtimeErrorOpaqueReason
  | _ => False

instance (types : TypeEnv) : Decidable (ReservedPrefix types) := by
  unfold ReservedPrefix
  split <;> infer_instance

theorem reservedPrefix_exact {types : TypeEnv} (h : ReservedPrefix types) :
    types.toList.take 2 = TypeEnv.reserved.toList := by
  unfold ReservedPrefix at h
  split at h
  · obtain ⟨h₀, hfields, h₁, hreason⟩ := h
    have hfields' := Array.eq_empty_of_size_eq_zero hfields
    simp_all [TypeEnv.reserved]
  · contradiction

/-- Unlike a full program well-formedness judgment, this checks only the
reserved prefix, type resolution order, unique keys, and `Ty.defined`
bounds. It deliberately does not assert lexical or semantic name validity. -/
def IndexStructure (p : Program) : Prop :=
  ReservedPrefix p.typeDefs ∧ p.typeDefs.WellFounded ∧
  (p.typeDefs.toList.map (fun t => t.1.key)).Nodup ∧
  (p.funcs.toList.map (fun f => f.id.key)).Nodup ∧ IndicesBound p

def InitialArguments (args : Array GoValue) : Prop :=
  ∀ v ∈ args.toList, InitialValueHasType v .bool
instance (args : Array GoValue) : Decidable (InitialArguments args) :=
  inferInstanceAs (Decidable (∀ v ∈ args.toList, InitialValueHasType v .bool))

/-- Actual driver lookup plus a bounded argument/type boundary. No
normalization result is treated as evidence of argument typing. -/
def Entry (p : Program) (name : String) (args : Array GoValue) : Prop :=
  match findFunctionIn? p.funcs ⟨name⟩ with
  | none => False
  | some f => f.args.size = args.size ∧ BoolParams f.args ∧ InitialArguments args

/-- This name is intentionally profile-specific. It does not mean
`ProgramWellTyped`, successful execution, or a typed runtime state. -/
def BooleanAdmission (p : Program) (name : String) (args : Array GoValue) : Prop :=
  IndexStructure p ∧ Entry p name args ∧ BooleanSyntax p

inductive Error where
  | reservedPrefix
  | typeDependencyOrder
  | duplicateTypeKey
  | duplicateFunctionKey
  | typeIndexBounds
  | missingEntry (name : String)
  | entryArity (expected actual : Nat)
  | entryParameterTypes
  | initialArgumentTypes
  | booleanSyntaxPolicy
  deriving Repr, DecidableEq

def Error.message : Error → String
  | .reservedPrefix => "type table must lead with the exact machine-reserved entries"
  | .typeDependencyOrder => "type table violates the dependency order (a forward edge or cycle)"
  | .duplicateTypeKey => "type table contains duplicate semantic type keys"
  | .duplicateFunctionKey => "function table contains duplicate semantic function keys"
  | .typeIndexBounds => "a Ty.defined index in the type table or program is out of bounds"
  | .missingEntry name => s!"entry function not found: {name}"
  | .entryArity expected actual => s!"entry expects {expected} arguments, got {actual}"
  | .entryParameterTypes => "this initial profile requires Boolean entry parameter types"
  | .initialArgumentTypes => "this initial profile requires Boolean argument values"
  | .booleanSyntaxPolicy =>
      "program is outside the Boolean syntax policy (all function bodies, initialization, globals and method declarations are checked)"

def require (p : Prop) [Decidable p] (error : Error) : Except Error Unit :=
  if p then .ok () else .error error

@[simp] theorem require_eq_ok (p : Prop) [Decidable p] (e : Error) :
    require p e = .ok () ↔ p := by
  by_cases h : p <;> simp [require, h]

@[simp] theorem sequence_eq_ok (x y : Except Error Unit) :
    (x >>= fun _ => y) = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x with
  | ok u => cases u; simp [Bind.bind, Except.bind]
  | error e => simp [Bind.bind, Except.bind]

def checkIndices (p : Program) : Except Error Unit := do
  require (ReservedPrefix p.typeDefs) .reservedPrefix
  require p.typeDefs.WellFounded .typeDependencyOrder
  require (p.typeDefs.toList.map (fun t => t.1.key)).Nodup .duplicateTypeKey
  require (p.funcs.toList.map (fun f => f.id.key)).Nodup .duplicateFunctionKey
  require (IndicesBound p) .typeIndexBounds

theorem checkIndices_iff (p : Program) :
    checkIndices p = .ok () ↔ IndexStructure p := by
  simp only [checkIndices, sequence_eq_ok, require_eq_ok, IndexStructure]

def checkEntry (p : Program) (name : String) (args : Array GoValue) : Except Error Unit :=
  match findFunctionIn? p.funcs ⟨name⟩ with
  | none => .error (.missingEntry name)
  | some f => do
      require (f.args.size = args.size) (.entryArity f.args.size args.size)
      require (BoolParams f.args) .entryParameterTypes
      require (InitialArguments args) .initialArgumentTypes

theorem checkEntry_iff (p : Program) (name : String) (args : Array GoValue) :
    checkEntry p name args = .ok () ↔ Entry p name args := by
  unfold checkEntry Entry
  split <;> simp only [sequence_eq_ok, require_eq_ok, reduceCtorEq]

def checkBoolean (p : Program) (name : String) (args : Array GoValue) : Except Error Unit := do
  checkIndices p
  checkEntry p name args
  require (BooleanSyntax p) .booleanSyntaxPolicy

theorem checkBoolean_iff (p : Program) (name : String) (args : Array GoValue) :
    checkBoolean p name args = .ok () ↔ BooleanAdmission p name args := by
  simp only [checkBoolean, sequence_eq_ok, require_eq_ok, checkIndices_iff,
    checkEntry_iff, BooleanAdmission]

theorem checkBoolean_sound {p : Program} {name : String} {args : Array GoValue}
    (h : checkBoolean p name args = .ok ()) : BooleanAdmission p name args :=
  (checkBoolean_iff p name args).mp h

theorem checkBoolean_complete {p : Program} {name : String} {args : Array GoValue}
    (h : BooleanAdmission p name args) : checkBoolean p name args = .ok () :=
  (checkBoolean_iff p name args).mpr h

theorem admitted_index_bound {p : Program} {name : String} {args : Array GoValue}
    (h : BooleanAdmission p name args) {i : TypeIdx} (hi : i ∈ programIndices p) :
    i < p.typeDefs.size := h.1.2.2.2.2 i hi

theorem admitted_all_bodies {p : Program} {name : String} {args : Array GoValue}
    (h : BooleanAdmission p name args) {f : Func} (hf : f ∈ p.funcs.toList) :
    BoolStmt f.body := (h.2.2.2.2 f hf).2.2.2.2.2

theorem admitted_no_initializer {p : Program} {name : String} {args : Array GoValue}
    (h : BooleanAdmission p name args) {f : Func} (hf : f ∈ p.funcs.toList) :
    f.id ≠ pkgInitFuncId := (h.2.2.2.2 f hf).1

end GoLean.GoCore.Admission
