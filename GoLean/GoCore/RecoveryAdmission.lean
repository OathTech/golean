import GoLean.GoCore.RecoveryDiagnostics

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
  | statementProfile (fid : FuncId)
  | declarationPlacement (fid : FuncId)
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
  | .statementProfile f => s!"{f.key}: body uses a constructor, type family or branch declaration effect outside the explicit recovery profile"
  | .declarationPlacement f => s!"{f.key}: bare initialization requires an actual statement list; malformed GoCore placement"
  | .body f => s!"{f.key}: body uses the admitted surface but fails binding, expression/target sort, known-callee or capture/argument/result-vector checks"
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
  require (statementInProfile f.body = true) (.statementProfile f.id)
  require (statementPlacement false f.body = true) (.declarationPlacement f.id)
  require (Statement fs false (initialContext f) f.body) (.body f.id)
  require (ReturnPolicy f) (.missingReturn f.id)

theorem checkFunction_iff (fs : Array Func) (f : Func) :
    checkFunction fs f = .ok () ↔ FunctionTyped fs f := by
  simp only [checkFunction, sequence_eq_ok, require_eq_ok, FunctionTyped]
  constructor
  · rintro ⟨hf, hp, hr, hd, _, _, hb, ht⟩
    exact ⟨hf, hp, hr, hd, hb, ht⟩
  · rintro ⟨hf, hp, hr, hd, hb, ht⟩
    exact ⟨hf, hp, hr, hd, hb.in_profile, hb.placement, hb, ht⟩

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
