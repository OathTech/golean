import GoLean.GoCore.Ops
import Lean

/-! I1 prototype: declaration queries need no executable body.

This is a representation experiment over the current exact GoCore signatures,
not the final I1 admission boundary. In particular it does not infer an exact
Go signature from an old arity-only quarantined function, remove any marker,
or authorize entering a function whose body is absent. The final frontend must
provide positive declaration facts and checked support/closure separately.
-/
namespace GoLean.I1Prototype
open GoCore

/-- Positive declaration facts, with no body, refusal reason or support flag.
Parameter binding keys support later actual frame construction; signature
identity uses their types and variadicness, never those binding keys. -/
structure FunctionDecl where
  id : FuncId
  args : Array Param
  results : Array Param
  variadic : Bool
  wrapper : Bool
  deriving Repr

def FunctionDecl.ofFunction (f : Func) : FunctionDecl :=
  ⟨f.id, f.args, f.results, f.variadic, f.wrapper⟩

def FunctionDecl.methodSignature (d : FunctionDecl) : Array Ty × Array Ty × Bool :=
  ((d.args.extract 1 d.args.size).map Param.typ, d.results.map Param.typ, d.variadic)

def findDeclaration (ds : Array FunctionDecl) (id : FuncId) : Option FunctionDecl :=
  ds.foldl (fun found d => match found with
    | some previous => some previous
    | none => if d.id == id then some d else none) none

private theorem project_fold {α β γ δ : Type} (xs : List α)
    (step : β → α → β) (project : β → γ) (element : α → δ)
    (step' : γ → δ → γ) (initial : β)
    (commute : ∀ b a, step' (project b) (element a) = project (step b a)) :
    (xs.map element).foldl step' (project initial) =
      project (xs.foldl step initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, commute]
      exact ih (step initial x)

/-- First-match lookup is preserved, including duplicate IDs in malformed
tables. No uniqueness assumption is silently needed by this projection. -/
theorem findDeclaration_ofFunctions (fs : Array Func) (id : FuncId) :
    findDeclaration (fs.map FunctionDecl.ofFunction) id =
      (findFunctionIn? fs id).map FunctionDecl.ofFunction := by
  simp only [findDeclaration, findFunctionIn?, ← Array.foldl_toList, Array.toList_map]
  apply project_fold fs.toList _ (Option.map FunctionDecl.ofFunction)
    FunctionDecl.ofFunction _ none
  intro found f
  cases found with
  | some hit => rfl
  | none =>
      by_cases h : (f.id == id) = true <;> simp [FunctionDecl.ofFunction, h]

def methodSignature (ds : Array FunctionDecl) (info : MethodInfo) :
    Option (Array Ty × Array Ty × Bool) :=
  (findDeclaration ds info.funcId).map FunctionDecl.methodSignature

/-- The actual current method-signature query factors through declarations.
The equality retains missing/duplicate IDs, result order and variadicness. -/
theorem concreteMethodSignature_declarations (s : ExecState) (info : MethodInfo) :
    concreteMethodSignature? s info =
      methodSignature (s.functions.map FunctionDecl.ofFunction) info := by
  rw [methodSignature, findDeclaration_ofFunctions]
  unfold concreteMethodSignature?
  cases h : findFunctionIn? s.functions info.funcId <;> rfl

def satisfies (s : ExecState) (ds : Array FunctionDecl) (dynamic : Ty)
    (required : MethodSig) : Bool :=
  match concreteMethodForDynamic? s dynamic required.name with
  | some (info, _) =>
      match methodSignature ds info with
      | some (parameters, results, variadic) =>
          parameters == required.params && results == required.results &&
            variadic == required.variadic
      | none => false
  | none => false

/-- Actual satisfaction is unchanged by taking signatures from a separate
declaration table. Receiver selection still uses the existing core operation;
this theorem does not yet remove any dependency from that operation. -/
theorem satisfies_declarations (s : ExecState) (dynamic : Ty) (required : MethodSig) :
    satisfiesMethodSig s dynamic required =
      satisfies s (s.functions.map FunctionDecl.ofFunction) dynamic required := by
  unfold satisfiesMethodSig satisfies
  cases hm : concreteMethodForDynamic? s dynamic required.name with
  | none => rfl
  | some pair =>
      obtain ⟨info, adjustment⟩ := pair
      dsimp only
      rw [concreteMethodSignature_declarations]
      with_unfolding_all rfl

theorem declaration_body_independent (f : Func) (body : Stmt) :
    FunctionDecl.ofFunction { f with body := body } = FunctionDecl.ofFunction f := by
  rfl

/- These probes target metadata that dummy-body replacement/pruning could
otherwise damage. They execute the actual signature query, not an invented
body evaluator. The two bodies are deliberately different. -/
private def sample (body : Stmt) (variadic : Bool := false) : Func := {
  id := ⟨"M"⟩
  args := #[⟨"recv", .bool⟩, ⟨"x", .slice .bool⟩]
  results := #[⟨"r", .bool⟩]
  body := body
  variadic := variadic
}

private def info : MethodInfo := ⟨"M", ⟨"M"⟩, .bool⟩

theorem unrelated_body_has_same_signature :
    concreteMethodSignature? { functions := #[sample .returnStmt] } info =
    concreteMethodSignature? { functions := #[sample (.seqn #[])] } info := by
  rfl

theorem first_duplicate_signature_is_retained :
    methodSignature (#[sample .returnStmt true, sample (.seqn #[]) false].map
      FunctionDecl.ofFunction) info =
      some (#[.slice .bool], #[.bool], true) := by
  with_unfolding_all rfl

theorem absent_declaration_is_absent :
    methodSignature #[] info = none := by rfl

theorem declaration_without_code_retains_signature :
    methodSignature #[⟨⟨"M"⟩, #[⟨"recv", .bool⟩, ⟨"x", .slice .bool⟩],
      #[⟨"r", .bool⟩], true, false⟩] info =
      some (#[.slice .bool], #[.bool], true) := by
  with_unfolding_all rfl

end GoLean.I1Prototype

open Lean in
def auditI1Prototype : CoreM Unit := do
  let env ← getEnv
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let selected := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!.getRoot == `GoLean
      | none => true
    unless selected do continue
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "I1 prototype: forbidden axiom {ax} in {name}"
    checked := checked + 1
  logInfo s!"I1 declaration projection: {checked} imported/local declarations audited"

#eval auditI1Prototype
