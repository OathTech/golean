import GoLean.GoCore.RelationalLocalExecution
import GoLean.GoCore.RelationalEntry

/-! All-outcome sequential program semantics. Phases preserve the actual validation,
setup, initialization, activation, body and readback order. Initialization and
body receive the same full budget independently. No tape or program driver
defines the semantic carriers; see RelationalProgramOutcomeSound for bridges. -/
namespace GoLean.GoCore.Relational.ProgramExecution
open Machine

inductive Phase where
  | lookup | arity | typeTable | globals | seededState
  | initializationShape | initialization
  | parameters | results | resultLocations | body | readback

structure Failure where
  phase : Phase
  cause : Stop

abbrev Result (α : Type) := Except Failure α

/-- Phase projection matches diagnostic wrapping only. Panic/fuel/deadlock
and fatal outcomes are not silently reclassified. -/
def initStop : Stop → Stop
  | .stuck msg => .stuck s!"package init: {msg}"
  | .unsupported msg => .unsupported s!"package init: {msg}"
  | .internal msg => .internal s!"package init: {msg}"
  | e => e

def missingFunction (name : String) : Stop := .stuck s!"GoCore function not found: {name}"
def wrongArity (expected actual : Nat) : Stop :=
  .stuck s!"expected {expected} argument(s), got {actual}"
def badTypeTable (program : Program) : Stop := .internal
  s!"program type table does not lead with the two machine-reserved entries ({emptyStructTypeId.key} at index 0, {runtimeErrorTypeId.key} at index 1): TypeEnv.hasReservedPrefix fails on a {program.typeDefs.size}-entry table — prepend TypeEnv.reserved (C2 acceptance clause)"
def badSeededState : Stop := .internal
  "seeded state ill-formed: a location in a global cell dangles beyond the allocator bound"
def badInitializerShape : Stop := .stuck
  s!"malformed {pkgInitFuncId.key}: expected no parameters and no results"

inductive Validation (program : Program) (name : String) (args : Array GoValue) :
    Result Func → Prop where
  | missing : findFunctionIn? program.funcs ⟨name⟩ = none →
      Validation program name args (.error ⟨.lookup, missingFunction name⟩)
  | arity {f} : findFunctionIn? program.funcs ⟨name⟩ = some f → f.args.size ≠ args.size →
      Validation program name args (.error ⟨.arity, wrongArity f.args.size args.size⟩)
  | types {f} : findFunctionIn? program.funcs ⟨name⟩ = some f → f.args.size = args.size →
      program.typeDefs.hasReservedPrefix = false →
      Validation program name args (.error ⟨.typeTable, badTypeTable program⟩)
  | ready {f} : findFunctionIn? program.funcs ⟨name⟩ = some f → f.args.size = args.size →
      program.typeDefs.hasReservedPrefix = true → Validation program name args (.ok f)

/-- Whole-program globals start from empty memory. The validity check follows
seeding; it is not an extra admission assumption. -/
inductive Seeding (program : Program) : Result Store → Prop where
  | failed {e} : seedGlobals ⟨program⟩ {} program.globals = .error e →
      Seeding program (.error ⟨.globals, e⟩)
  | invalid {s} : seedGlobals ⟨program⟩ {} program.globals = .ok s → ¬ StateWf ⟨program⟩ s →
      Seeding program (.error ⟨.seededState, badSeededState⟩)
  | ready {s} : seedGlobals ⟨program⟩ {} program.globals = .ok s → StateWf ⟨program⟩ s →
      Seeding program (.ok s)

/-- A local semantic execution, including its endpoint, finishing outcome,
cost and selections. Intermediate states remain available through `Runs`. -/
structure Segment where
  start : State
  finish : State
  labels : List StepLabel
  records : List PickRecord
  outcome : Local.Outcome
  cost : Nat

def Segment.Runs (mode : Local.Mode) (ctx : ProgramCtx) (fuel : Nat) (seg : Segment) : Prop :=
  Local.Execution mode ctx fuel seg.start seg.labels seg.finish seg.records seg.outcome seg.cost

def initializerPoint (f : Func) (s : Store) : State :=
  statement f.body [] ⟨.frame [] [] [] [] .stop f.id⟩ s

/-- A malformed initializer shape is rejected before entering initialization;
only actual initialization execution errors receive `initStop`. -/
inductive Initialization (ctx : ProgramCtx) (fuel : Nat) (s : Store) :
    Option Segment → Result Store → Prop where
  | absent : findFunctionIn? ctx.functions pkgInitFuncId = none → Initialization ctx fuel s none (.ok s)
  | malformed {f} : findFunctionIn? ctx.functions pkgInitFuncId = some f →
      (f.args.size ≠ 0 ∨ f.results.size ≠ 0) →
      Initialization ctx fuel s none (.error ⟨.initializationShape, badInitializerShape⟩)
  | normal {f seg} : findFunctionIn? ctx.functions pkgInitFuncId = some f →
      f.args.size = 0 → f.results.size = 0 → seg.start = initializerPoint f s →
      seg.Runs .initialization ctx fuel → seg.outcome = .boundary .normal →
      Initialization ctx fuel s (some seg) (.ok seg.finish.store)
  | stopped {f seg e} : findFunctionIn? ctx.functions pkgInitFuncId = some f →
      f.args.size = 0 → f.results.size = 0 → seg.start = initializerPoint f s →
      seg.Runs .initialization ctx fuel → seg.outcome.stop? = some e →
      Initialization ctx fuel s (some seg) (.error ⟨.initialization, initStop e⟩)

/-- Ordered activation retains the three failure sites of `LocalEntry`. -/
inductive ActivationPhase (ctx : ProgramCtx) (f : Func) (args : List GoValue) (s : Store) :
    Result Activation → Prop where
  | ready {a} : LocalEntry ctx f args s (.ok a) → ActivationPhase ctx f args s (.ok a)
  | parameters {e} : bindParams ctx [] s f.args.toList args = .error e →
      ActivationPhase ctx f args s (.error ⟨.parameters, e⟩)
  | results {env t e} : bindParams ctx [] s f.args.toList args = .ok (env, t) →
      allocDecls ctx env t f.results.toList = .error e →
      ActivationPhase ctx f args s (.error ⟨.results, e⟩)
  | locations {env t frameEnv u e} : bindParams ctx [] s f.args.toList args = .ok (env, t) →
      allocDecls ctx env t f.results.toList = .ok (frameEnv, u) →
      pinResultLocs frameEnv f.results.toList = .error e →
      ActivationPhase ctx f args s (.error ⟨.resultLocations, e⟩)

structure Ready where
  function : Func
  activation : Activation

inductive Setup (program : Program) (name : String) (args : Array GoValue) (fuel : Nat) :
    Option Segment → Result Ready → Prop where
  | validationFailed {e} : Validation program name args (.error e) →
      Setup program name args fuel none (.error e)
  | seedingFailed {f e} : Validation program name args (.ok f) → Seeding program (.error e) →
      Setup program name args fuel none (.error e)
  | initializationFailed {f s seg e} : Validation program name args (.ok f) → Seeding program (.ok s) →
      Initialization ⟨program⟩ fuel s seg (.error e) → Setup program name args fuel seg (.error e)
  | activationFailed {f s t seg e} : Validation program name args (.ok f) → Seeding program (.ok s) →
      Initialization ⟨program⟩ fuel s seg (.ok t) → ActivationPhase ⟨program⟩ f args.toList t (.error e) →
      Setup program name args fuel seg (.error e)
  | ready {f s t seg a} : Validation program name args (.ok f) → Seeding program (.ok s) →
      Initialization ⟨program⟩ fuel s seg (.ok t) → ActivationPhase ⟨program⟩ f args.toList t (.ok a) →
      Setup program name args fuel seg (.ok ⟨f, a⟩)

structure History where
  initialization : Option Segment
  body : Option Segment

abbrev Outcome := Result (List GoValue)

/-- Initialization and body each receive the full `fuel`, independently.
Readback is fallible even after a normal body execution. -/
inductive Execution (program : Program) (name : String) (args : Array GoValue) (fuel : Nat) :
    History → Outcome → Prop where
  | setupFailed {init e} : Setup program name args fuel init (.error e) →
      Execution program name args fuel ⟨init, none⟩ (.error e)
  | bodyStopped {init ready seg e} : Setup program name args fuel init (.ok ready) →
      seg.start = activationPoint ready.function ready.activation → seg.Runs .main ⟨program⟩ fuel →
      seg.outcome.stop? = some e →
      Execution program name args fuel ⟨init, some seg⟩ (.error ⟨.body, e⟩)
  | readbackFailed {init ready seg e} : Setup program name args fuel init (.ok ready) →
      seg.start = activationPoint ready.function ready.activation → seg.Runs .main ⟨program⟩ fuel →
      seg.outcome = .boundary .normal → Readback ⟨program⟩ seg.finish.store ready.activation.results (.error e) →
      Execution program name args fuel ⟨init, some seg⟩ (.error ⟨.readback, e⟩)
  | normal {init ready seg values} : Setup program name args fuel init (.ok ready) →
      seg.start = activationPoint ready.function ready.activation → seg.Runs .main ⟨program⟩ fuel →
      seg.outcome = .boundary .normal → Readback ⟨program⟩ seg.finish.store ready.activation.results (.ok values) →
      Execution program name args fuel ⟨init, some seg⟩ (.ok values)

def Outcome.isRefusal : Outcome → Prop
  | .error e => ∃ r, e.cause = .refusal r
  | .ok _ => False

def Outcome.isFatal : Outcome → Prop
  | .error e => ∃ m, e.cause = .terminal (.fatal m)
  | .ok _ => False

/-- All admitted alternatives and budgets, not one selected successful path. -/
def Avoids (program : Program) (name : String) (args : Array GoValue) (bad : Outcome → Prop) : Prop :=
  ∀ fuel history outcome, Execution program name args fuel history outcome → ¬ bad outcome

end GoLean.GoCore.Relational.ProgramExecution
