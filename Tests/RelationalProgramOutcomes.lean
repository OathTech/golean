import GoLean.Relational

/-! Exact correspondence obligations from the early C2 interface checkpoint.
The implementation must supply these through the facade, with no assumed law. -/
namespace Tests.RelationalProgramOutcomes
open GoLean GoCore Relational ProgramExecution
namespace Requested
open Machine ExecutionStatement

def project : Outcome → Except Stop Readout
  | .ok values => .ok { values := values.toArray }
  | .error failure => .error failure.cause

def SegmentReplay (ctx : ProgramCtx) (seg : Segment) (ch tail : Choices) : Prop :=
  ∃ middle, ExecutionStatement.Prefix ctx seg.labels.length seg.start.store seg.start.control ch
    seg.labels seg.finish.store seg.finish.control middle ∧ replays seg.records middle tail

def OptionalReplay (ctx : ProgramCtx) : Option Segment → Choices → Choices → Prop
  | none, ch, tail => ch = tail
  | some seg, ch, tail => SegmentReplay ctx seg ch tail

def HistoryReplay (ctx : ProgramCtx) (history : History) (ch tail : Choices) : Prop :=
  ∃ middle, OptionalReplay ctx history.initialization ch middle ∧
    OptionalReplay ctx history.body middle tail

/-- Unrestricted coverage of the actual selected program result. The suffix
is a semantic witness only: even successful `Readout` does not return it. -/
def Coverage : Prop :=
  ∀ program name args fuel ch, ∃ history outcome tail,
    Execution program name args fuel history outcome ∧
    HistoryReplay ⟨program⟩ history ch tail ∧ runProgramM fuel program name args ch = project outcome

/-- Every admitted program execution realizes with arbitrary final suffix.
The same budget is supplied independently to initialization and body. -/
def Realization : Prop :=
  ∀ program name args fuel history outcome,
    Execution program name args fuel history outcome → ∀ tail,
    ∃ ch, HistoryReplay ⟨program⟩ history ch tail ∧ runProgramM fuel program name args ch = project outcome

def RefusalExclusion : Prop :=
  ∀ program name args, Avoids program name args Outcome.isRefusal → ∀ fuel ch reason,
    runProgramM fuel program name args ch ≠ .error (.refusal reason)

def FatalExclusion : Prop :=
  ∀ program name args, Avoids program name args Outcome.isFatal → ∀ fuel ch message,
    runProgramM fuel program name args ch ≠ .error (.terminal (.fatal message))

end Requested

theorem coverage : Requested.Coverage := Correspondence.coverage
theorem realization : Requested.Realization := Correspondence.realization
theorem refusal : Requested.RefusalExclusion := Correspondence.refusal_exclusion
theorem fatal : Requested.FatalExclusion := Correspondence.fatal_exclusion

#print axioms coverage
#print axioms realization
#print axioms refusal
#print axioms fatal


-- Preserve the selected history and suffix in the generic facade client.
theorem selected_history (program : Program) (name : String) (args : Array GoValue)
    (fuel : Nat) (history : History) (outcome : Outcome)
    (hx : Execution program name args fuel history outcome) (tail : Choices) :
    ∃ ch, Correspondence.HistoryReplay ⟨program⟩ history ch tail ∧
      Machine.runProgramM fuel program name args ch = Correspondence.project outcome :=
  Correspondence.realization program name args fuel history outcome hx tail

-- A real setup and normal body admit fallible readback without a safety premise.
theorem after_normal_body {program name args fuel init ready seg e}
    (hs : Setup program name args fuel init (.ok ready))
    (start : seg.start = activationPoint ready.function ready.activation)
    (body : seg.Runs .main ⟨program⟩ fuel)
    (normal : seg.outcome = .boundary .normal)
    (read : Readback ⟨program⟩ seg.finish.store ready.activation.results (.error e)) :
    Execution program name args fuel ⟨init, some seg⟩ (.error ⟨.readback, e⟩) :=
  .readbackFailed hs start body normal read

#print axioms selected_history
#print axioms after_normal_body
#print axioms Correspondence.initialization_coverage
#print axioms Correspondence.initialization_realization
#print axioms Correspondence.setup_coverage
#print axioms Correspondence.setup_realization
#print axioms Correspondence.initialization_projection
#print axioms Seeding.invalid_unreachable
#print axioms normal_iff
end Tests.RelationalProgramOutcomes

-- Phase controls originated in the independent interface review; now maintained
-- as facade regressions alongside the general laws.
set_option maxRecDepth 10000
open GoLean GoLean.GoCore GoLean.GoCore.Relational
open Machine
namespace Tests.RelationalProgramOutcomes.Controls
def emptyFunction (id : FuncId) : Func :=
  { id := id, args := #[], results := #[], body := .seqn #[] }
def both : Program := { funcs := #[emptyFunction pkgInitFuncId, emptyFunction ⟨"main"⟩] }

-- Lookup takes priority over an invalid type prefix and zero fuel.
example (fuel : Nat) (ch : Choices) :
    runProgramM fuel { funcs := #[], typeDefs := #[] } "missing" #[] ch =
      .error (.stuck "GoCore function not found: missing") := rfl

-- Arity takes priority over the same invalid prefix.
example (fuel : Nat) (ch : Choices) :
    runProgramM fuel { funcs := #[emptyFunction ⟨"main"⟩], typeDefs := #[] }
      "main" #[.bool true] ch =
      .error (.stuck "expected 0 argument(s), got 1") := rfl

-- Each phase uses three steps: the program succeeds with fuel three, not six.
example (ch : Choices) : runProgramM 3 both "main" #[] ch =
    .ok { values := #[] } := rfl
example (ch : Choices) : runProgramM 2 both "main" #[] ch = .error .fuelOut := rfl

-- A malformed initializer is rejected before either local execution.
def malformed : Program := { funcs := #[
  { emptyFunction pkgInitFuncId with results := #[⟨0, .bool⟩] }, emptyFunction ⟨"main"⟩] }
example (fuel : Nat) (ch : Choices) : runProgramM fuel malformed "main" #[] ch =
    .error (ProgramExecution.badInitializerShape) := rfl

def failingInit : Program := { funcs := #[
  { emptyFunction pkgInitFuncId with body := .unsupported "init review" },
  { emptyFunction ⟨"main"⟩ with body := .unsupported "body review" }] }
example (ch : Choices) : runProgramM 1 failingInit "main" #[] ch =
    .error (.unsupported "package init: init review") := rfl
example (ch : Choices) : runProgramM 0 failingInit "main" #[] ch =
    .error .fuelOut := rfl

-- Error projections discard phase annotations, but preserve exact diagnostics.
example (msg : String) : ProgramExecution.Correspondence.project
    (.error ⟨.initialization, ProgramExecution.initStop (.stuck msg)⟩) =
      .error (.stuck s!"package init: {msg}") := rfl

-- This is deliberately only a supplied-state component example, not a claim
-- of reachability from whole-program activation.
example (ctx : ProgramCtx) : Readback ctx {} [.base ⟨0⟩]
    (.error (.stuck s!"unbound GoCore heap location: {repr (Loc.base ⟨0⟩)}")) := rfl
end Tests.RelationalProgramOutcomes.Controls

namespace Tests.RelationalProgramOutcomes.Controls
-- An arbitrary supplied-state component control: normal local execution does
-- not by itself make arbitrary result locations readable. This is not a claim
-- that this store/location pair is reachable from whole-program activation.
theorem component_readback_after_normal (ctx : ProgramCtx) :
    Local.Execution .main ctx 0 (resumed Continuation.halt {}) []
      (resumed Continuation.halt {}) [] (.boundary .normal) 0 ∧
    Readback ctx {} [.base ⟨0⟩]
      (.error (.stuck s!"unbound GoCore heap location: {repr (Loc.base ⟨0⟩)}")) :=
  ⟨.finished (.boundary .normal (.inl rfl)) (Nat.le_refl _), rfl⟩

-- Initialization's print guard wins with no remaining fuel at the output point.
def printInit : Program := { funcs := #[
  { emptyFunction pkgInitFuncId with body := .print false #[.boolLit true] }, emptyFunction ⟨"main"⟩] }
example (ch : Choices) : Machine.runProgramM 2 printInit "main" #[] ch =
    .error (ProgramExecution.initStop Local.initializationStop) := rfl

end Tests.RelationalProgramOutcomes.Controls
