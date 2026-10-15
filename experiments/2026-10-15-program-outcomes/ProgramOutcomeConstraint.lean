import GoLean.Relational

/-! Exact correspondence obligations from the early C2 interface checkpoint.
The implementation must supply these through the facade, with no assumed law. -/
namespace C2Constraint
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


end C2Constraint
