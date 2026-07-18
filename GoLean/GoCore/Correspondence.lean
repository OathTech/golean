import GoLean.GoCore.Rel
import GoLean.GoCore.Eval

/-!
# Interpreter/relation correspondence

States the intended relationship between the executable interpreter
(`GoLean.GoCore.Eval`) and the relational skeleton (`GoLean.GoCore.Rel`),
and proves small instances that exercise the relational rules.

The full soundness proofs are deliberately deferred: the skeleton exists to
force every interpreter feature to have an explicit rule shape, not to
block cleanup on proof engineering. The statements below are the contract
new features must keep provable in principle.
-/

namespace GoLean.GoCore.Correspondence

open GoLean GoLean.GoCore GoLean.GoCore.Rel

/-- Intended soundness of the interpreter against the relation, for
supported deterministic terminating runs: a normal interpreter completion
is a reachable terminal of the step relation. (Analogous statements for
returned/broke/continued outcomes quantify over the matching unwinding
configurations, and interpreter panics correspond to `Config.panicked`.)
Deferred, not yet proven. -/
def interpreterSoundStatement : Prop :=
  ∀ (fuel : Nat) (s s' : ExecState) (stmt : Stmt),
    execStmt fuel s stmt = .ok (.normal s') →
    Steps (.exec stmt .stop s) (.next .stop s')

/-- Intended panic agreement: if the interpreter reports a Go panic, the
relation reaches `panicked` with the same message. Deferred. -/
def interpreterPanicStatement : Prop :=
  ∀ (fuel : Nat) (s : ExecState) (stmt : Stmt) (msg : String),
    execStmt fuel s stmt = .error (.panic msg) →
    Steps (.exec stmt .stop s) (.panicked msg)

/-! ## Proven instances

Concrete derivations over rules with no opaque function premises, checking
that the control-flow rules compose the way the interpreter behaves. -/

/-- An empty sequence completes normally in two steps. -/
theorem seqnNilSteps (s : ExecState) :
    Steps (.exec (.seqn #[]) .stop s) (.next .stop s) :=
  ((Steps.single .seqn).tail .seqDone)

/-- `while false { body }` skips its body: condition literals evaluate by
rule, the loop exits normally. -/
theorem whileFalseSteps (s : ExecState) (body : Stmt) :
    Steps (.exec (.while (.boolLit false) body) .stop s) (.next .stop s) :=
  Steps.single (.whileFalse .boolLit)

/-- `if true { return } else {}` reaches the returning configuration and
unwinds through sequence context. -/
theorem ifTrueReturnSteps (s : ExecState) :
    Steps
      (.exec (.seqn #[.ifThenElse (.boolLit true) .returnStmt (.seqn #[])]) .stop s)
      (.returning .stop s) :=
  (((((Steps.single .seqn).tail
      .seqNext).tail
      (.ifTrue .boolLit)).tail
      .returnStmt).tail
      .seqReturn)

/-- `break` inside `while true` exits the loop normally: the breaking
configuration is absorbed by the loop context. -/
theorem whileTrueBreakSteps (s : ExecState) :
    Steps (.exec (.while (.boolLit true) .breakStmt) .stop s) (.next .stop s) :=
  (((Steps.single (.whileTrue .boolLit)).tail
      .breakStmt).tail
      .loopBreak)

/-- Divide-by-zero is panic behavior, not stuckness: `x = 1 / 0` steps to
`panicked` with Go's message whenever the target local resolves. -/
theorem divByZeroPanics (s : ExecState) (loc : Loc)
    (h : lookupLoc s "x" = .ok loc) :
    Steps
      (.exec (.assign (.var "x") (.div (.intLit 1) (.intLit 0))) .stop s)
      (.panicked "runtime error: integer divide by zero") :=
  Steps.single (.assignValuePanic (.var h) (.divByZero .intLit .intLit))

end GoLean.GoCore.Correspondence
