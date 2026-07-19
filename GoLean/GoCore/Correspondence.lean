import GoLean.GoCore.Rel
import GoLean.GoCore.Eval

/-!
# Interpreter/relation correspondence

States the intended relationship between the executable interpreter
(`GoLean.GoCore.Eval`) and the relational skeleton (`GoLean.GoCore.Rel`),
and proves small instances that exercise the relational rules.

Honest status (per the 2026-07 design review): these statements are not
merely "deferred" — as written they are **not yet provable**. Both the
interpreter (`Eval`) and the shared substrate (`Ops`: `loadLoc`, `valueEq`,
`normalizeValueForTy`, …) are `partial def`, which in Lean 4 emit opaque
constants with no equational lemmas, so the `execStmt … = .ok …` hypothesis
below cannot be inverted and the relation's own rule premises (which call
those partials) cannot be unfolded. Making the substrate and interpreter
total (structural where possible; a fuel or type-environment-acyclicity
argument for the type-directed ops) is the prerequisite that turns these
`Prop`s into provable theorems. That totality work is the current top
priority; until it lands, treat the correspondence as blocked, not deferred.
-/

namespace GoLean.GoCore.Correspondence

open GoLean GoLean.GoCore GoLean.GoCore.Rel

/-- Intended soundness of the interpreter against the relation, for
supported deterministic terminating runs: a normal interpreter completion
is a reachable terminal of the step relation. (Analogous statements for
returned/broke/continued outcomes quantify over the matching unwinding
configurations, and interpreter panics correspond to `Config.panicked`.)

After Reshape B (oracle externalization,
`docs/2026-07-19_reshape-b-oracle-externalization.md`) the interpreter threads
the choice stream `ch → ch'` *externally*, so it never appears in the relation's
oracle-free `ExecState`. This is what removes master-plan §8 C1's obstruction:
the interpreter's nondeterminism consumption is invisible to the state the
relation compares. Still blocked on interpreter/substrate totality (module
header) — but now the statement is over clean states. -/
def interpreterSoundStatement : Prop :=
  ∀ (fuel : Nat) (s s' : ExecState) (stmt : Stmt) (ch ch' : Choices),
    execStmt fuel s ch stmt = .ok (.normal s', ch') →
    Steps (.exec stmt .stop) s (.next .stop) s'

/-- Intended panic agreement: if the interpreter reports a Go panic, the
relation reaches `panicked` with the same message (at some fault state). The
input choice stream is threaded but irrelevant to the panic message. Deferred. -/
def interpreterPanicStatement : Prop :=
  ∀ (fuel : Nat) (s : ExecState) (stmt : Stmt) (msg : String) (ch : Choices),
    execStmt fuel s ch stmt = .error (.panic msg) →
    ∃ s', Steps (.exec stmt .stop) s (.panicked msg) s'

/-! ## Proven instances

Concrete derivations over rules with no opaque function premises, checking
that the control-flow rules compose the way the interpreter behaves. -/

/-- An empty sequence completes normally in two steps. -/
theorem seqnNilSteps (s : ExecState) :
    Steps (.exec (.seqn #[]) .stop) s (.next .stop) s :=
  ((Steps.single .seqn).tail .seqDone)

/-- `while false { body }` skips its body: condition literals evaluate by
rule, the loop exits normally. -/
theorem whileFalseSteps (s : ExecState) (body : Stmt) :
    Steps (.exec (.while (.boolLit false) body) .stop) s (.next .stop) s :=
  Steps.single (.whileFalse .boolLit)

/-- `if true { return } else {}` reaches the returning configuration and
unwinds through sequence context. -/
theorem ifTrueReturnSteps (s : ExecState) :
    Steps
      (.exec (.seqn #[.ifThenElse (.boolLit true) .returnStmt (.seqn #[])]) .stop) s
      (.returning .stop) s :=
  (((((Steps.single .seqn).tail
      .seqNext).tail
      (.ifTrue .boolLit)).tail
      .returnStmt).tail
      .seqReturn)

/-- `break` inside `while true` exits the loop normally: the breaking
configuration is absorbed by the loop context. -/
theorem whileTrueBreakSteps (s : ExecState) :
    Steps (.exec (.while (.boolLit true) .breakStmt) .stop) s (.next .stop) s :=
  (((Steps.single (.whileTrue .boolLit)).tail
      .breakStmt).tail
      .loopBreak)

/-- Divide-by-zero is panic behavior, not stuckness: `x = 1 / 0` steps to
`panicked` with Go's message whenever the target local resolves. -/
theorem divByZeroPanics (s : ExecState) (loc : Loc)
    (h : lookupLoc s "x" = .ok loc) :
    Steps
      (.exec (.assign (.var "x") (.div (.intLit 1) (.intLit 0))) .stop) s
      (.panicked "runtime error: integer divide by zero") s :=
  Steps.single (.assignValuePanic (.var h) (.divByZero .intLit .intLit))

end GoLean.GoCore.Correspondence
