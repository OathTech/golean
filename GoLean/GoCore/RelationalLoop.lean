import GoLean.GoCore.RelationalStorePath

/-! While-loop control views. The entry is one real admitted step, so clients
can use it for guarded recursion. Invariants and body safety are not premises
of these control laws and remain separate obligations of the client. -/
namespace GoLean.GoCore.Relational
open Machine

/-- Guard and body continuations, with control paths for normal completion
and unlabelled continue/break/return. No safety requirement is imposed on the
body or the final tail. This does not claim labelled exits or cleanup laws. -/
structure WhileControl (ctx : ProgramCtx) (guard : Expr) (body : Stmt)
    (env : LocalEnv) (k : Continuation) where
  test : Continuation
  next : Continuation
  admission : StepAdmission (.exec (.while guard body) env k.toMachine)
  enter : ∀ s, Pure ctx (statement (.while guard body) env k s) (expression guard env test s)
  select : ∀ b : Bool, StorePath ctx (fun _ => True) (.retV (.bool b) test.toMachine)
    (if b then .exec body env next.toMachine else .next k.toMachine)
  repeatPath : StorePath ctx (fun _ => True) (.next next.toMachine) (.exec (.while guard body) env k.toMachine)
  continuePath : StorePath ctx (fun _ => True) (.signal .cont next.toMachine) (.exec (.while guard body) env k.toMachine)
  breakPath : StorePath ctx (fun _ => True) (.signal .brk next.toMachine) (.next k.toMachine)
  returnPath : StorePath ctx (fun _ => True) (.signal .ret next.toMachine) (.signal .ret k.toMachine)

/-- Semantic while boundaries, independent of any loop invariant or fixture. -/
def while_control (ctx : ProgramCtx) (guard : Expr) (body : Stmt) (env : LocalEnv)
    (k : Continuation) : WhileControl ctx guard body env k := by
  refine { test := ⟨.whileK guard body env k.toMachine⟩
           next := ⟨.loop guard body env k.toMachine⟩
           admission := ⟨(by intro h; cases h), rfl⟩
           enter := fun _ => ⟨Step.whileStmt, rfl⟩
           select := ?_
           repeatPath := StorePath.pure (fun _ => ⟨Step.loopNext, rfl⟩) ⟨(by intro h; cases h), rfl⟩
           continuePath := StorePath.pure (fun _ => ⟨Step.signal rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩
           breakPath := StorePath.pure (fun _ => ⟨Step.signal rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩
           returnPath := StorePath.pure (fun _ => ⟨Step.signal rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩ }
  intro b
  cases b
  · exact StorePath.pure (fun _ => ⟨Step.whileFalse, rfl⟩) ⟨(by intro h; cases h), rfl⟩
  · exact StorePath.pure (fun _ => ⟨Step.whileTrue, rfl⟩) ⟨(by intro h; cases h), rfl⟩

end GoLean.GoCore.Relational
