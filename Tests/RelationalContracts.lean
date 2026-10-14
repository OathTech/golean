import GoLean.Relational

/-! Symbolic semantic clients. These compose construct laws without matching
machine frames or unfolding an evaluator; they are not Iris program proofs.
The allocation regression checks the distinction between silence and purity.
-/

namespace Tests.RelationalContracts

open GoLean GoLean.GoCore GoLean.GoCore.Relational

theorem literal_conditional (ctx : ProgramCtx) (b : Bool) (yes no : Stmt)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    Run ctx (statement (.ifThenElse (.boolLit b) yes no) env k s)
      [⟨[], [], []⟩, ⟨[], [], []⟩, ⟨[], [], []⟩]
      (statement (if b then yes else no) env k s) :=
  conditional (.single (bool_literal ctx b env (branch yes no env k) s).1)

theorem literal_conditional_realizable (ctx : ProgramCtx) (b : Bool) (yes no : Stmt)
    (env : LocalEnv) (k : Continuation) (s : Store) :
    ∃ ch, ExecutionStatement.Prefix ctx 3 s
      (statement (.ifThenElse (.boolLit b) yes no) env k s).control ch
      [⟨[], [], []⟩, ⟨[], [], []⟩, ⟨[], [], []⟩] s
      (statement (if b then yes else no) env k s).control [] :=
  (literal_conditional ctx b yes no env k s).realize []

theorem allocating_silence_is_not_pure {ctx : ProgramCtx} {decls : Array Param}
    {ss : Array Stmt} {env env' : LocalEnv} {k : Continuation} {s t : Store}
    (h : Machine.allocDecls ctx env.pushScope s decls.toList = .ok (env', t))
    (nonempty : 0 < decls.size) :
    Transition ctx (statement (.block decls ss) env k s) ⟨[], [], []⟩
      (resumed (sequence ss.toList env' k) t) ∧
    ¬ Pure ctx (statement (.block decls ss) env k s) (resumed (sequence ss.toList env' k) t) := by
  have hc := block_enter (ss := ss) (k := k) h
  refine ⟨hc.1, ?_⟩
  intro hp
  have he : t = s := hp.2
  have hs := hc.2.1
  rw [he] at hs
  omega

-- Headline exports: the existing audit also checks every imported declaration.
#print axioms Run.realize
#print axioms Transition.deterministic_by_picks
#print axioms Run.deterministic_by_picks
#print axioms PickFreeProgress.run
#print axioms Completed.realize
#print axioms panic_run_iff
#print axioms deadlock_run_iff
#print axioms exhaustion_iff
#print axioms Completed.rendering_refusal
#print axioms LocalEntry.layout
#print axioms local_normal_iff
#print axioms Initializes.realize
#print axioms initializes_of_run
#print axioms init_print_at_zero
#print axioms ProgramNormal.realize
#print axioms program_normal_of_run
#print axioms Enters.transition
#print axioms root_writes_commute
#print axioms read_variable
#print axioms sequence_splice
#print axioms assign_pointer_variables

#print axioms reference
#print axioms assign_variable
#print axioms return_start
#print axioms return_sequence
#print axioms SavedCaller.enter
#print axioms LocalEntry.resultSlots
#print axioms Readback.traced
#print axioms CallBoundary.deliver
#print axioms SavedCaller.invoke

#print axioms StorePath.run
#print axioms StorePath.trans
#print axioms StorePath.weaken
#print axioms OperandPaths.values
#print axioms pointer_assignment_phases
#print axioms variable_assignment_phases
#print axioms SavedCaller.entry_phases

end Tests.RelationalContracts
