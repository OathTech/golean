import GoLean.GoCore.RelationalUnseqCanonical

namespace GoLean.GoCore.Relational.Unseq
open Machine

/-- Allocation is a separate visible step. Subsequent steps preserve the
post-allocation heap domain. No heap equality across allocation is asserted. -/
def Domain.EntryFrame {ctx g env} (d : Domain ctx g env) (source : State)
    (a : State) (l : StepLabel) (b : State) : Prop :=
  (a = source ∧ d.MemInvariant b) ∨ d.FrameStep a l b

theorem Domain.enter {ctx g env} (d : Domain ctx g env)
    {oldEnv s allocated} (wf : g.wellFormed? = none)
    (entry : unseqEntryCheck? g oldEnv = none)
    (alloc : allocDecls ctx oldEnv.pushScope s g.cells = .ok (env, allocated))
    (heap : d.heap.At g.initStatus allocated)
    (body : Stmt) (rest : List Stmt) (k : Continuation) :
    let source : State := ⟨.exec (.unseq g body) oldEnv (.seq rest oldEnv k.toMachine), s⟩
    SafeUntil ctx (d.EntryFrame source) (Completed d body ⟨.seq rest oldEnv k.toMachine⟩) source := by
  dsimp only
  refine SafeUntil.deterministic_step (l := ⟨[], [], []⟩)
    (b := atPick g body g.initStatus env ⟨.seq rest oldEnv k.toMachine⟩ allocated)
    ⟨(by intro h; cases h), rfl⟩ (Step.unseqEnter wf entry alloc) rfl
    (Or.inl ⟨rfl, _, binary_initial g, heap⟩) ?_
  exact (d.all_schedules body ⟨.seq rest oldEnv k.toMachine⟩ _ (binary_initial g) _ heap).weaken
    (fun _ _ _ h => Or.inr h)

theorem Domain.canonical_entry {ctx g env} (d : Domain ctx g env)
    {oldEnv s allocated} (wf : g.wellFormed? = none)
    (entry : unseqEntryCheck? g oldEnv = none)
    (alloc : allocDecls ctx oldEnv.pushScope s g.cells = .ok (env, allocated))
    (heap : d.heap.At g.initStatus allocated)
    (body : Stmt) (rest : List Stmt) (k : Continuation) :
    ∃ order labels final,
      CanonicalExecution d body ⟨.seq rest oldEnv k.toMachine⟩ g.initStatus allocated order labels final ∧
      Run ctx ⟨.exec (.unseq g body) oldEnv (.seq rest oldEnv k.toMachine), s⟩
        (⟨[], [], []⟩ :: labels) final := by
  obtain ⟨order, labels, final, h⟩ :=
    d.canonical body ⟨.seq rest oldEnv k.toMachine⟩ _ (binary_initial g) _ heap
  exact ⟨order, labels, final, h,
    .cons (b := atPick g body g.initStatus env ⟨.seq rest oldEnv k.toMachine⟩ allocated)
      (Step.unseqEnter wf entry alloc) h.run⟩

end GoLean.GoCore.Relational.Unseq
