import RD8Acceptance
import U1RD8.Simulation

/-! Private joint acceptance for frozen RD8. No public export imports this
module. Policies constrain traversed sources, never the arbitrary final tail. -/
namespace I2
open GoLean GoCore GoCore.Machine GoCore.Relational GoCore.Relational.Unseq
open GoLean.Logic RelationalCodeX.Sweep

def boundaryObserver : Observation BoundaryEvent where
  designated := fun _ => true
  atCall := fun f args s => [.entry ⟨f, args, s⟩]
  atReturn := fun f vs s => [.returned ⟨f, vs, s⟩]

theorem reflects (es : List BoundaryEvent) :
    es.flatMap (O1Compatibility.observe boundaryObserver) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.flatMap_cons, ih]
    cases e <;> rfl

def EventQuiet (ctx : ProgramCtx) (c : Config) : Prop :=
  ∀ s, Boundary.events ctx ⟨c, s⟩ = []

/-- The frozen universal policy is exactly silence of the public event list,
including payloads and pre-stores, rather than silence for Observer.none. -/
theorem quiet_iff {ctx c} : Quiet ctx c ↔ EventQuiet ctx c := by
  constructor
  · intro h s
    have eq := h boundaryObserver s []
    rw [← O1Compatibility.emit_projection] at eq
    exact (reflects _).symm.trans eq
  · intro h Ev O s ch
    rw [← O1Compatibility.emit_projection]
    simp [Boundary.project, h s]

theorem path_policy {ctx fact c d}
    (path : StorePathFor ctx fact (Quiet ctx) c d) :
    StorePathFor ctx fact (EventQuiet ctx) c d := by
  induction path with
  | refl => exact .refl
  | step ht ha hq _ ih => exact .step ht ha (quiet_iff.mp hq) ih

theorem traversal_policy {ctx g env fact head value st}
    (tree : Traversal ctx g env fact (Quiet ctx) head value st) :
    Traversal ctx g env fact (EventQuiet ctx) head value st := by
  induction tree with
  | done binary settled => exact .done binary settled
  | next binary pending ready paths _ ih =>
    exact .next binary pending ready (fun i hi k => path_policy (paths i hi k)) ih

/-- Consume the existing operation-derived read/read/add paths, unchanged. -/
theorem source_paths (ctx : ProgramCtx) (env : LocalEnv) (p q base : Nat) (x y : Input)
    (h0 : env.lookup 0 = some (.base ⟨p⟩)) (h1 : env.lookup 1 = some (.base ⟨q⟩))
    (st : List UnseqStatus) (i : Nat) (ready : i ∈ graph.ready st) :
    ReadOnlyExprFor ctx (Facts (U1RD8.rows p q base x y st)) (EventQuiet ctx)
      (U1RD8.scope env base) (U1RD8.head i) (val (U1RD8.result x y i)) :=
  fun k => path_policy (U1RD8.paths ctx env p q base x y h0 h1 st i ready k)

theorem source_traversal (ctx : ProgramCtx) (env : LocalEnv) (p q base : Nat) (x y : Input)
    (h0 : env.lookup 0 = some (.base ⟨p⟩)) (h1 : env.lookup 1 = some (.base ⟨q⟩)) :
    Traversal ctx graph (U1RD8.scope env base)
      (fun st => Facts (U1RD8.rows p q base x y st)) (EventQuiet ctx)
      U1RD8.head (fun i => val (U1RD8.result x y i)) graph.initStatus :=
  traversal_policy (U1RD8.traversal ctx env p q base x y h0 h1)

/-- Every non-final residual plan supplies the same public-event policy,
including scheduler, binder write, allocation and completion/glue sources.
This imposes no condition on the final continuation or unrelated transitions. -/
theorem plan_source {ctx finish post c rows}
    (plan : Plan ctx finish post c rows) (before : c ≠ finish) : EventQuiet ctx c := by
  induction plan with
  | done => exact False.elim (before rfl)
  | reorder _ _ ih => exact ih before
  | choose _ quiet _ _ _ => exact quiet_iff.mp quiet
  | write quiet _ _ _ _ => exact quiet_iff.mp quiet
  | @allocate c rows cs next admitted quiet step plans ih => exact quiet_iff.mp quiet

theorem projected_source {ctx finish post c rows}
    (plan : Plan ctx finish post c rows) (before : c ≠ finish)
    {Ev : Type} (O : Observation Ev) (s : Store) (l : StepLabel) (b : State) :
    (RD8Acceptance.events ctx ⟨c,s⟩ l b).flatMap
      (RelationalCodeX.Observed.project O) = [] := by
  simp [RD8Acceptance.events, plan_source plan before s]

-- Both exact consumers coexist in one environment. No law premise is added.
theorem agreement : RelationalCodeX.Observed.EventAgreement RD8Acceptance.events :=
  RD8Acceptance.agreement
theorem simulation : SimulationLaw := U1RD8.simulation
theorem guarded : GuardedTarget := U1RD8.closed_guarded

#print axioms quiet_iff
#print axioms source_paths
#print axioms source_traversal
#print axioms plan_source
#print axioms projected_source
#print axioms agreement
#print axioms simulation
#print axioms guarded
#print axioms RD8Acceptance.prefix_history
#print axioms RD8Acceptance.guarded
end I2
