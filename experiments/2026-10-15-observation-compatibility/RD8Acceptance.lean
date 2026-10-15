import O1Compatibility
import RelationalCodeX.ObservedLifting
import RelationalCodeX.ObservationAcceptance

/-! Exact adapters to frozen logic RD8 5e8ed98. Semantic event completeness
is supplied independently by Transition.boundary_cases and the depth iff laws. -/
namespace RD8Acceptance
open GoLean GoCore GoCore.Machine GoCore.Relational GoLean.Logic
open RelationalCodeX.Observed

def adapt : BoundaryEvent → Event
  | .entry e => .inl e
  | .returned e => .inr e

def events : Events := fun ctx a _ _ => (Boundary.events ctx a).map adapt

theorem agreement : EventAgreement events := by
  intro ctx a b l _ Ev O ch
  rw [← O1Compatibility.emit_projection ctx O a.store a.control ch]
  simp only [Boundary.project, events, List.flatMap_map]
  congr 1
  funext e
  cases e <;> rfl

theorem prefix_history {ctx : ProgramCtx} {Ev : Type} (O : Observation Ev)
    {n : Nat} {s t : Store} {c d : Config} {ch tail : Choices} {ls : List StepLabel}
    (hp : ExecutionStatement.Prefix ctx n s c ch ls t d tail) :
    ∃ es, RelationalCodeX.Observed.History events ctx ⟨c, s⟩ ls ⟨d, t⟩ es ∧
      Safe.Obs ctx O s c ch ls = es.flatMap (project O) :=
  prefix_acceptance events agreement O hp

open GoLean.IrisCustomer Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
noncomputable section

-- Verbatim LiftingTarget body, with only its semantic law parameter supplied.
theorem guarded :
  ∀ (ctx : ProgramCtx)
    (GF : BundledGFunctors) (O : Observer) [GoGSO GF O]
    (md : Safe.Index) (E : CoPset) (Φ : Safe.Outcome → IProp GF)
    (c : Config) (R : IProp GF) (fact : Store → Prop)
    (post : (s : Store) → fact s → Store) (next : Store → Config) (Ψ : Store → IProp GF)
    (h evs : List O.Ev),
    (∀ s, iprop(heapInterp ctx s ∗ R) ⊢ iprop(⌜fact s⌝ ∗ heapInterp ctx s ∗ R)) →
    (∀ s (hf : fact s), iprop(heapInterp ctx s ∗ R) ⊢ |==> (heapInterp ctx (post s hf) ∗ Ψ s)) →
    (∀ s (hf : fact s), ∃ l,
      Transition ctx ⟨c, s⟩ l ⟨next s, post s hf⟩ ∧ l.picks = [] ∧
      (events ctx ⟨c, s⟩ l ⟨next s, post s hf⟩).flatMap (project O.obs) = evs) →
    c ≠ .next .stop → md.Admits c →
    (∀ s (hf : fact s), s.heap.size ≤ (post s hf).heap.size) → O.Inv (h ++ evs) →
    iprop(GoLean.Logic.History.frag h ∗ R ∗ ▷ (∀ s, ⌜fact s⌝ -∗ Ψ s -∗ GoLean.Logic.History.frag (h ++ evs) -∗
      WP (Safe.ExprAt.run (ctx := ctx) (O := O) (m := md) (next s))
        @ Stuckness.NotStuck; E {{ Φ }})) ⊢
      WP (Safe.ExprAt.run (ctx := ctx) (O := O) (m := md) c)
        @ Stuckness.NotStuck; E {{ Φ }} :=
  observed_step events agreement

#print axioms agreement
#print axioms prefix_history
#print axioms guarded
#print axioms GoLean.Logic.ProgramExecution.original_closed_program_prefix
#print axioms GoLean.Logic.ProgramExecution.original_closed_program_outcomes_hist
end
end RD8Acceptance
