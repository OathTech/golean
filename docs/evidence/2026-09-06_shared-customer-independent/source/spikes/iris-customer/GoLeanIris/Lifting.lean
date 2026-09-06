import GoLeanIris.Ghost

/-! Reusable lifting over actual machine steps. Full ownership is required
for a write; reads preserve arbitrary fractions. Continuations are explicit
parameters, so these rules do not assume recovery is context-insensitive. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

theorem step_unique {c c' : Config} {state state' : ExecState}
    (h : ∀ choices, stepFn state c choices = .ok (c', state', choices))
    {next : Config} {final : ExecState} (hs : Step c state next final) :
    next = c' ∧ final = state' := by
  obtain ⟨ch, ch', he⟩ := step_complete hs
  rw [h] at he
  obtain ⟨hc, hp⟩ := Prod.mk.inj (Except.ok.inj he)
  obtain ⟨hstate, _⟩ := Prod.mk.inj hp
  exact ⟨hc.symm, hstate.symm⟩

section
variable {GF : BundledGFunctors} [GoGS GF]
variable {E : CoPset} {Φ : Unit → IProp GF}

theorem wp_context_step {c c' : Config}
    (hnv : ToVal.toVal c = (none : Option Unit))
    (hred : ∀ state, ContextEq state (GoGS.context GF) →
      ∀ choices, stepFn state c choices = .ok (c', state, choices)) :
    (▷ WP c' @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step hnv
  iintro %state %ns %obs %obs' %nt Hstate
  simp only [stateInterp]
  icases Hstate with ⟨Hheap, %Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], c', state, [], GateA1.Customer.Prim.step (stepFn_sound (hred state Hctx []))⟩
  inext
  iintro %next %final %forks %hs _
  cases hs with
  | step st =>
    obtain ⟨rfl, rfl⟩ := step_unique (hred state Hctx) st
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · isplitl [Hheap]
      · iexact Hheap
      · ipureintro; exact Hctx
    · isplitl [Hcont]
      · iexact Hcont
      · itrivial

theorem wp_read_step {a : Nat} {cell : HeapCell} {dq : DFrac} {c c' : Config}
    (hnv : ToVal.toVal c = (none : Option Unit))
    (hred : ∀ state, ContextEq state (GoGS.context GF) → state.heap[a]? = some cell →
      ∀ choices, stepFn state c choices = .ok (c', state, choices)) :
    (a ↦{dq} cell ∗ ▷ (a ↦{dq} cell -∗ WP c' @ Stuckness.NotStuck; E {{ Φ }})) ⊢
      WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step hnv
  iintro %state %ns %obs %obs' %nt Hstate
  simp only [stateInterp]
  icases Hstate with ⟨Hheap, %Hctx⟩
  ihave %Hlookup : ⌜get? (heapToMap state.heap) a = some cell⌝ $$ [Hheap Hpt]
  · icases genHeap_valid $$ [$Hheap $Hpt] with >%h
    itrivial
  rw [get?_heapToMap] at Hlookup
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], c', state, [], GateA1.Customer.Prim.step (stepFn_sound (hred state Hctx Hlookup []))⟩
  inext
  iintro %next %final %forks %hs _
  cases hs with
  | step st =>
    obtain ⟨rfl, rfl⟩ := step_unique (hred state Hctx Hlookup) st
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · isplitl [Hheap]
      · iexact Hheap
      · ipureintro; exact Hctx
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ Hpt
      · itrivial

theorem wp_write_step {a : Nat} {old new : HeapCell} {c c' : Config}
    (hnv : ToVal.toVal c = (none : Option Unit))
    (hred : ∀ state, ContextEq state (GoGS.context GF) →
      (hlook : state.heap[a]? = some old) → ∀ choices,
      stepFn state c choices = .ok
        (c', {state with heap := state.heap.set a new (Array.getElem?_eq_some_iff.mp hlook).1}, choices)) :
    (a ↦ old ∗ ▷ (a ↦ new -∗ WP c' @ Stuckness.NotStuck; E {{ Φ }})) ⊢
      WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step hnv
  iintro %state %ns %obs %obs' %nt Hstate
  simp only [stateInterp]
  icases Hstate with ⟨Hheap, %Hctx⟩
  ihave %Hlookup : ⌜get? (heapToMap state.heap) a = some old⌝ $$ [Hheap Hpt]
  · icases genHeap_valid $$ [$Hheap $Hpt] with >%h
    itrivial
  rw [get?_heapToMap] at Hlookup
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], c', _, [], GateA1.Customer.Prim.step (stepFn_sound (hred state Hctx Hlookup []))⟩
  inext
  iintro %next %final %forks %hs _
  cases hs with
  | step st =>
    obtain ⟨rfl, rfl⟩ := step_unique (hred state Hctx Hlookup) st
    imod (genHeap_update (v₂ := new)) $$ [$Hheap $Hpt] with ⟨Hheap, Hpt⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · isplitl [Hheap]
      · iapply (genHeapInterp_eqv (fun k => (heapToMap_set state.heap a new _ k).symm)) $$ Hheap
      · ipureintro; exact Hctx.heap _
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ Hpt
      · itrivial

theorem wp_alloc_step {cell : HeapCell} {c : Config} (next : Nat → Config)
    (hnv : ToVal.toVal c = (none : Option Unit))
    (hred : ∀ state, ContextEq state (GoGS.context GF) → ∀ choices,
      stepFn state c choices = .ok
        (next state.heap.size, {state with heap := state.heap.push cell}, choices)) :
    (▷ ∀ a : Nat, a ↦ cell -∗ WP (next a) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step hnv
  iintro %state %ns %obs %obs' %nt Hstate
  simp only [stateInterp]
  icases Hstate with ⟨Hheap, %Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], next state.heap.size, _, [],
      GateA1.Customer.Prim.step (stepFn_sound (hred state Hctx []))⟩
  inext
  iintro %next' %final %forks %hs _
  cases hs with
  | step st =>
    obtain ⟨rfl, rfl⟩ := step_unique (hred state Hctx) st
    imod (genHeap_alloc (v := cell) (heapToMap_fresh state.heap)) $$ Hheap
      with ⟨Hheap, Hpt, _⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · isplitl [Hheap]
      · iapply (genHeapInterp_eqv (fun k => (heapToMap_push state.heap cell k).symm)) $$ Hheap
      · ipureintro; exact Hctx.heap _
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %state.heap.size Hpt
      · itrivial

end
end GoLean.IrisCustomer
