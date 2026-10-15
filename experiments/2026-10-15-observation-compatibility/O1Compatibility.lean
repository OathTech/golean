import GoLean.Relational
import RelationalCodeX.AdequacyFrozen

namespace O1Compatibility
open GoLean GoCore GoCore.Machine GoCore.Relational GoLean.Logic GoLean.IrisCustomer
open GoCore.ExecutionStatement

theorem sites {fid args c frame} : EntrySite fid args c frame ↔ CallSite fid args c frame := by
  constructor
  · intro h
    cases h with
    | @direct targets args plans env k hp ha =>
      have hn : args = #[] := by simpa using ha
      subst args
      exact .direct hp
    | arguments => exact .arguments
    | closure => exact .closure
    | closureArguments => exact .closureArguments
    | deferFall => exact .deferFall
    | deferReturn => exact .deferReturn
    | deferPanic => exact .deferPanic
  · intro h
    cases h with
    | direct hp => exact .direct hp rfl
    | arguments => exact .arguments
    | closure => exact .closure
    | closureArguments => exact .closureArguments
    | deferFall => exact .deferFall
    | deferReturn => exact .deferReturn
    | deferPanic => exact .deferPanic

theorem table {fid args c frame} (h : EntrySite fid args c frame) : callEntry? c = some (fid, args) := by
  cases h <;> simp_all [callEntry?, entryCallSite?]

open Classical in
theorem candidate (c : Config) : Boundary.invocation? c =
    (match callEntry? c with
    | some (fid, args) => if ∃ frame, CallSite fid args c frame then some (fid, args) else none
    | none => none) := by
  cases hc : callEntry? c with
  | none =>
    cases hi : Boundary.invocation? c with
    | none => rfl
    | some pair =>
      obtain ⟨fid, args⟩ := pair
      obtain ⟨frame, site⟩ := Boundary.invocation?_iff.mp hi
      have ht := table site
      rw [hc] at ht
      cases ht
  | some pair =>
    obtain ⟨fid, args⟩ := pair
    by_cases hs : ∃ frame, CallSite fid args c frame
    · obtain ⟨frame, site⟩ := hs
      rw [Boundary.invocation?_iff.mpr ⟨frame, sites.mpr site⟩]
      simp [show ∃ frame, CallSite fid args c frame from ⟨frame, site⟩]
    · simp only [if_neg hs]
      cases hi : Boundary.invocation? c with
      | none => rfl
      | some pair =>
        obtain ⟨fid', args'⟩ := pair
        obtain ⟨frame, site⟩ := Boundary.invocation?_iff.mp hi
        have ht := table site
        rw [hc] at ht
        cases ht
        exact (hs ⟨frame, sites.mp site⟩).elim

def observe {Ev : Type} (O : Observation Ev) : BoundaryEvent → List Ev
  | .entry e => if O.designated e.function then O.atCall e.function e.supplied e.before else []
  | .returned e => if O.designated e.function then O.atReturn e.function e.values e.before else []

theorem entry_projection {Ev : Type} (ctx : ProgramCtx) (O : Observation Ev) (s : Store) (c : Config) (ch : Choices) :
    ((Boundary.entry? ctx ⟨c,s⟩).toList.map BoundaryEvent.entry).flatMap (observe O) = entryEvents ctx O s c ch := by
  classical
  unfold Boundary.entry? entryEvents
  rw [candidate]
  cases hc : callEntry? c with
  | none => rfl
  | some pair =>
    obtain ⟨fid, args⟩ := pair
    by_cases hs : ∃ frame, CallSite fid args c frame
    · simp only [if_pos hs]
      dsimp only [Bind.bind, Option.bind]
      unfold entered?
      split <;> simp_all [observe]
    · simp [hs]

theorem return_projection {Ev : Type} (ctx : ProgramCtx) (O : Observation Ev) (s : Store) (c : Config) :
    ((Boundary.return? ctx ⟨c,s⟩).toList.map BoundaryEvent.returned).flatMap (observe O) = returnEvents ctx O s c := by
  unfold Boundary.return? returnEvents returnSite?
  split
  · rename_i plans env roots fid k hc
    change c = _ at hc
    subst c
    change ((exitValues ctx s plans roots k).map _ |>.toList.map BoundaryEvent.returned).flatMap (observe O) = _
    cases hv : exitValues ctx s plans roots k <;> simp [hv, observe]
  · rename_i plans env roots fid k hc
    change c = _ at hc
    subst c
    change ((exitValues ctx s plans roots k).map _ |>.toList.map BoundaryEvent.returned).flatMap (observe O) = _
    cases hv : exitValues ctx s plans roots k <;> simp [hv, observe]
  · split <;> simp_all

/-- All-state equality of projections does not assert that a failed attempt
executes an event. The history theorem requires the actual prefix. -/
theorem emit_projection {Ev : Type} (ctx : ProgramCtx) (O : Observation Ev) (s : Store) (c : Config) (ch : Choices) :
    Boundary.project (observe O) ctx ⟨c,s⟩ = emit ctx O s c ch := by
  simp only [Boundary.project, Boundary.events, List.flatMap_append, emit,
    entry_projection ctx O s c ch, return_projection ctx O s c]

theorem history {Ev : Type} {ctx : ProgramCtx} (O : Observation Ev) {n s c ch ls sf cf chf}
    (h : Prefix ctx n s c ch ls sf cf chf) :
    Boundary.History (observe O) ctx ⟨c,s⟩ ls (Safe.Obs ctx O s c ch ls) ⟨cf,sf⟩ := by
  induction h with
  | done => exact .refl
  | step hs _ ih =>
    rw [Safe.obs_step hs, ← emit_projection]
    exact .cons (stepFn_sound hs) ih

#print axioms emit_projection
#print axioms history
end O1Compatibility
