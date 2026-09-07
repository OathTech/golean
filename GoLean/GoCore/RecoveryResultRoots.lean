import GoLean.GoCore.RecoveryAllocation

/-! Typed result locations and actual result pinning/readout. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

inductive ResultRoots (world : World) : List Param → List Loc → Prop
  | nil : ResultRoots world [] []
  | cons {p ps loc locs} : AddressAt world p.typ loc → ResultRoots world ps locs →
      ResultRoots world (p :: ps) (loc :: locs)

theorem ResultRoots.length {world ps locs} (h : ResultRoots world ps locs) :
    ps.length = locs.length := by
  induction h <;> simp_all

theorem ResultRoots.mono {world next ps locs} (h : ResultRoots world ps locs)
    (ext : Extends world next) : ResultRoots next ps locs := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (ha.mono ext) ih

theorem ResultRoots.load {world s ps locs} (h : ResultRoots world ps locs)
    (heap : HeapTyped world s) :
    ∃ vs, loadMany s locs = .ok vs ∧ ParamsValues world ps vs := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons ha _ ih =>
    obtain ⟨sort, ht, hl⟩ := ha
    obtain ⟨v, hv, hvtype⟩ := heap.load hl
    obtain ⟨vs, hvs, htypes⟩ := ih
    exact ⟨v :: vs, by simp [loadMany, hv, hvs, Bind.bind, Except.bind,
      Pure.pure, Except.pure],
      .cons ⟨sort, ht, hvtype⟩ htypes⟩

theorem pinResultLocs_typed (ps : List Param) {world env}
    (h : ∀ p ∈ ps, ∃ loc, env.lookup p.id = some loc ∧ AddressAt world p.typ loc) :
    ∃ locs, pinResultLocs env ps = .ok locs ∧ ResultRoots world ps locs := by
  induction ps with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons p ps ih =>
    obtain ⟨loc, hl, ht⟩ := h p (by simp)
    obtain ⟨locs, hls, hts⟩ := ih (fun q hq => h q (by simp [hq]))
    exact ⟨loc :: locs, by simp [pinResultLocs, hl, hls, Bind.bind, Except.bind,
      Pure.pure, Except.pure],
      .cons ht hts⟩

end GoLean.GoCore.RecoveryRuntime
