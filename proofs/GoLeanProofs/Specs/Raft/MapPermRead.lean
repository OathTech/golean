import GoLeanProofs.MapPerm
import GoLeanProofs.Specs.Raft.AbsTwinCheckerRead

/-!
# The (M) carrier's decode transports (target-side half)

Split out of `MapPerm.lean` at the triage landing (2026-08-27): these
two lemmas are stated over the raft reader module's decoders
(`mapPairs`/`mapPairsD`, `Specs/Raft/AbsTwinCheckerRead.lean`), so
they live target-side — the import-direction lint (general proof
modules import no `Specs/*`) flagged the old placement, which the
triage plan had already recorded as an altitude smell. The namespace
stays `GoLean.MapPerm` so the family reads as one carrier (pins:
`Audit/Landing.lean`); revisit the placement when G-MAPITER restates
the law.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam (mapPairs mapPairsD)

namespace GoLean.MapPerm

/-- The decode transport (pure-decoder side): reading a PERMUTED
`mapData` entry list decodes to a permutation of the original decode
— fail-closed arms preserved (a permutation decodes iff the original
does). -/
theorem mapPairs_perm {κ ν : Type}
    {dk : GoValue → Option κ} {dv : GoValue → Option ν} :
    ∀ {es es' : List (GoValue × GoValue)}, List.Perm es es' →
    ∀ {xs : List (κ × ν)}, mapPairs dk dv es = some xs →
    ∃ xs', mapPairs dk dv es' = some xs' ∧ List.Perm xs xs' := by
  intro es es' hperm
  induction hperm with
  | nil =>
      intro xs h
      exact ⟨xs, h, List.Perm.refl _⟩
  | cons p _ ih =>
      intro xs h
      obtain ⟨kg, vg⟩ := p
      simp only [mapPairs, Option.bind_eq_bind] at h ⊢
      obtain ⟨k', hk', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest', hrest', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest'', hrest'', hpr⟩ := ih hrest'
      injection h with h
      subst h
      exact ⟨(k', v') :: rest'',
        by simp [hk', hv', hrest''], hpr.cons _⟩
  | swap p q t =>
      intro xs h
      obtain ⟨kp, vp⟩ := p
      obtain ⟨kq, vq⟩ := q
      simp only [mapPairs, Option.bind_eq_bind] at h ⊢
      obtain ⟨kq', hkq', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vq', hvq', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨kp', hkp', hrest2⟩ := Option.bind_eq_some_iff.mp hrest
      obtain ⟨vp', hvp', hrest3⟩ := Option.bind_eq_some_iff.mp hrest2
      obtain ⟨tail, htail, hrest4⟩ := Option.bind_eq_some_iff.mp hrest3
      injection hrest4 with hrest4
      injection h with h
      subst hrest4
      subst h
      refine ⟨(kp', vp') :: (kq', vq') :: tail, ?_, List.Perm.swap _ _ _⟩
      simp [hkp', hvp', hkq', hvq', htail]
  | trans _ _ ih₁ ih₂ =>
      intro xs h
      obtain ⟨xs₁, h₁, hp₁⟩ := ih₁ h
      obtain ⟨xs₂, h₂, hp₂⟩ := ih₂ h₁
      exact ⟨xs₂, h₂, hp₁.trans hp₂⟩

/-- The decode transport, σ-dependent-decoder side (`mapReadD`'s
walk). -/
theorem mapPairsD_perm {κ ν : Type} {σ : ExecState}
    {dk : GoValue → Option κ} {dv : ExecState → GoValue → Option ν} :
    ∀ {es es' : List (GoValue × GoValue)}, List.Perm es es' →
    ∀ {xs : List (κ × ν)}, mapPairsD σ dk dv es = some xs →
    ∃ xs', mapPairsD σ dk dv es' = some xs' ∧ List.Perm xs xs' := by
  intro es es' hperm
  induction hperm with
  | nil =>
      intro xs h
      exact ⟨xs, h, List.Perm.refl _⟩
  | cons p _ ih =>
      intro xs h
      obtain ⟨kg, vg⟩ := p
      simp only [mapPairsD, Option.bind_eq_bind] at h ⊢
      obtain ⟨k', hk', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest', hrest', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest'', hrest'', hpr⟩ := ih hrest'
      injection h with h
      subst h
      exact ⟨(k', v') :: rest'',
        by simp [hk', hv', hrest''], hpr.cons _⟩
  | swap p q t =>
      intro xs h
      obtain ⟨kp, vp⟩ := p
      obtain ⟨kq, vq⟩ := q
      simp only [mapPairsD, Option.bind_eq_bind] at h ⊢
      obtain ⟨kq', hkq', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vq', hvq', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨kp', hkp', hrest2⟩ := Option.bind_eq_some_iff.mp hrest
      obtain ⟨vp', hvp', hrest3⟩ := Option.bind_eq_some_iff.mp hrest2
      obtain ⟨tail, htail, hrest4⟩ := Option.bind_eq_some_iff.mp hrest3
      injection hrest4 with hrest4
      injection h with h
      subst hrest4
      subst h
      refine ⟨(kp', vp') :: (kq', vq') :: tail, ?_, List.Perm.swap _ _ _⟩
      simp [hkp', hvp', hkq', hvq', htail]
  | trans _ _ ih₁ ih₂ =>
      intro xs h
      obtain ⟨xs₁, h₁, hp₁⟩ := ih₁ h
      obtain ⟨xs₂, h₂, hp₂⟩ := ih₂ h₁
      exact ⟨xs₂, h₂, hp₁.trans hp₂⟩

end GoLean.MapPerm
