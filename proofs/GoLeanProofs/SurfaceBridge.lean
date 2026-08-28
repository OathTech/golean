import GoLeanProofs.Surface
import GoLeanProofs.Ghost

/-!
# The surface boundary (Layer B)

The two once-proven crossings between the native spec surface
(`GoLeanProofs/Surface.lean`, Iris-free) and the Iris internals
(`docs/2026-07-21_native-spec-surface.md` §3):

- **Reflection (precondition in)**: a `sat`-isfied heaplet's ownership
  big-op entails the embedded assertion — `reflect`.
- **Extraction (postcondition out)**: the embedded assertion plus the state
  interpretation yields the pure sub-heaplet `sat` fact — `extract`.

Both are by induction on `HProp` syntax; no per-program work ever happens
here. Also holds the kernel-checked agreements between the surface's plain
`Std.ExtTreeMap` operations and the Iris side's `PartialMap` typeclass
operations (`heapletOf_eq_heapToMap`, `heaplet_insert_eq`) — the surface
deliberately does not import even `Iris.Std`, so these live on this side.
-/

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris

/-! ## Map-operation agreements (surface `Std` API vs bridge `PartialMap` API)

`Heaplet` is definitionally `GoHeapF HeapCell`; the bridge states its lemmas
over `GoHeapF HeapCell` so the `PartialMap` functor argument infers, and the
surface's `Heaplet`-typed values flow in by that defeq. -/

/-- The surface's `ExtTreeMap.get?` IS the bridge's `PartialMap.get?`. -/
theorem heaplet_get?_eq (h : GoHeapF HeapCell) (k : Nat) :
    h.get? k = Std.PartialMap.get? (M := GoHeapF) h k := rfl

/-- The surface's `ExtTreeMap.insert` agrees with the bridge's
`PartialMap.insert` (which is `alter`-implemented) — extensionally, hence
by `ExtTreeMap`'s extensionality, equal. -/
theorem heaplet_insert_eq (h : GoHeapF HeapCell) (k : Nat) (c : HeapCell) :
    h.insert k c = Std.PartialMap.insert (M := GoHeapF) h k c := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  by_cases hk : k = k' <;>
    simp [Std.PartialMap.insert, hk, Std.ExtTreeMap.getElem?_alter,
      Std.ExtTreeMap.getElem?_insert]

/-- The surface heap projection IS the bridge heap projection. -/
theorem heapletOf_eq_heapToMap (h : Heap) : heapletOf h = heapToMap h := by
  unfold heapletOf heapToMap
  induction h with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldr_cons, ih]
    cases p.1 <;> simp [heaplet_insert_eq]

/-- Cover characterization of a disjoint union — the pure fact `sat`'s
`sep` case wants, both for reflection and extraction. -/
theorem union_cover {h₁ h₂ : GoHeapF HeapCell}
    (hdisj : ∀ k, h₁.get? k = none ∨ h₂.get? k = none) :
    ∀ (k : Nat) (c : HeapCell),
      (Std.PartialMap.union (M := GoHeapF) h₁ h₂).get? k = some c
      ↔ (h₁.get? k = some c ∨ h₂.get? k = some c) := by
  simp only [heaplet_get?_eq] at hdisj ⊢
  intro k c
  -- 4.32.2 pin move: upstream `get?_union` is now stated over `∪`
  -- (`Union.union`); go through `union = merge` (`@[simp] def`) and the
  -- `get?_merge` class field instead.
  simp only [Std.PartialMap.union]
  rw [LawfulPartialMap.get?_merge]
  rcases hdisj k with hn | hn <;> rw [hn] <;>
    cases hx : Std.PartialMap.get? (M := GoHeapF) h₁ k <;>
      cases hy : Std.PartialMap.get? (M := GoHeapF) h₂ k <;>
        simp_all [Option.merge]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-! ## The embedding and heaplet ownership -/

/-- Ownership of every cell of a heaplet. -/
def ownHeaplet (h : GoHeapF HeapCell) : IProp GF :=
  iprop([∗map] l ↦ c ∈ h, l ↦ c)

/-- The embedding `⟦·⟧ : HProp → IProp` — structural; the only place the
surface syntax meets Iris. -/
def embed : HProp → IProp GF
  | .emp => iprop(emp)
  | .pure φ => iprop(⌜φ⌝)
  | .pointsTo ℓ c => iprop(ℓ ↦ c)
  | .sep P Q => iprop(embed P ∗ embed Q)
  | .ex f => iprop(∃ a, embed (f a))

/-- Every embedded surface assertion is **timeless** — `HProp` is first-order
heap data (`emp`/pure/`↦`/`∗`/`∃`), so `▷ ⟦P⟧` collapses to `◇ ⟦P⟧`. This is
what lets the invariance readout strip the later that `inv`-opening puts on
the invariant body (arc `invariant-readout`); proven once by induction, like
every boundary crossing. -/
instance embed_timeless : (P : HProp) → BI.Timeless (embed (GF := GF) P)
  | .emp => by unfold embed; infer_instance
  | .pure φ => by unfold embed; infer_instance
  | .pointsTo ℓ c => by unfold embed; infer_instance
  | .sep P Q =>
      haveI := embed_timeless P
      haveI := embed_timeless Q
      by unfold embed; infer_instance
  | .ex f =>
      haveI : ∀ a, BI.Timeless (embed (GF := GF) (f a)) :=
        fun a => embed_timeless (f a)
      by unfold embed; infer_instance

/-! ## Ownership helpers -/

theorem ownHeaplet_empty {P : IProp GF} [Affine P] :
    P ⊢ ownHeaplet (GF := GF) (∅ : GoHeapF HeapCell) :=
  BigSepM.bigSepM_empty_intro

theorem ownHeaplet_singleton {ℓ : Nat} {c : HeapCell} :
    (iprop(ℓ ↦ c) : IProp GF) ⊢ ownHeaplet ((∅ : Heaplet).insert ℓ c) := by
  rw [heaplet_insert_eq]
  exact (BigSepM.bigSepM_singleton (PROP := IProp GF) (M := GoHeapF)
    (Φ := fun (l : Nat) (c : HeapCell) => iprop(l ↦ c)) (i := ℓ) (x := c)).2

/-- Two owned heaplets are provably disjoint: overlapping full-fraction
cells would compose to an invalid `DFrac`. This is what makes the native
`∗` honest — extraction reconstructs a genuine disjoint split, never an
approximation. -/
theorem ownHeaplet_lookup_False {h₁ h₂ : GoHeapF HeapCell} {k : Nat}
    {c₁ c₂ : HeapCell}
    (hk₁ : Std.PartialMap.get? (M := GoHeapF) h₁ k = some c₁)
    (hk₂ : Std.PartialMap.get? (M := GoHeapF) h₂ k = some c₂) :
    ownHeaplet (GF := GF) h₁ ∗ ownHeaplet h₂ ⊢ ⌜False⌝ := by
  unfold ownHeaplet
  iintro ⟨H₁, H₂⟩
  ihave Hc₁ := BigSepM.bigSepM_lookup
    (Φ := fun (l : Nat) (c : HeapCell) => iprop(l ↦ c)) hk₁ $$ H₁
  ihave Hc₂ := BigSepM.bigSepM_lookup
    (Φ := fun (l : Nat) (c : HeapCell) => iprop(l ↦ c)) hk₂ $$ H₂
  ihave %Hv := pointsTo_op_cmraValid $$ [$Hc₁ $Hc₂]
  exact absurd (DFrac.valid_op_own Hv.1) (by simp)

theorem ownHeaplet_disjoint {h₁ h₂ : GoHeapF HeapCell} :
    ownHeaplet (GF := GF) h₁ ∗ ownHeaplet h₂
      ⊢ ⌜∀ k, h₁.get? k = none ∨ h₂.get? k = none⌝ := by
  iintro H
  iapply (pure_forall (PROP := IProp GF)).2
  iintro %k
  cases hk₁ : Std.PartialMap.get? (M := GoHeapF) h₁ k with
  | none => ipureintro; exact .inl hk₁
  | some c₁ =>
    cases hk₂ : Std.PartialMap.get? (M := GoHeapF) h₂ k with
    | none => ipureintro; exact .inr hk₂
    | some c₂ =>
      ihave %Hf := ownHeaplet_lookup_False hk₁ hk₂ $$ H
      exact Hf.elim

/-- Disjoint-union split/join for heaplet ownership (`bigSepM_union`). -/
theorem ownHeaplet_union {h₁ h₂ : GoHeapF HeapCell}
    (hdisj : ∀ k, h₁.get? k = none ∨ h₂.get? k = none) :
    ownHeaplet (GF := GF) (Std.PartialMap.union (M := GoHeapF) h₁ h₂)
      ⊣⊢ ownHeaplet h₁ ∗ ownHeaplet h₂ := by
  have hdisj' : h₁ ##ₘ h₂ := (disjoint_iff h₁ h₂).mpr hdisj
  exact BigSepM.bigSepM_union hdisj'

/-- Any heaplet with `sat`'s disjoint-cover characterization IS the union,
extensionally — transport for the `sep` case of reflection. -/
theorem cover_equiv {h h₁ h₂ : GoHeapF HeapCell}
    (hdisj : ∀ k, h₁.get? k = none ∨ h₂.get? k = none)
    (hcover : ∀ k c, h.get? k = some c
      ↔ (h₁.get? k = some c ∨ h₂.get? k = some c)) :
    h ≡ₘ Std.PartialMap.union (M := GoHeapF) h₁ h₂ := by
  intro k
  cases hc : Std.PartialMap.get? (M := GoHeapF) h k with
  | some c =>
    exact ((union_cover hdisj k c).mpr ((hcover k c).mp hc)).symm
  | none =>
    cases hu : Std.PartialMap.get?
        (Std.PartialMap.union (M := GoHeapF) h₁ h₂) k with
    | some c =>
      have hsome := (hcover k c).mpr ((union_cover hdisj k c).mp hu)
      rw [heaplet_get?_eq] at hsome
      rw [hc] at hsome
      cases hsome
    | none => rfl

/-! ## Reflection: `sat` → embedding (the precondition crossing) -/

/-- **Reflection.** A heaplet satisfying `P` natively, all of whose cells we
own, entails `⟦P⟧`. Once-proven induction on `HProp`. -/
theorem reflect : ∀ (P : HProp) (h : Heaplet), sat h P →
    ownHeaplet (GF := GF) h ⊢ embed P
  | .emp, h, hsat => by
    simp only [embed]
    rw [show h = ∅ from hsat]
    exact BigSepM.bigSepM_empty.1
  | .pure φ, h, hsat => by
    simp only [embed]
    rw [show h = ∅ from hsat.2]
    exact BigSepM.bigSepM_empty.1.trans (pure_intro hsat.1)
  | .pointsTo ℓ c, h, hsat => by
    simp only [embed]
    rw [show h = (∅ : Heaplet).insert ℓ c from hsat]
    rw [ownHeaplet, heaplet_insert_eq]
    exact BigSepM.bigSepM_singleton.1
  | .sep P Q, h, hsat => by
    obtain ⟨h₁, h₂, hs₁, hs₂, hdisj, hcover⟩ := hsat
    simp only [embed]
    refine (BigSepM.bigSepM_eqv_of_perm (cover_equiv hdisj hcover)).1.trans ?_
    exact (ownHeaplet_union hdisj).1.trans
      (sep_mono (reflect P h₁ hs₁) (reflect Q h₂ hs₂))
  | .ex f, h, hsat => by
    obtain ⟨a, ha⟩ := hsat
    simp only [embed]
    exact (reflect (f a) h ha).trans (exists_intro (Ψ := fun a => embed (f a)) a)

/-! ## Extraction: embedding → `sat` (the postcondition crossing) -/

/-- Step 1 of extraction: every embedded assertion is equivalent to owning
the cells of SOME natively-satisfying heaplet. Once-proven induction on
`HProp`; the `sep` case reconstructs genuine disjointness from `DFrac`
validity (`ownHeaplet_disjoint`). -/
theorem embed_toHeaplet : ∀ (Q : HProp),
    embed (GF := GF) Q ⊢ ∃ h : Heaplet, ⌜sat h Q⌝ ∗ ownHeaplet h
  | .emp => by
    simp only [embed]
    iintro H
    iexists (∅ : Heaplet)
    isplitr
    · ipureintro; rfl
    · iapply ownHeaplet_empty $$ H
  | .pure φ => by
    simp only [embed]
    iintro %hφ
    iexists (∅ : Heaplet)
    isplitr
    · ipureintro; exact ⟨hφ, rfl⟩
    · iapply ownHeaplet_empty (P := iprop(emp))
      itrivial
  | .pointsTo ℓ c => by
    simp only [embed]
    iintro H
    iexists ((∅ : Heaplet).insert ℓ c)
    isplitr
    · ipureintro; rfl
    · iapply ownHeaplet_singleton $$ H
  | .sep P Q => by
    simp only [embed]
    iintro ⟨HP, HQ⟩
    icases (embed_toHeaplet P) $$ HP with ⟨%h₁, %hs₁, H₁⟩
    icases (embed_toHeaplet Q) $$ HQ with ⟨%h₂, %hs₂, H₂⟩
    ihave %hdisj := ownHeaplet_disjoint $$ [$H₁ $H₂]
    iexists (Std.PartialMap.union (M := GoHeapF) h₁ h₂)
    isplitr
    · ipureintro
      exact ⟨h₁, h₂, hs₁, hs₂, hdisj, union_cover hdisj⟩
    · iapply (ownHeaplet_union hdisj).2 $$ [$H₁ $H₂]
  | .ex f => by
    simp only [embed]
    iintro ⟨%a, H⟩
    icases (embed_toHeaplet (f a)) $$ H with ⟨%h, %hs, Hh⟩
    iexists h
    isplitr
    · ipureintro; exact ⟨a, hs⟩
    · iexact Hh

/-- Step 2: owned cells are genuinely in the (authoritative) heap —
`ghost_map_lookup_big` against the state interpretation's auth. -/
theorem ownHeaplet_sub {m : GoHeapF HeapCell} {h : GoHeapF HeapCell} :
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) m ∗ ownHeaplet h)
      ⊢ ⌜Heaplet.sub h m⌝ := by
  unfold genHeapInterp ownHeaplet pointsTo
  iintro ⟨⟨%mγ, -, Hσ, -⟩, Hown⟩
  ihave %hsub := ghost_map_lookup_big h $$ Hσ Hown
  ipureintro
  intro k c hk
  exact hsub k c hk

/-- A sub-heaplet fact about a disjoint union decomposes (via
`union_cover`) — the pure tail of framed extraction. -/
theorem sub_union_split {hQ F m : GoHeapF HeapCell}
    (hdisj : ∀ k, hQ.get? k = none ∨ F.get? k = none)
    (hsub : Heaplet.sub (Std.PartialMap.union (M := GoHeapF) hQ F) m) :
    Heaplet.sub hQ m ∧ Heaplet.sub F m :=
  ⟨fun k c hk => hsub k c ((union_cover hdisj k c).mpr (.inl hk)),
   fun k c hk => hsub k c ((union_cover hdisj k c).mpr (.inr hk))⟩

/-- **Extraction.** The state interpretation over the final heap plus an
embedded postcondition yields the pure native fact: some sub-heaplet of the
final heap satisfies `Q`. This is the once-proven postcondition crossing
the generic exit theorem feeds to `go_heap_adequacy_own`'s `Hext`. -/
theorem extract {Q : HProp} {m : GoHeapF HeapCell} :
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) m ∗ embed Q)
      ⊢ ⌜∃ h : Heaplet, Heaplet.sub h m ∧ sat h Q⌝ := by
  iintro ⟨Hσ, HQ⟩
  icases (embed_toHeaplet Q) $$ HQ with ⟨%h, %hs, Hown⟩
  ihave %hsub := ownHeaplet_sub $$ [$Hσ $Hown]
  ipureintro
  exact ⟨h, hsub, hs⟩

end

end GoLean.Iris
