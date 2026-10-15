import GoLean.GoCore.ShadowOrder
import GoLean.GoCore.PoolStep

/-! Shadow-history contracts for the existing detector update. Sortedness is
strict (hence keys are unique). Different keys may overlap; no disjointness
premise is used to preserve their histories. -/
namespace GoLean.GoCore.Machine
open GoLean Std

def ShadowOrdered (xs : List (ShadowKey × ShadowCell)) : Prop :=
  xs.Pairwise (fun a b => compare a.1 b.1 = .lt)

def shadowLookup (xs : List (ShadowKey × ShadowCell)) (key : ShadowKey) :
    Option ShadowCell := (xs.find? (·.1 == key)).map (·.2)

theorem ShadowOrdered.keys_nodup {xs : List (ShadowKey × ShadowCell)}
    (ordered : ShadowOrdered xs) : (xs.map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact ordered.imp (fun h e => by rw [e] at h; simp at h)

theorem shadowLookup_mem {xs : List (ShadowKey × ShadowCell)} {key cell}
    (found : shadowLookup xs key = some cell) : (key, cell) ∈ xs := by
  unfold shadowLookup at found
  cases hf : xs.find? (·.1 == key) with
  | none => simp [hf] at found
  | some p =>
    rcases p with ⟨k, v⟩
    have heq : (k == key) = true := List.find?_some (p := fun (p : ShadowKey × ShadowCell) => p.1 == key) hf
    have hk : k = key := eq_of_beq heq
    subst k
    simp only [hf, Option.map_some, Option.some.injEq] at found
    subst v
    exact List.mem_of_find?_eq_some hf

theorem shadowSet_other_mem {xs : List (ShadowKey × ShadowCell)}
    {key other : ShadowKey} {value cell : ShadowCell} (ne : other ≠ key) :
    (other, cell) ∈ shadowSet xs key value ↔ (other, cell) ∈ xs := by
  induction xs with
  | nil => simp [shadowSet, ne]
  | cons p xs ih =>
    rcases p with ⟨k, w⟩
    cases h : compare key k with
    | lt => simp [shadowSet, h, ne]
    | eq =>
      obtain rfl := LawfulEqOrd.eq_of_compare h
      simp [shadowSet, ne]
    | gt => simp [shadowSet, h, ih]

theorem shadowSet_origin {xs : List (ShadowKey × ShadowCell)}
    {key : ShadowKey} {value : ShadowCell} {p : ShadowKey × ShadowCell}
    (h : p ∈ shadowSet xs key value) : p = (key, value) ∨ p ∈ xs := by
  induction xs with
  | nil => simpa [shadowSet] using h
  | cons q xs ih =>
    rcases q with ⟨k, w⟩
    cases hc : compare key k <;> simp only [shadowSet, hc, List.mem_cons] at h
    · rcases h with h | h; exact Or.inl h; exact Or.inr (List.mem_cons.2 h)
    · rcases h with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases h with h | h
      · exact Or.inr (List.mem_cons.2 (Or.inl h))
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem shadowSet_ordered {xs : List (ShadowKey × ShadowCell)}
    (ordered : ShadowOrdered xs) (key : ShadowKey) (value : ShadowCell) :
    ShadowOrdered (shadowSet xs key value) := by
  induction xs with
  | nil => simp [ShadowOrdered, shadowSet]
  | cons p xs ih =>
    rcases p with ⟨k, w⟩
    obtain ⟨head, tail⟩ := List.pairwise_cons.1 ordered
    cases h : compare key k with
    | lt =>
      simp only [shadowSet, h, ShadowOrdered, List.pairwise_cons]
      refine ⟨?_, head, tail⟩
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h
      · exact TransCmp.lt_trans h (head q hq)
    | eq =>
      obtain rfl := LawfulEqOrd.eq_of_compare h
      simpa [shadowSet, ShadowOrdered] using
        (List.pairwise_cons.2 ⟨head, tail⟩ : ShadowOrdered ((key, value) :: xs))
    | gt =>
      simp only [shadowSet, h, ShadowOrdered, List.pairwise_cons]
      refine ⟨?_, ih tail⟩
      intro q hq
      rcases shadowSet_origin hq with rfl | hq
      · exact OrientedCmp.lt_of_gt h
      · exact head q hq

theorem shadowSet_lookup_self (xs : List (ShadowKey × ShadowCell))
    (key : ShadowKey) (value : ShadowCell) :
    shadowLookup (shadowSet xs key value) key = some value := by
  induction xs with
  | nil => simp [shadowSet, shadowLookup]
  | cons p xs ih =>
    rcases p with ⟨k, w⟩
    cases h : compare key k with
    | lt => simp [shadowSet, h, shadowLookup]
    | eq => simp [shadowSet, h, shadowLookup]
    | gt =>
      have ne : k ≠ key := by
        intro e; subst k; simp at h
      simpa [shadowSet, h, shadowLookup, ne] using ih

theorem shadowSet_lookup_other {xs : List (ShadowKey × ShadowCell)}
    {key other : ShadowKey} {value : ShadowCell} (ne : other ≠ key) :
    shadowLookup (shadowSet xs key value) other = shadowLookup xs other := by
  induction xs with
  | nil => simp [shadowSet, shadowLookup, Ne.symm ne]
  | cons p xs ih =>
    rcases p with ⟨k, w⟩
    cases h : compare key k with
    | lt => simp [shadowSet, h, shadowLookup, Ne.symm ne]
    | eq =>
      obtain rfl := LawfulEqOrd.eq_of_compare h
      simp [shadowSet, shadowLookup, Ne.symm ne]
    | gt =>
      by_cases e : k = other
      · subst k; simp [shadowSet, h, shadowLookup]
      · simpa [shadowSet, h, shadowLookup, e] using ih

theorem RaceState.accessKey_ordered {r r' : RaceState} {t kind key}
    (ordered : ShadowOrdered r.shadow) (ok : r.accessKey t kind key = .ok r') :
    ShadowOrdered r'.shadow := by
  unfold RaceState.accessKey at ok
  dsimp only at ok
  split at ok
  · contradiction
  · cases ok
    exact shadowSet_ordered ordered _ _

/-- Every history at a different key survives a successful access, even when
that key overlaps the updated key. Successful conflict checking is explicit. -/
theorem RaceState.accessKey_other {r r' : RaceState} {t kind key other}
    (ok : r.accessKey t kind key = .ok r') (ne : other ≠ key) :
    shadowLookup r'.shadow other = shadowLookup r.shadow other := by
  unfold RaceState.accessKey at ok
  dsimp only at ok
  split at ok
  · contradiction
  · cases ok
    exact shadowSet_lookup_other ne

theorem RaceState.accessKey_reject_of_mem {r : RaceState} {t kind key prior cell}
    (mem : (prior, cell) ∈ r.shadow) (overlap : key.overlap prior = true)
    (conflict : cell.conflicts kind t (r.vcOf t) = true) :
    r.accessKey t kind key = .error .raceDetected := by
  have hit : r.shadow.any (fun (k, c) => key.overlap k && c.conflicts kind t (r.vcOf t)) = true :=
    List.any_eq_true.2 ⟨(prior, cell), mem, by simp [overlap, conflict]⟩
  simp [RaceState.accessKey, hit, throw, throwThe, MonadExceptOf.throw]

@[simp] theorem RaceState.hbAction_shadow (r : RaceState) (t : Nat) (a : HbAction) :
    (r.hbAction t a).shadow = r.shadow := by
  cases a <;>
    simp [RaceState.hbAction, RaceState.slotOp, RaceState.rendezvous,
      RaceState.closeOp, RaceState.closeAcquire, RaceState.spawn,
      RaceState.syncAcquire, RaceState.syncRelease, RaceState.atomicAcquire,
      RaceState.atomicReleaseStore, RaceState.atomicReleaseAcquire,
      RaceState.setVC, RaceState.setChan, RaceState.setSync, RaceState.setAtomic]
  split <;> try rfl
  split <;> rfl

theorem RaceState.event_ordered {r r' : RaceState} {t : Nat} {e : MemEvent}
    (ordered : ShadowOrdered r.shadow) (ok : r.event t e = .ok r') :
    ShadowOrdered r'.shadow := by
  induction e generalizing r r' t with
  | access kind key => exact RaceState.accessKey_ordered ordered ok
  | hb a =>
    cases ok
    simpa using ordered
  | attributed who e ih => exact ih ordered ok

theorem RaceState.events_ordered {r r' : RaceState} {t : Nat} {es : AccessTrace}
    (ordered : ShadowOrdered r.shadow) (ok : r.events t es = .ok r') :
    ShadowOrdered r'.shadow := by
  induction es generalizing r with
  | nil => cases ok; exact ordered
  | cons e es ih =>
    simp only [RaceState.events] at ok
    cases he : r.event t e with
    | error err => simp [he, Bind.bind, Except.bind] at ok
    | ok next =>
      simp only [he, Bind.bind, Except.bind] at ok
      exact ih (RaceState.event_ordered ordered he) ok

theorem raceUpdate_ordered {r r' : RaceState} {ev : StepEvent} {m : MultiConfig}
    (ordered : ShadowOrdered r.shadow) (ok : raceUpdate ev m r = .ok r') :
    ShadowOrdered r'.shadow := by
  unfold raceUpdate at ok
  split at ok
  · cases ok; exact ordered
  · exact RaceState.events_ordered ordered ok

/-- No final-state invariant assumption: the actual detector-checked prefix
preserves strict key order from any ordered start, in particular `{}`. -/
theorem PoolPrefix.shadow_ordered {ctx n m r ch es mf rf tail}
    (run : PoolPrefix ctx n m r ch es mf rf tail)
    (ordered : ShadowOrdered r.shadow) : ShadowOrdered rf.shadow := by
  induction run with
  | done => exact ordered
  | step _ _ detector _ ih => exact ih (raceUpdate_ordered ordered detector)

theorem PoolPrefix.shadow_ordered_empty {ctx n m ch es mf rf tail}
    (run : PoolPrefix ctx n m {} ch es mf rf tail) : ShadowOrdered rf.shadow :=
  run.shadow_ordered (by simp [ShadowOrdered])

/-- Excludes writes/reads to this exact key, not accesses to overlapping keys.
The success premise of the detector fold still enforces conflict checking. -/
def _root_.GoLean.GoCore.MemEvent.AvoidsKey (key : ShadowKey) : MemEvent → Prop
  | .access _ other => key ≠ other
  | .hb _ => True
  | .attributed _ e => MemEvent.AvoidsKey key e

theorem RaceState.event_preserves_lookup {r r' : RaceState} {t e key}
    (avoid : MemEvent.AvoidsKey key e) (ok : r.event t e = .ok r') :
    shadowLookup r'.shadow key = shadowLookup r.shadow key := by
  induction e generalizing r r' t with
  | access kind other => exact RaceState.accessKey_other ok avoid
  | hb a => cases ok; simp
  | attributed who e ih => exact ih avoid ok

theorem RaceState.events_preserve_lookup {r r' : RaceState} {t es key}
    (avoid : ∀ e ∈ es, MemEvent.AvoidsKey key e) (ok : r.events t es = .ok r') :
    shadowLookup r'.shadow key = shadowLookup r.shadow key := by
  induction es generalizing r with
  | nil => cases ok; rfl
  | cons e es ih =>
    simp only [RaceState.events] at ok
    cases he : r.event t e with
    | error err => simp [he, Bind.bind, Except.bind] at ok
    | ok next =>
      simp only [he, Bind.bind, Except.bind] at ok
      exact (ih (fun e h => avoid e (List.mem_cons_of_mem _ h)) ok).trans
        (RaceState.event_preserves_lookup (avoid e List.mem_cons_self) he)

theorem raceUpdate_preserves_lookup {r r' : RaceState} {ev : StepEvent} {m key}
    (avoid : ∀ e ∈ ev.trace, MemEvent.AvoidsKey key e)
    (ok : raceUpdate ev m r = .ok r') :
    shadowLookup r'.shadow key = shadowLookup r.shadow key := by
  unfold raceUpdate at ok
  split at ok
  · cases ok; rfl
  · exact RaceState.events_preserve_lookup avoid ok

theorem PoolPrefix.preserves_lookup {ctx n m r ch es mf rf tail key}
    (run : PoolPrefix ctx n m r ch es mf rf tail)
    (avoid : ∀ de ∈ es, ∀ e ∈ de.event.trace, MemEvent.AvoidsKey key e) :
    shadowLookup rf.shadow key = shadowLookup r.shadow key := by
  induction run with
  | done => rfl
  | step _ _ detector _ ih =>
    exact (ih (fun de h => avoid de (List.mem_cons_of_mem _ h))).trans
      (raceUpdate_preserves_lookup (avoid _ List.mem_cons_self) detector)

end GoLean.GoCore.Machine
