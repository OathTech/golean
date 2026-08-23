import GoLeanProofs.FastEval.Loops

/-!
# FastEval — shared small mirrors (campaign Arc 2, U4): the heap-reading
helpers consumed across the wave's modules, plus the loop exemplar.

UNTRUSTED METHOD — never in any statement closure. Template per
`docs/campaign-arc2-log.md` (U4 template of record);
`sliceVisibleValuesF` is the worked exemplar of the LOOP rule: fast
loops are `List.forIn (List.range' …)` (structural, kernel-friendly);
sims convert the slow side by `Std.Legacy.Range.forIn_eq_forIn_range'`
and transport by `list_forIn_sim`.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- `loadMany`, fast. -/
def loadManyF (σF : ExecStateF) : List Loc → Except GoError (List GoValue)
  | [] => return []
  | loc :: locs => do return (← loadLocF σF loc) :: (← loadManyF σF locs)

/-- `storeMany`, fast. -/
def storeManyF : ExecStateF → List Loc → List GoValue → Except GoError ExecStateF
  | σF, [], [] => return σF
  | σF, loc :: locs, v :: vs => do storeManyF (← storeLocF σF loc v) locs vs
  | _, [], _ :: _ => stuck "extra GoCore assignment value"
  | _, _ :: _, [] => stuck "missing GoCore assignment value"

/-- `mapEntries`, fast. -/
def mapEntriesF (σF : ExecStateF) (map : MapValue) :
    Except GoError (Option (Loc × Array (GoValue × GoValue))) := do
  match map.base with
  | none => return none
  | some baseLoc =>
      match ← loadLocF σF baseLoc with
      | .mapData entries => return some (baseLoc, entries)
      | other => stuck s!"expected map data, got {repr other}"

/-- `mapLookupValue`, fast (the key scan and defaults are PURE — the
lazy `γF` view carries them; only the entries read is mirrored). -/
def mapLookupValueF (σF : ExecStateF) (map : MapValue) (key : GoValue)
    (keyTy valueTy : Ty) : Except GoError (GoValue × Bool) := do
  match ← mapEntriesF σF map with
  | none => do
      checkKeyHashable (γF σF) key (isInsert := false) (nonEmpty := false)
      return (← defaultValue (γF σF) valueTy, false)
  | some (_, entries) =>
      match ← mapEntryIndex? (γF σF) keyTy entries key with
      | some i =>
          match entries[i]? with
          | some (_, value) => return (value, true)
          | none => stuck s!"missing map entry at index {i}"
      | none => return (← defaultValue (γF σF) valueTy, false)

/-- `sliceVisibleValues`, fast — the loop exemplar. -/
def sliceVisibleValuesF (σF : ExecStateF) (slice : SliceValue) :
    Except GoError (Array GoValue) := do
  validateSlice slice
  let values ← forIn (List.range' 0 slice.len 1) (#[] : Array GoValue)
    (fun i values => do
      let v ← loadLocF σF (← sliceIndexLoc slice (Int.ofNat i))
      pure (ForInStep.yield (values.push v)))
  return values

/-! ## Sims -/

theorem loadManyF_ok {σF : ExecStateF} :
    ∀ {locs : List Loc} {vs : List GoValue},
    loadManyF σF locs = .ok vs → loadMany (γF σF) locs = .ok vs := by
  intro locs
  induction locs with
  | nil => intro vs h; simpa [loadManyF, loadMany] using h
  | cons loc locs ih =>
      intro vs h
      unfold loadManyF at h
      unfold loadMany
      cases hl : loadLocF σF loc with
      | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
      | ok v =>
          rw [hl] at h
          rw [loadLocF_ok hl]
          simp only [Bind.bind, Except.bind] at h ⊢
          cases hm : loadManyF σF locs with
          | error e => rw [hm] at h; simp at h
          | ok vs' =>
              rw [hm] at h
              rw [ih hm]
              exact h

theorem storeManyF_ok :
    ∀ {locs : List Loc} {σF : ExecStateF} {vs : List GoValue} {σF' : ExecStateF},
    storeManyF σF locs vs = .ok σF' →
    storeMany (γF σF) locs vs = .ok (γF σF') := by
  intro locs
  induction locs with
  | nil =>
      intro σF vs σF' h
      cases vs with
      | nil =>
          simp only [storeManyF, pure, Except.pure, Except.ok.injEq] at h
          simp [storeMany, pure, Except.pure, h]
      | cons v vs => simp [storeManyF] at h
  | cons loc locs ih =>
      intro σF vs σF' h
      cases vs with
      | nil => simp [storeManyF] at h
      | cons v vs =>
          unfold storeManyF at h
          unfold storeMany
          cases hs : storeLocF σF loc v with
          | error e => rw [hs] at h; simp [Bind.bind, Except.bind] at h
          | ok σF₁ =>
              rw [hs] at h
              rw [storeLocF_ok hs]
              simp only [Bind.bind, Except.bind] at h ⊢
              exact ih h

theorem mapEntriesF_ok {σF : ExecStateF} {map : MapValue} {r} :
    mapEntriesF σF map = .ok r → mapEntries (γF σF) map = .ok r := by
  intro h
  unfold mapEntriesF at h
  split at h <;> rename_i hb
  · simp only [mapEntries, hb]
    exact h
  · rename_i baseLoc
    simp only [mapEntries, hb]
    cases hl : loadLocF σF baseLoc with
    | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok bv =>
        rw [hl] at h
        rw [loadLocF_ok hl]
        simp only [Bind.bind, Except.bind] at h ⊢
        exact h

theorem mapLookupValueF_ok {σF : ExecStateF} {map : MapValue} {key : GoValue}
    {keyTy valueTy : Ty} {r} :
    mapLookupValueF σF map key keyTy valueTy = .ok r →
    mapLookupValue (γF σF) map key keyTy valueTy = .ok r := by
  intro h
  unfold mapLookupValueF at h
  unfold mapLookupValue
  cases hm : mapEntriesF σF map with
  | error e => rw [hm] at h; simp [Bind.bind, Except.bind] at h
  | ok ents =>
      rw [hm] at h
      rw [mapEntriesF_ok hm]
      simp only [Bind.bind, Except.bind] at h ⊢
      exact h

theorem sliceVisibleValuesF_ok {σF : ExecStateF} {slice : SliceValue}
    {arr : Array GoValue} :
    sliceVisibleValuesF σF slice = .ok arr →
    sliceVisibleValues (γF σF) slice = .ok arr := by
  intro h
  unfold sliceVisibleValuesF at h
  unfold sliceVisibleValues
  cases hv : validateSlice slice with
  | error e => rw [hv] at h; simp [Bind.bind, Except.bind] at h
  | ok u =>
      rw [hv] at h
      cases hrun : forIn (List.range' 0 slice.len 1) (#[] : Array GoValue)
          (fun i values => do
            let v ← loadLocF σF (← sliceIndexLoc slice (Int.ofNat i))
            pure (ForInStep.yield (values.push v))) with
      | error e => rw [hrun] at h; simp [Bind.bind, Except.bind] at h
      | ok values =>
          rw [hrun] at h
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at h
          obtain ⟨res, hres, hrel⟩ :=
            list_forIn_sim (R := (· = ·))
              (body := fun i r => do
                let x ← sliceIndexLoc slice (Int.ofNat i)
                let y ← loadLoc (γF σF) x
                pure PUnit.unit
                pure (ForInStep.yield (r.push y)))
              (fun i b' b hR s' hstep => by
                subst hR
                cases hloc : sliceIndexLoc slice (Int.ofNat i) with
                | error e => rw [hloc] at hstep; simp [Bind.bind, Except.bind] at hstep
                | ok loc =>
                    rw [hloc] at hstep
                    simp only [Bind.bind, Except.bind] at hstep
                    cases hl : loadLocF σF loc with
                    | error e => rw [hl] at hstep; simp at hstep
                    | ok v =>
                        rw [hl] at hstep
                        simp only [pure, Except.pure, Except.ok.injEq] at hstep
                        refine ⟨ForInStep.yield (b'.push v), ?_, ?_⟩
                        · simp only [Bind.bind, Except.bind]
                          rw [loadLocF_ok hl]
                          simp [pure, Except.pure]
                        · rw [← hstep]
                          simp [stepRel])
              (List.range' 0 slice.len 1) rfl hrun
          simp only [Std.Legacy.Range.forIn_eq_forIn_range',
            Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
            Nat.div_one]
          rw [hres]
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq]
          rw [← hrel, h]

end GoLean.FastEval
