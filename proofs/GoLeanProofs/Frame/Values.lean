import GoLeanProofs.Frame.TypeCongr

/-!
# The executable frame theorem, module 4: value-operation commutations

The type-directed value walks (`coerceStoredValue`,
`normalizeValueForTy`, `isNormalForTy`, `defaultValue`,
`convertValueToTy`) and the shape coercions (`valueAs*`) commute with
the address renaming: canonical `.ok` results transfer to the framed
run with renamed payloads (the `_ren` ok-transfer convention —
statements are canonical-hypothesis → framed-conclusion, so error arms
whose messages embed value `repr`s never need to transfer).

None of these operations read the heap; the state enters only through
`σ.types`, so the framed side is any state with equal types.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

-- Uniform simp sets across sibling arms (the golden-walk convention).
set_option linter.unusedSimpArgs false

variable (ρ : Nat → Nat)

/-! ## Shape inversions (renaming preserves and reflects head shapes) -/

theorem renameValue_int_iff {v : GoValue} {n : Int} {k : IntKind} :
    renameValue ρ v = .int n k ↔ v = .int n k := by
  cases v <;> simp [renameValue]

theorem renameValue_float_iff {v : GoValue} {b : Nat} {k : FloatKind} :
    renameValue ρ v = .float b k ↔ v = .float b k := by
  cases v <;> simp [renameValue]

theorem renameValue_array_iff {v : GoValue} {vs : Array GoValue} :
    renameValue ρ v = .array vs
      ↔ ∃ vs₀, v = .array vs₀ ∧ vs = (renameValueList ρ vs₀.toList).toArray := by
  cases v <;> simp [renameValue, eq_comm]

theorem renameValue_struct_iff {v : GoValue} {tid : TypeId}
    {fs : Array (String × GoValue)} :
    renameValue ρ v = .struct tid fs
      ↔ ∃ fs₀, v = .struct tid fs₀
          ∧ fs = (renameValueFields ρ fs₀.toList).toArray := by
  cases v
  case struct tid₀ fs₀ =>
    constructor
    · intro h
      simp only [renameValue, GoValue.struct.injEq] at h
      exact ⟨fs₀, by simp [h.1], h.2.symm⟩
    · rintro ⟨fs₁, heq, rfl⟩
      injection heq with h1 h2
      subst h1; subst h2
      simp [renameValue]
  all_goals simp [renameValue]

/-! ## `valueAs*` coercions -/

theorem valueAsInt_ren {v : GoValue} {i : Int} (h : valueAsInt v = .ok i) :
    valueAsInt (renameValue ρ v) = .ok i := by
  cases v <;> simp_all [valueAsInt, renameValue]

theorem valueAsIntValue_ren {v : GoValue} {p : Int × IntKind}
    (h : valueAsIntValue v = .ok p) :
    valueAsIntValue (renameValue ρ v) = .ok p := by
  cases v <;> simp_all [valueAsIntValue, renameValue]

theorem valueAsBool_ren {v : GoValue} {b : Bool} (h : valueAsBool v = .ok b) :
    valueAsBool (renameValue ρ v) = .ok b := by
  cases v <;> simp_all [valueAsBool, renameValue]

theorem valueAsSlice_ren {v : GoValue} {sl : SliceValue}
    (h : valueAsSlice v = .ok sl) :
    valueAsSlice (renameValue ρ v)
      = .ok { sl with base := sl.base.map (renameLoc ρ) } := by
  cases v <;> simp_all [valueAsSlice, renameValue]

theorem valueAsMap_ren {v : GoValue} {m : MapValue}
    (h : valueAsMap v = .ok m) :
    valueAsMap (renameValue ρ v)
      = .ok { base := m.base.map (renameLoc ρ) } := by
  cases v <;> simp_all [valueAsMap, renameValue]

theorem valueAsChan_ren {v : GoValue} {c : ChanValue}
    (h : valueAsChan v = .ok c) :
    valueAsChan (renameValue ρ v)
      = .ok { base := c.base.map (renameLoc ρ) } := by
  cases v <;> simp_all [valueAsChan, renameValue]

theorem valueAsLoc_sim (v : GoValue) :
    ExSim (fun l lF => lF = renameLoc ρ l)
      (valueAsLoc v) (valueAsLoc (renameValue ρ v)) := by
  cases v with
  | addr l => exact ExSim.ok rfl
  | nil => exact ExSim.panic
  | _ => exact ExSim.stuck'

theorem valueAsLoc_ren {v : GoValue} {l : Loc} (h : valueAsLoc v = .ok l) :
    valueAsLoc (renameValue ρ v) = .ok (renameLoc ρ l) := by
  obtain ⟨lF, hF, hrel⟩ := (valueAsLoc_sim ρ v).ok_inv h
  rw [hF, hrel]

theorem valueAsLoc_panic_ren {v : GoValue} {m : String}
    (h : valueAsLoc v = .error (.panic m)) :
    valueAsLoc (renameValue ρ v) = .error (.panic m) :=
  (valueAsLoc_sim ρ v).panic_inv h

/-! ## Loc-free values rename to themselves -/

theorem renameValue_locFree :
    ∀ v : GoValue, GoValue.locSup v = 0 → renameValue ρ v = v := by
  refine fun v => renameValue.induct
    (motive_1 := fun v => GoValue.locSup v = 0 → renameValue ρ v = v)
    (motive_2 := fun l => goValueEntriesSup l = 0 → renameValueEntries ρ l = l)
    (motive_3 := fun l => goValueListSup l = 0 → renameValueList ρ l = l)
    (motive_4 := fun l => goValueFieldsSup l = 0 → renameValueFields ρ l = l)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
  · intro _; rfl
  · intro b _; rfl
  · intro n k _; rfl
  · intro b k _; rfl
  · intro s _; rfl
  · intro _; rfl
  · -- addr: impossible at sup 0
    intro l h
    simp [GoValue.locSup, Loc.locSup] at h
  · -- interface
    intro t v ih h
    simp only [GoValue.locSup] at h
    simp [renameValue, ih h]
  · -- struct
    intro tid fields ih h
    simp only [GoValue.locSup] at h
    simp [renameValue, ih h]
  · -- array
    intro vs ih h
    simp only [GoValue.locSup] at h
    simp [renameValue, ih h]
  · -- slice
    intro s h
    simp only [GoValue.locSup] at h
    cases s with
    | mk base off len cap =>
        cases base with
        | none => simp [renameValue]
        | some l => simp [optLocSup, Loc.locSup] at h
  · -- map
    intro m h
    simp only [GoValue.locSup] at h
    cases m with
    | mk base =>
        cases base with
        | none => simp [renameValue]
        | some l => simp [optLocSup, Loc.locSup] at h
  · -- mapData
    intro es ih h
    simp only [GoValue.locSup] at h
    simp [renameValue, ih h]
  · -- chan
    intro c h
    simp only [GoValue.locSup] at h
    cases c with
    | mk base =>
        cases base with
        | none => simp [renameValue]
        | some l => simp [optLocSup, Loc.locSup] at h
  · -- chanData
    intro buf cap closed ih h
    simp only [GoValue.locSup] at h
    simp [renameValue, ih h]
  · -- funcVal
    intro fid cap ih h
    simp only [GoValue.locSup] at h
    simp [renameValue, ih h]
  · intro p _; rfl
  · intro _; rfl
  · -- value list cons
    intro v vs ihv ihl h
    simp only [goValueListSup, Nat.max_eq_zero_iff] at h
    simp [renameValueList, ihv h.1, ihl h.2]
  · intro _; rfl
  · -- fields cons
    intro n v rest ihv ihl h
    simp only [goValueFieldsSup, Nat.max_eq_zero_iff] at h
    simp [renameValueFields, ihv h.1, ihl h.2]
  · intro _; rfl
  · -- entries cons
    intro k v rest ihk ihv ihl h
    simp only [goValueEntriesSup, Nat.max_eq_zero_iff] at h
    simp [renameValueEntries, ihk h.1.1, ihv h.1.2, ihl h.2]

/-! ## `coerceStoredValue` -/

private theorem renameValueFields_length (l : List (String × GoValue)) :
    (renameValueFields ρ l).length = l.length := by
  rw [renameValueFields_eq_map]; exact List.length_map ..

theorem coerceStoredValue_ren :
    ∀ old v r : GoValue, coerceStoredValue old v = .ok r →
      coerceStoredValue (renameValue ρ old) (renameValue ρ v)
        = .ok (renameValue ρ r) := by
  refine fun old v => coerceStoredValue.induct
    (motive_1 := fun old v => ∀ r, coerceStoredValue old v = .ok r →
      coerceStoredValue (renameValue ρ old) (renameValue ρ v)
        = .ok (renameValue ρ r))
    (motive_2 := fun oldFs newFs => ∀ r, coerceStruct oldFs newFs = .ok r →
      coerceStruct (renameValueFields ρ oldFs) (renameValueFields ρ newFs)
        = .ok ((renameValueFields ρ r.toList).toArray))
    (motive_3 := fun oldL newL => ∀ r, coerceArray oldL newL = .ok r →
      coerceArray (renameValueList ρ oldL) (renameValueList ρ newL)
        = .ok ((renameValueList ρ r.toList).toArray))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ old v
  · -- int / int
    intro ov k nv k' r h
    simp only [coerceStoredValue, pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp [renameValue, coerceStoredValue]
  · -- float / float, kinds equal
    intro ob kind bits k hk r h
    simp only [coerceStoredValue] at h
    rw [if_pos hk] at h
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    simp only [renameValue, coerceStoredValue]
    rw [if_pos hk]
    rfl
  · -- float / float, kind mismatch: stuck, no ok
    intro ob kind bits k hk r h
    simp only [coerceStoredValue] at h
    rw [if_neg hk] at h
    simp at h
  · -- array size mismatch: stuck
    intro o n hne r h
    simp only [coerceStoredValue] at h
    rw [if_pos hne] at h
    simp at h
  · -- array / array
    intro o n hne ih r h
    simp only [coerceStoredValue] at h
    rw [if_neg hne] at h
    rw [map_eq_ok] at h
    obtain ⟨arr, harr, rfl⟩ := h
    have ihr := ih arr harr
    simp only [renameValue, coerceStoredValue]
    rw [if_neg (by
      simp only [ne_eq, List.size_toArray, renameValueList_length,
        Array.length_toList, bne_iff_ne]
      simpa using hne)]
    rw [map_eq_ok]
    exact ⟨(renameValueList ρ arr.toList).toArray, by simpa using ihr, by simp⟩
  · -- struct type mismatch
    intro ot ofs nt nfs hne r h
    simp only [coerceStoredValue] at h
    rw [if_pos hne] at h
    simp at h
  · -- struct field-count mismatch
    intro ot ofs nt nfs hne hsz r h
    simp only [coerceStoredValue] at h
    rw [if_neg hne, if_pos hsz] at h
    simp at h
  · -- struct / struct
    intro ot ofs nt nfs hne hsz ih r h
    simp only [coerceStoredValue] at h
    rw [if_neg hne, if_neg hsz] at h
    rw [map_eq_ok] at h
    obtain ⟨fs, hfs, rfl⟩ := h
    have ihr := ih fs hfs
    simp only [renameValue, coerceStoredValue]
    rw [if_neg (by simpa using hne)]
    rw [if_neg (by
      simp only [ne_eq, List.size_toArray, renameValueFields_length,
        Array.length_toList, bne_iff_ne]
      simpa using hsz)]
    rw [map_eq_ok]
    exact ⟨(renameValueFields ρ fs.toList).toArray, by simpa using ihr, by simp⟩
  · -- catch-all: pass the new value through
    intro t v hint hfloat harr hstruct r h
    rw [coerceStoredValue.eq_def] at h
    split at h
    · exact (hint _ _ _ _ rfl rfl).elim
    · exact (hfloat _ _ _ _ rfl rfl).elim
    · exact (harr _ _ rfl rfl).elim
    · exact (hstruct _ _ _ _ rfl rfl).elim
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      have hgoal : ∀ rt rv : GoValue, renameValue ρ t = rt → renameValue ρ v = rv →
          coerceStoredValue rt rv = .ok rv := by
        intro rt rv hgt hgv
        rw [coerceStoredValue.eq_def]
        split
        · rename_i n k v' k'
          exact (hint _ _ _ _ ((renameValue_int_iff ρ).mp hgt)
            ((renameValue_int_iff ρ).mp hgv)).elim
        · rename_i b k v' k'
          exact (hfloat _ _ _ _ ((renameValue_float_iff ρ).mp hgt)
            ((renameValue_float_iff ρ).mp hgv)).elim
        · rename_i a b
          obtain ⟨a₀, ha, -⟩ := (renameValue_array_iff ρ).mp hgt
          obtain ⟨b₀, hb, -⟩ := (renameValue_array_iff ρ).mp hgv
          exact (harr _ _ ha hb).elim
        · rename_i t1 f1 t2 f2
          obtain ⟨f1₀, hf1, -⟩ := (renameValue_struct_iff ρ).mp hgt
          obtain ⟨f2₀, hf2, -⟩ := (renameValue_struct_iff ρ).mp hgv
          exact (hstruct _ _ _ _ hf1 hf2).elim
        · rfl
      exact hgoal _ _ rfl rfl
  · -- coerceArray cons
    intro ov orest nv nrest ih1 ih3 r h
    simp only [coerceArray, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    simp only [renameValueList, coerceArray, bind_eq_ok]
    refine ⟨_, ih1 head hhead, _, ih3 tail htail, ?_⟩
    simp [renameValueList_eq_map]
  · -- coerceArray catch-all
    intro t x hnc r h
    rw [coerceArray.eq_def] at h
    split at h
    · exact (hnc _ _ _ _ rfl rfl).elim
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      have hgoal : ∀ rt rx : List GoValue, renameValueList ρ t = rt →
          renameValueList ρ x = rx →
          coerceArray rt rx = .ok ((renameValueList ρ (#[] : Array GoValue).toList).toArray) := by
        intro rt rx hgt hgx
        rw [coerceArray.eq_def]
        split
        · rename_i a as b bs
          cases t with
          | nil => simp [renameValueList] at hgt
          | cons tv tl =>
              cases x with
              | nil => simp [renameValueList] at hgx
              | cons xv xl => exact (hnc _ _ _ _ rfl rfl).elim
        · simp [renameValueList]
      exact hgoal _ _ rfl rfl
  · -- coerceStruct cons, name mismatch: stuck
    intro on ov orest nn nv nrest hname _ih1 _ih2 r h
    simp only [coerceStruct] at h
    rw [if_pos hname] at h
    simp [Bind.bind, Except.bind] at h
  · -- coerceStruct cons, names equal
    intro on ov orest nn nv nrest hname ih1 ih2 r h
    simp only [coerceStruct] at h
    rw [if_neg hname] at h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    simp only [renameValueFields, coerceStruct]
    rw [if_neg (by simpa using hname)]
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
    refine ⟨_, ih1 head hhead, _, ih2 tail htail, ?_⟩
    simp [renameValueFields_eq_map]
  · -- coerceStruct catch-all
    intro t x hnc r h
    rw [coerceStruct.eq_def] at h
    split at h
    · exact (hnc _ _ _ _ _ _ rfl rfl).elim
    · simp only [pure_eq_ok, Except.ok.injEq] at h
      subst h
      have hgoal : ∀ rt rx : List (String × GoValue), renameValueFields ρ t = rt →
          renameValueFields ρ x = rx →
          coerceStruct rt rx
            = .ok ((renameValueFields ρ (#[] : Array (String × GoValue)).toList).toArray) := by
        intro rt rx hgt hgx
        rw [coerceStruct.eq_def]
        split
        · rename_i a b as c d cs
          cases t with
          | nil => simp [renameValueFields] at hgt
          | cons tp tl =>
              cases x with
              | nil => simp [renameValueFields] at hgx
              | cons xp xl => exact (hnc _ _ _ _ _ _ rfl rfl).elim
        · simp [renameValueFields]
      exact hgoal _ _ rfl rfl

/-! ## `normalizeValueForTy` -/

section Normalize

variable {σ σF : ExecState}

theorem normalizeListWith_ren {f g : GoValue → Except GoError GoValue}
    (hfg : ∀ v r, f v = .ok r → g (renameValue ρ v) = .ok (renameValue ρ r)) :
    ∀ {l : List GoValue} {arr : Array GoValue},
      normalizeListWith f l = .ok arr →
      normalizeListWith g (renameValueList ρ l)
        = .ok ((renameValueList ρ arr.toList).toArray) := by
  intro l
  induction l with
  | nil =>
      intro arr h
      simp only [normalizeListWith, pure_eq_ok, Except.ok.injEq] at h
      subst h
      simp [normalizeListWith, renameValueList]
  | cons v vs ih =>
      intro arr h
      simp only [normalizeListWith, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      simp only [renameValueList, normalizeListWith, bind_eq_ok]
      refine ⟨_, hfg _ _ hhead, _, ih htail, ?_⟩
      simp [renameValueList_eq_map]

theorem normalizeFieldsWith_ren {f g : Ty → GoValue → Except GoError GoValue}
    (hfg : ∀ ty v r, f ty v = .ok r →
      g ty (renameValue ρ v) = .ok (renameValue ρ r)) :
    ∀ {fds : List FieldDef} {l : List (String × GoValue)}
      {arr : Array (String × GoValue)},
      normalizeFieldsWith f fds l = .ok arr →
      normalizeFieldsWith g fds (renameValueFields ρ l)
        = .ok ((renameValueFields ρ arr.toList).toArray) := by
  intro fds
  induction fds with
  | nil =>
      intro l arr h
      simp only [normalizeFieldsWith, pure_eq_ok, Except.ok.injEq] at h
      subst h
      cases l <;> simp [normalizeFieldsWith, renameValueFields]
  | cons fd rest ih =>
      intro l arr h
      cases l with
      | nil =>
          simp only [normalizeFieldsWith, pure_eq_ok, Except.ok.injEq] at h
          subst h
          simp [normalizeFieldsWith, renameValueFields]
      | cons p ps =>
          obtain ⟨pn, pv⟩ := p
          simp only [normalizeFieldsWith] at h
          split at h
          · simp [Bind.bind, Except.bind] at h
          · rename_i hname
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
            obtain ⟨tail, htail, rest', hrest, rfl⟩ := h
            simp only [renameValueFields, normalizeFieldsWith]
            rw [if_neg hname]
            simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
            refine ⟨_, hfg _ _ _ htail, _, ih hrest, ?_⟩
            simp [renameValueFields_eq_map]

private theorem renamedFields_isEmpty (l : Array (String × GoValue)) :
    ((renameValueFields ρ l.toList).toArray).isEmpty = l.isEmpty := by
  simp [Array.isEmpty, renameValueFields_length]

theorem normalizeStructValueWith_ren {f g : Ty → GoValue → Except GoError GoValue}
    (hfg : ∀ ty v r, f ty v = .ok r →
      g ty (renameValue ρ v) = .ok (renameValue ρ r))
    {name : TypeId} {fields : Array FieldDef} {v r : GoValue}
    (h : normalizeStructValueWith f name fields v = .ok r) :
    normalizeStructValueWith g name fields (renameValue ρ v)
      = .ok (renameValue ρ r) := by
  cases v
  case struct actual fieldsValue =>
    simp only [normalizeStructValueWith] at h
    simp only [renameValue, normalizeStructValueWith]
    by_cases hne : (actual != name) = true
    · rw [if_pos hne] at h
      rw [if_pos hne]
      by_cases hesc : emptyStructAssignable actual name fields fieldsValue = true
      · rw [if_pos hesc] at h
        simp only [pure_eq_ok, Except.ok.injEq] at h
        subst h
        rw [if_pos (show emptyStructAssignable actual name fields
            ((renameValueFields ρ fieldsValue.toList).toArray) = true by
          simp only [emptyStructAssignable, Bool.and_eq_true] at hesc ⊢
          exact ⟨⟨hesc.1.1, hesc.1.2⟩, by
            rw [renamedFields_isEmpty]; exact hesc.2⟩)]
        simp [renameValue, renameValueFields]
      · rw [if_neg hesc] at h
        simp [Bind.bind, Except.bind] at h
    · rw [if_neg hne] at h
      rw [if_neg hne]
      by_cases hsz : (fieldsValue.size != fields.size) = true
      · rw [if_pos hsz] at h
        simp [Bind.bind, Except.bind] at h
      · rw [if_neg hsz] at h
        rw [if_neg (show ¬((((renameValueFields ρ fieldsValue.toList).toArray).size
            != fields.size) = true) by
          simp only [List.size_toArray, renameValueFields_length,
            Array.length_toList]
          exact hsz)]
        rw [map_eq_ok] at h
        obtain ⟨fs, hfs, rfl⟩ := h
        rw [map_eq_ok]
        exact ⟨_, normalizeFieldsWith_ren ρ hfg (by simpa using hfs),
          by simp [renameValue]⟩
  all_goals simp [normalizeStructValueWith] at h

/-! ### The normalizer itself -/

theorem normalizeValueForTyFuel_ren (htypes : σF.types = σ.types) :
    ∀ (fuel : Nat) {ty : Ty} {v r : GoValue},
      normalizeValueForTyFuel fuel σ ty v = .ok r →
      normalizeValueForTyFuel fuel σF ty (renameValue ρ v) = .ok (renameValue ρ r) := by
  intro fuel
  induction fuel with
  | zero => intro ty v r h; simp [normalizeValueForTyFuel] at h
  | succ n ih =>
      intro ty v r h
      cases ty with
      | int kind =>
          cases v <;> simp only [normalizeValueForTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [normalizeValueForTyFuel, renameValue])
      | float kind =>
          cases v <;> simp only [normalizeValueForTyFuel] at h <;>
            first
            | (simp at h; done)
            | skip
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq] at h
            subst h
            rename_i hk
            simp only [normalizeValueForTyFuel, renameValue]
            rw [if_pos hk]
            rfl
          · simp at h
      | array length elem =>
          cases v <;> simp only [normalizeValueForTyFuel] at h <;>
            first
            | (simp at h; done)
            | skip
          rename_i vs
          split at h
          · simp [Bind.bind, Except.bind] at h
          · rename_i hsz
            rw [map_eq_ok] at h
            obtain ⟨arr, harr, rfl⟩ := h
            simp only [normalizeValueForTyFuel, renameValue]
            rw [if_neg (by
              simp only [ne_eq, List.size_toArray, renameValueList_length,
                Array.length_toList]
              simpa using hsz)]
            rw [map_eq_ok]
            exact ⟨_, normalizeListWith_ren ρ (fun v r hv => ih hv)
              (by simpa using harr), by simp [renameValue]⟩
      | interface id =>
          simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
          subst h
          simp [normalizeValueForTyFuel]
      | funcType ps rs _ =>
          cases v <;> simp only [normalizeValueForTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [normalizeValueForTyFuel, renameValue])
      | chan dir elem =>
          cases v <;> simp only [normalizeValueForTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [normalizeValueForTyFuel, renameValue])
      | sync kind =>
          cases v <;> simp only [normalizeValueForTyFuel] at h <;>
            first
            | (simp at h; done)
            | skip
          split at h
          · simp only [pure_eq_ok, Except.ok.injEq] at h
            subst h
            rename_i hp
            simp only [normalizeValueForTyFuel, renameValue]
            rw [if_pos hp]
            rfl
          · simp at h
      | defined name =>
          simp only [normalizeValueForTyFuel, htypes] at h ⊢
          cases hlook : TypeEnv.lookup σ.types name with
          | none => rw [hlook] at h; simp at h
          | some td =>
              rw [hlook] at h
              cases td with
              | alias target => exact ih h
              | defined target => exact ih h
              | struct fields =>
                  exact normalizeStructValueWith_ren ρ (fun ty v r hv => ih hv) h
              | interfaceDef ms => simp at h
              | unsupported f => simp at h
      | unsupported f => simp [normalizeValueForTyFuel] at h
      | bool =>
          simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
          subst h; simp [normalizeValueForTyFuel]
      | string =>
          simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
          subst h; simp [normalizeValueForTyFuel]
      | slice elem =>
          simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
          subst h; simp [normalizeValueForTyFuel]
      | map kt vt =>
          simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
          subst h; simp [normalizeValueForTyFuel]
      | pointer elem =>
          simp only [normalizeValueForTyFuel, pure_eq_ok, Except.ok.injEq] at h
          subst h; simp [normalizeValueForTyFuel]

theorem normalizeValueForTy_ren (htypes : σF.types = σ.types)
    {ty : Ty} {v r : GoValue}
    (h : normalizeValueForTy σ ty v = .ok r) :
    normalizeValueForTy σF ty (renameValue ρ v) = .ok (renameValue ρ r) := by
  rw [normalizeValueForTy] at h ⊢
  exact normalizeValueForTyFuel_ren ρ htypes _ h

end Normalize

/-! ## `isNormalForTy` is renaming-invariant -/

section IsNormal

private theorem isNormalListWith_ren {f g : GoValue → Bool}
    (hfg : ∀ v, f (renameValue ρ v) = g v) :
    ∀ l : List GoValue,
      isNormalListWith f (renameValueList ρ l) = isNormalListWith g l := by
  intro l
  induction l with
  | nil => rfl
  | cons v vs ih => simp [renameValueList, isNormalListWith, hfg, ih]

private theorem isNormalFieldsWith_ren {f g : Ty → GoValue → Bool}
    (hfg : ∀ ty v, f ty (renameValue ρ v) = g ty v) :
    ∀ (fds : List FieldDef) (l : List (String × GoValue)),
      isNormalFieldsWith f fds (renameValueFields ρ l)
        = isNormalFieldsWith g fds l := by
  intro fds
  induction fds with
  | nil => intro l; cases l <;> rfl
  | cons fd rest ih =>
      intro l
      cases l with
      | nil => rfl
      | cons p ps =>
          obtain ⟨pn, pv⟩ := p
          simp [renameValueFields, isNormalFieldsWith, hfg, ih]

theorem isNormalForTyFuel_ren :
    ∀ (fuel : Nat) (types : TypeEnv) (ty : Ty) (v : GoValue),
      isNormalForTyFuel fuel types ty (renameValue ρ v)
        = isNormalForTyFuel fuel types ty v := by
  intro fuel
  induction fuel with
  | zero => intro types ty v; rfl
  | succ n ih =>
      intro types ty v
      cases ty with
      | int kind => cases v <;> simp [isNormalForTyFuel, renameValue]
      | float kind => cases v <;> simp [isNormalForTyFuel, renameValue]
      | array length elem =>
          cases v <;> simp [isNormalForTyFuel, renameValue,
            renameValueList_length,
            isNormalListWith_ren ρ (fun v => ih types elem v)]
      | interface id => cases v <;> simp [isNormalForTyFuel, renameValue]
      | funcType ps rs _ => cases v <;> simp [isNormalForTyFuel, renameValue]
      | chan dir elem => cases v <;> simp [isNormalForTyFuel, renameValue]
      | sync kind => cases v <;> simp [isNormalForTyFuel, renameValue]
      | defined name =>
          simp only [isNormalForTyFuel]
          cases TypeEnv.lookup types name with
          | none => rfl
          | some td =>
              cases td with
              | alias target => exact ih types target v
              | defined target => exact ih types target v
              | struct fields =>
                  cases v <;> simp [renameValue, renameValueFields_length,
                    isNormalFieldsWith_ren ρ (fun ty v => ih types ty v)]
              | interfaceDef ms => rfl
              | unsupported f => rfl
      | unsupported f => rfl
      | bool => cases v <;> simp [isNormalForTyFuel, renameValue]
      | string => cases v <;> simp [isNormalForTyFuel, renameValue]
      | slice elem => cases v <;> simp [isNormalForTyFuel, renameValue]
      | map kt vt => cases v <;> simp [isNormalForTyFuel, renameValue]
      | pointer elem => cases v <;> simp [isNormalForTyFuel, renameValue]

theorem isNormalForTy_ren (types : TypeEnv) (ty : Ty) (v : GoValue) :
    isNormalForTy types ty (renameValue ρ v) = isNormalForTy types ty v := by
  rw [isNormalForTy, isNormalForTy]
  exact isNormalForTyFuel_ren ρ _ types ty v

end IsNormal

/-! ## `defaultValue`: state-congruent and loc-free -/

section Defaults

variable {σ σF : ExecState}

theorem defaultValueFuel_congr (htypes : σF.types = σ.types) :
    ∀ fuel : Nat, defaultValueFuel fuel σF = defaultValueFuel fuel σ := by
  intro fuel
  induction fuel with
  | zero => funext ty; rfl
  | succ n ih => funext ty; cases ty <;> simp [defaultValueFuel, htypes, ih]

theorem defaultValue_congr (htypes : σF.types = σ.types) (ty : Ty) :
    defaultValue σF ty = defaultValue σ ty := by
  rw [defaultValue, defaultValue, defaultValueFuel_congr htypes]

theorem defaultValue_ren_id {ty : Ty} {v : GoValue}
    (h : defaultValue σ ty = .ok v) : renameValue ρ v = v :=
  renameValue_locFree ρ v (defaultValue_locSup h)

/-- The composite the arm induction consumes: framed `defaultValue`
answers identically and its value is renaming-inert. -/
theorem defaultValue_ren (htypes : σF.types = σ.types) {ty : Ty} {v : GoValue}
    (h : defaultValue σ ty = .ok v) :
    defaultValue σF ty = .ok (renameValue ρ v) := by
  rw [defaultValue_congr htypes, h, defaultValue_ren_id ρ h]

end Defaults

/-! ## `convertValueToTy` -/

section Convert

variable {σ σF : ExecState}

private theorem convert_float_int_ren {σ σF : ExecState} {fuel : Nat}
    {kind : IntKind} {bits : Nat} {fk : FloatKind} {r : GoValue}
    (h : convertValueToTyFuel fuel σ (.int kind) (.float bits fk) = .ok r) :
    convertValueToTyFuel fuel σF (.int kind)
      (renameValue ρ (.float bits fk)) = .ok (renameValue ρ r) := by
  have hr : renameValue ρ r = r := renameValue_locFree ρ r (by
    have hle := convertValueToTyFuel_locSup fuel h
    simpa [GoValue.locSup] using hle)
  have hbody : convertValueToTyFuel fuel σF (Ty.int kind)
      (.float bits fk) = convertValueToTyFuel fuel σ (Ty.int kind)
        (.float bits fk) := by
    cases fuel <;> rfl
  have hv : renameValue ρ (GoValue.float bits fk) = .float bits fk := by
    simp [renameValue]
  rw [hv, hbody, h, hr]

theorem convertValueToTyFuel_ren (htypes : σF.types = σ.types) :
    ∀ (fuel : Nat) {ty : Ty} {v r : GoValue},
      convertValueToTyFuel fuel σ ty v = .ok r →
      convertValueToTyFuel fuel σF ty (renameValue ρ v) = .ok (renameValue ρ r) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v r h
      cases ty with
      | defined name => simp [convertValueToTyFuel] at h
      | int kind =>
          cases v
          case int val k =>
            simp only [convertValueToTyFuel, pure_eq_ok, Except.ok.injEq] at h
            subst h
            simp [convertValueToTyFuel, renameValue]
          case float bits fk => exact convert_float_int_ren ρ h
          all_goals simp [convertValueToTyFuel] at h
      | float kind =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue]
               done)
            | skip
          · -- float / float kind dispatch
            rename_i bits fk
            cases kind <;> cases fk <;>
              simp_all only [convertValueToTyFuel, pure_eq_ok, Except.ok.injEq] <;>
              (subst h; simp [convertValueToTyFuel, renameValue])
      | string =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | pointer elem =>
          cases v <;>
            first
            | (simp only [convertValueToTyFuel] at h;
               first
               | (simp at h; done)
               | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
                  simp [convertValueToTyFuel, renameValue]))
            | -- slice operand (triage L2a): elem dispatch, panic or
              -- unsupported only — no ok.
              (cases elem <;> simp only [convertValueToTyFuel] at h <;>
                first
                | (simp at h; done)
                | (split at h <;> simp at h))
      | slice elem =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | map kt vt =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | chan dir elem =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | funcType ps rs _ =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | interface id =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | bool => simp [convertValueToTyFuel] at h
      | unsupported f => simp [convertValueToTyFuel] at h
      | array length elem =>
          -- slice operand (triage L2a): panic or unsupported — no ok.
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (split at h <;> simp at h)
      | sync kind => simp [convertValueToTyFuel] at h
  | succ n ih =>
      intro ty v r h
      cases ty with
      | defined name =>
          simp only [convertValueToTyFuel, htypes] at h ⊢
          cases hlook : TypeEnv.lookup σ.types name with
          | none => rw [hlook] at h; simp at h
          | some td =>
              rw [hlook] at h
              cases td with
              | alias target => exact ih h
              | defined target => exact ih h
              | struct targetFields =>
                  cases v <;> (try (simp at h; done))
                  rename_i actual actualFields
                  simp only at h ⊢
                  by_cases htag : (actual == name) = true
                  · rw [if_pos htag] at h
                    simp only [pure_eq_ok, Except.ok.injEq] at h
                    subst h
                    simp only [renameValue]
                    rw [if_pos htag]
                    rfl
                  · rw [if_neg htag] at h
                    simp only [renameValue]
                    rw [if_neg htag]
                    cases hlook2 : TypeEnv.lookup σ.types actual with
                    | none => rw [hlook2] at h; simp at h
                    | some td2 =>
                        rw [hlook2] at h
                        cases td2 with
                        | struct sourceFields =>
                            by_cases hsf : (sourceFields == targetFields) = true
                            · simp only [hsf, if_true] at h
                              simp only [pure_eq_ok, Except.ok.injEq] at h
                              subst h
                              simp [hsf, renameValue]
                            · simp [hsf] at h
                        | alias t2 => simp at h
                        | defined t2 => simp at h
                        | interfaceDef ms2 => simp at h
                        | unsupported f2 => simp at h
              | interfaceDef ms => simp at h
              | unsupported f => simp at h
      | int kind =>
          cases v
          case int val k =>
            simp only [convertValueToTyFuel, pure_eq_ok, Except.ok.injEq] at h
            subst h
            simp [convertValueToTyFuel, renameValue]
          case float bits fk => exact convert_float_int_ren ρ h
          all_goals simp [convertValueToTyFuel] at h
      | float kind =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue]
               done)
            | skip
          · rename_i bits fk
            cases kind <;> cases fk <;>
              simp_all only [convertValueToTyFuel, pure_eq_ok, Except.ok.injEq] <;>
              (subst h; simp [convertValueToTyFuel, renameValue])
      | string =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | pointer elem =>
          cases v <;>
            first
            | (simp only [convertValueToTyFuel] at h;
               first
               | (simp at h; done)
               | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
                  simp [convertValueToTyFuel, renameValue]))
            | -- slice operand (triage L2a): elem dispatch, panic or
              -- unsupported only — no ok.
              (cases elem <;> simp only [convertValueToTyFuel] at h <;>
                first
                | (simp at h; done)
                | (split at h <;> simp at h))
      | slice elem =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | map kt vt =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | chan dir elem =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | funcType ps rs _ =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | interface id =>
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (simp only [pure_eq_ok, Except.ok.injEq] at h; subst h;
               simp [convertValueToTyFuel, renameValue])
      | bool => simp [convertValueToTyFuel] at h
      | unsupported f => simp [convertValueToTyFuel] at h
      | array length elem =>
          -- slice operand (triage L2a): panic or unsupported — no ok.
          cases v <;> simp only [convertValueToTyFuel] at h <;>
            first
            | (simp at h; done)
            | (split at h <;> simp at h)
      | sync kind => simp [convertValueToTyFuel] at h

theorem convertValueToTy_ren (htypes : σF.types = σ.types)
    {ty : Ty} {v r : GoValue}
    (h : convertValueToTy σ ty v = .ok r) :
    convertValueToTy σF ty (renameValue ρ v) = .ok (renameValue ρ r) := by
  rw [convertValueToTy] at h ⊢
  exact convertValueToTyFuel_ren ρ htypes _ h

/-- Panic transfer for the conversion kernel (triage L2a, 2026-08-19):
the ONLY panicking arms are the slice→array(-pointer) length checks,
whose message depends on the slice's `len` and the target length alone
— both rename-invariant (`renameValue` rewrites a slice's BASE only) —
and whose dispatch depends only on the types map (equal by `htypes`).
Every other arm errs stuck/unsupported or recurses through the
`defined` chain; this replaces the retired `convertValueToTy_noPanic`
in `arm_convert`. -/
theorem convertValueToTyFuel_panic_ren (htypes : σF.types = σ.types) :
    ∀ (fuel : Nat) {ty : Ty} {v : GoValue} {m : String},
      convertValueToTyFuel fuel σ ty v = .error (.panic m) →
      convertValueToTyFuel fuel σF ty (renameValue ρ v) = .error (.panic m) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v m h
      cases ty <;> cases v <;>
        first
        | (simp [convertValueToTyFuel] at h; done)
        | (simp only [convertValueToTyFuel] at h;
           (repeat' split at h) <;> simp_all; done)
        | skip
      case array.slice n elem sl =>
        simp only [convertValueToTyFuel] at h
        simp only [renameValue, convertValueToTyFuel]
        split at h
        · rename_i hlt
          rw [if_pos hlt]
          exact h
        · simp at h
      case pointer.slice elem sl =>
        cases elem <;>
          first
          | (simp [convertValueToTyFuel] at h; done)
          | skip
        case array n e =>
          simp only [convertValueToTyFuel] at h
          simp only [renameValue, convertValueToTyFuel]
          split at h
          · rename_i hlt
            rw [if_pos hlt]
            exact h
          · simp at h
  | succ n ih =>
      intro ty v m h
      cases ty with
      | defined name =>
          simp only [convertValueToTyFuel, htypes] at h ⊢
          cases hlook : TypeEnv.lookup σ.types name with
          | none => rw [hlook] at h; simp at h
          | some td =>
              rw [hlook] at h
              cases td with
              | alias target => exact ih h
              | defined target => exact ih h
              | struct targetFields =>
                  cases v <;> (try (simp at h; done))
                  rename_i actual actualFields
                  simp only at h
                  (repeat' split at h) <;> simp_all
              | interfaceDef x => simp at h
              | unsupported f => simp at h
      | array n' elem =>
          cases v <;>
            first
            | (simp [convertValueToTyFuel] at h; done)
            | skip
          case slice sl =>
            simp only [convertValueToTyFuel] at h
            simp only [renameValue, convertValueToTyFuel]
            split at h
            · rename_i hlt
              rw [if_pos hlt]
              exact h
            · simp at h
      | pointer elem =>
          cases v <;>
            first
            | (simp [convertValueToTyFuel] at h; done)
            | skip
          case slice sl =>
            cases elem <;>
              first
              | (simp [convertValueToTyFuel] at h; done)
              | skip
            case array n' e =>
              simp only [convertValueToTyFuel] at h
              simp only [renameValue, convertValueToTyFuel]
              split at h
              · rename_i hlt
                rw [if_pos hlt]
                exact h
              · simp at h
      | _ =>
          cases v <;>
            first
            | (simp [convertValueToTyFuel] at h; done)
            | (simp only [convertValueToTyFuel] at h;
               (repeat' split at h) <;> simp_all; done)

theorem convertValueToTy_panic_ren (htypes : σF.types = σ.types)
    {ty : Ty} {v : GoValue} {m : String}
    (h : convertValueToTy σ ty v = .error (.panic m)) :
    convertValueToTy σF ty (renameValue ρ v) = .error (.panic m) := by
  rw [convertValueToTy] at h ⊢
  exact convertValueToTyFuel_panic_ren ρ htypes _ h

end Convert

end GoLean.Frame
