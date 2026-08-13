import GoLeanProofs.Frame.Values

/-!
# The executable frame theorem, module 5: slice-shape ops and builders

The pure slice-shape operations (`validateSlice`, `sliceIndexLoc`,
`sliceFromSlice`, `sliceFromArray`, `stringSlice`, `stringByteGet`,
`arrayIndexNat`, `arrayGet`, `arraySet`) commute with the address
renaming as `ExSim` facts — bounds panics carry int-only messages, so
the panic clause transfers verbatim. The value builders
(`buildStructFields`/`buildStructValue`, `buildArrayValue`,
`buildDefaultArrayValue`, `buildAppendBackingValue`, `typeAssertValue`)
are ok-transfer (`_ren`) facts: the state enters only through the
static tables, so the framed side is any state with equal tables.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

variable (ρ : Nat → Nat)

/-- Keyed-entry renaming for `buildArrayValue`'s argument shape: keys
unchanged, values renamed (what `applyStrictOp`'s arrayLit arm produces). -/
def renameValueEntriesKeyed (args : Array (Int × GoValue)) : Array (Int × GoValue) :=
  (args.toList.map (fun p => (p.1, renameValue ρ p.2))).toArray

/-! ## Array/list bridges for renamed arrays -/

private theorem renArray_size (values : Array GoValue) :
    ((renameValueList ρ values.toList).toArray).size = values.size := by
  simp [renameValueList_eq_map]

private theorem renArray_getElem? (values : Array GoValue) (i : Nat) :
    ((renameValueList ρ values.toList).toArray)[i]?
      = (values[i]?).map (renameValue ρ) := by
  simp [renameValueList_eq_map, List.getElem?_toArray, List.getElem?_map,
    Array.getElem?_toList]

private theorem renArray_push (values : Array GoValue) (d : GoValue) :
    ((renameValueList ρ values.toList).toArray).push (renameValue ρ d)
      = (renameValueList ρ (values.push d).toList).toArray := by
  simp [renameValueList_eq_map]

private theorem renArray_set! (values : Array GoValue) (i : Nat) (c : GoValue) :
    ((renameValueList ρ values.toList).toArray).set! i (renameValue ρ c)
      = (renameValueList ρ (values.set! i c).toList).toArray := by
  rw [Array.set!, Array.set!]
  apply Array.toList_inj.mp
  simp [renameValueList_eq_map, Array.toList_setIfInBounds, List.map_set]

/-! ## `ExSim` utilities -/

/-- Same computation on both sides: only the ok-payload condition is owed
(the panic clause is `rfl`, other errors are vacuous). -/
private theorem exsim_self {α : Type} {R : α → α → Prop} {x : Except GoError α}
    (h : ∀ a, x = .ok a → R a a) : ExSim R x x := by
  cases x with
  | ok a => exact h a rfl
  | error e => cases e <;> first | rfl | trivial

/-- Functional ok-transfer plus a no-panic guarantee yields the `ExSim`. -/
private theorem exsim_of_ren {α β : Type} {f : α → β}
    {x : Except GoError α} {y : Except GoError β}
    (hok : ∀ a, x = .ok a → y = .ok (f a))
    (hnp : ∀ m, x ≠ .error (.panic m)) :
    ExSim (fun a b => b = f a) x y := by
  cases x with
  | ok a => rw [hok a rfl]; exact ExSim.ok rfl
  | error e =>
      cases e with
      | panic m => exact absurd rfl (hnp m)
      | _ => trivial

private theorem indexOutOfRangePanic_ne_ok {α : Type} {i : Int} {n : Nat} {a : α} :
    indexOutOfRangePanic i n ≠ .ok a := by
  unfold indexOutOfRangePanic; split <;> simp

private theorem bind_no_ok {α β : Type} {x : Except GoError α}
    {f : α → Except GoError β} {b : β}
    (hx : ∀ a, x ≠ .ok a) (h : x >>= f = .ok b) : False := by
  cases hx' : x with
  | ok a => exact hx a hx'
  | error e => rw [hx'] at h; simp [Bind.bind, Except.bind] at h

/-! ## No-panic facts (for full-`ExSim` statements over `stuck`-only ops) -/

private theorem map_ne_panic {α β : Type} {g : α → β} {x : Except GoError α}
    (hx : ∀ m, x ≠ .error (.panic m)) (m : String) :
    g <$> x ≠ .error (.panic m) := by
  intro h
  cases hx' : x with
  | ok a => rw [hx'] at h; simp [Functor.map, Except.map] at h
  | error e =>
      rw [hx'] at h
      simp only [Functor.map, Except.map, Except.error.injEq] at h
      exact hx m (by rw [hx', h])

private theorem bind_ne_panic {α β : Type} {x : Except GoError α}
    {f : α → Except GoError β}
    (hx : ∀ m, x ≠ .error (.panic m))
    (hf : ∀ a m, f a ≠ .error (.panic m)) (m : String) :
    x >>= f ≠ .error (.panic m) := by
  intro h
  cases hx' : x with
  | ok a => rw [hx'] at h; exact hf a m (by simpa [Bind.bind, Except.bind] using h)
  | error e =>
      rw [hx'] at h
      simp only [Bind.bind, Except.bind, Except.error.injEq] at h
      exact hx m (by rw [hx', h])

/-- `coerceStoredValue` fails only `stuck` — never a panic (its `ExSim`
panic clause is therefore vacuous). -/
private theorem coerceStoredValue_ne_panic :
    ∀ old v : GoValue, ∀ m, coerceStoredValue old v ≠ .error (.panic m) := by
  refine fun old v => coerceStoredValue.induct
    (motive_1 := fun old v => ∀ m, coerceStoredValue old v ≠ .error (.panic m))
    (motive_2 := fun a b => ∀ m, coerceStruct a b ≠ .error (.panic m))
    (motive_3 := fun a b => ∀ m, coerceArray a b ≠ .error (.panic m))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ old v
  · intro _ _ _ _ m h; simp [coerceStoredValue] at h
  · intro _ _ _ _ hk m h
    simp only [coerceStoredValue] at h
    rw [if_pos hk] at h
    simp at h
  · intro _ _ _ _ hk m h
    simp only [coerceStoredValue] at h
    rw [if_neg hk] at h
    simp at h
  · intro _ _ hne m h
    simp only [coerceStoredValue] at h
    rw [if_pos hne] at h
    simp at h
  · intro o n hne ih m h
    simp only [coerceStoredValue] at h
    rw [if_neg hne] at h
    exact map_ne_panic (fun m' => ih m') m h
  · intro _ _ _ _ hne m h
    simp only [coerceStoredValue] at h
    rw [if_pos hne] at h
    simp at h
  · intro _ _ _ _ hne hsz m h
    simp only [coerceStoredValue] at h
    rw [if_neg hne, if_pos hsz] at h
    simp at h
  · intro _ _ _ _ hne hsz ih m h
    simp only [coerceStoredValue] at h
    rw [if_neg hne, if_neg hsz] at h
    exact map_ne_panic (fun m' => ih m') m h
  · intro t v hint hfloat harr hstruct m h
    rw [coerceStoredValue.eq_def] at h
    split at h
    · exact (hint _ _ _ _ rfl rfl).elim
    · exact (hfloat _ _ _ _ rfl rfl).elim
    · exact (harr _ _ rfl rfl).elim
    · exact (hstruct _ _ _ _ rfl rfl).elim
    · simp at h
  · intro _ _ _ _ ih1 ih3 m h
    simp only [coerceArray] at h
    exact bind_ne_panic ih1
      (fun a => bind_ne_panic ih3 (fun b m' => by simp)) m h
  · intro t x hnc m h
    rw [coerceArray.eq_def] at h
    split at h
    · exact (hnc _ _ _ _ rfl rfl).elim
    · simp at h
  · intro _ _ _ _ _ _ hname _ _ m h
    simp only [coerceStruct] at h
    rw [if_pos hname] at h
    simp [Bind.bind, Except.bind] at h
  · intro _ _ _ _ _ _ hname ih1 ih2 m h
    simp only [coerceStruct] at h
    rw [if_neg hname] at h
    simp only [pure_bind] at h
    exact bind_ne_panic ih1
      (fun a => bind_ne_panic ih2 (fun b m' => by simp)) m h
  · intro t x hnc m h
    rw [coerceStruct.eq_def] at h
    split at h
    · exact (hnc _ _ _ _ _ _ rfl rfl).elim
    · simp at h

/-! ## Slice-shape operations -/

private theorem validateSlice_ren_eq (base : Option Loc) (off len cap : Nat) :
    validateSlice ⟨base.map (renameLoc ρ), off, len, cap⟩
      = validateSlice ⟨base, off, len, cap⟩ := by
  cases base <;> simp [validateSlice, Option.map]

theorem validateSlice_ren {sl : SliceValue} (h : validateSlice sl = .ok ()) :
    validateSlice { sl with base := sl.base.map (renameLoc ρ) } = .ok () := by
  obtain ⟨base, off, len, cap⟩ := sl
  show validateSlice ⟨base.map (renameLoc ρ), off, len, cap⟩ = .ok ()
  rw [validateSlice_ren_eq]
  exact h

theorem sliceIndexLoc_sim (sl : SliceValue) (i : Int) :
    ExSim (fun l lF => lF = renameLoc ρ l)
      (sliceIndexLoc sl i)
      (sliceIndexLoc { sl with base := sl.base.map (renameLoc ρ) } i) := by
  obtain ⟨base, off, len, cap⟩ := sl
  show ExSim _ (sliceIndexLoc ⟨base, off, len, cap⟩ i)
      (sliceIndexLoc ⟨base.map (renameLoc ρ), off, len, cap⟩ i)
  unfold sliceIndexLoc
  refine ExSim.bind (R := Eq) ?_ ?_
  · rw [validateSlice_ren_eq]; exact ExSim.refl _
  · intro _ _ _
    refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
    intro iN iN' hi
    subst hi
    refine ExSim.ite_congr (fun _ => ?_) (fun _ => ?_)
    · cases base with
      | some b => exact ExSim.ok rfl
      | none => exact ExSim.stuck'
    · exact exsim_self fun a ha => absurd ha indexOutOfRangePanic_ne_ok

theorem sliceFromSlice_sim (sl : SliceValue) (lo hi : Int) (m : Option Int) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (sliceFromSlice sl lo hi m)
      (sliceFromSlice { sl with base := sl.base.map (renameLoc ρ) } lo hi m) := by
  obtain ⟨base, off, len, cap⟩ := sl
  show ExSim _ (sliceFromSlice ⟨base, off, len, cap⟩ lo hi m)
      (sliceFromSlice ⟨base.map (renameLoc ρ), off, len, cap⟩ lo hi m)
  unfold sliceFromSlice
  refine ExSim.bind (R := Eq) ?_ ?_
  · rw [validateSlice_ren_eq]; exact ExSim.refl _
  · intro _ _ _
    cases m with
    | none =>
        refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
        intro p p' hp
        subst hp
        obtain ⟨lo', hi'⟩ := p
        exact ExSim.pure' (by simp [renameValue])
    | some mx =>
        refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
        intro mx' mx'' hmx
        subst hmx
        refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
        intro p p' hp
        subst hp
        obtain ⟨lo', hi'⟩ := p
        exact ExSim.pure' (by simp [renameValue])

theorem sliceFromArray_sim (base : Loc) (len : Nat) (lo hi : Int) (m : Option Int) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (sliceFromArray base len lo hi m)
      (sliceFromArray (renameLoc ρ base) len lo hi m) := by
  unfold sliceFromArray
  cases m with
  | none =>
      refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
      intro p p' hp
      subst hp
      obtain ⟨lo', hi'⟩ := p
      exact ExSim.pure' (by simp [renameValue, Option.map])
  | some mx =>
      refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
      intro mx' mx'' hmx
      subst hmx
      refine ExSim.bind (R := Eq) (ExSim.refl _) ?_
      intro p p' hp
      subst hp
      obtain ⟨lo', hi'⟩ := p
      exact ExSim.pure' (by simp [renameValue, Option.map])

theorem stringSlice_ren_sim (gs : GoString) (lo hi : Int) (m : Option Int) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (stringSlice gs lo hi m) (stringSlice gs lo hi m) := by
  refine exsim_self fun v hv => ?_
  exact (renameValue_locFree ρ v (stringSlice_locSup hv)).symm

theorem stringByteGet_sim (gs : GoString) (i : Int) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (stringByteGet gs i) (stringByteGet gs i) := by
  refine exsim_self fun v hv => ?_
  unfold stringByteGet at hv
  split at hv
  · exact absurd hv (fun h => bind_no_ok (fun _ => indexOutOfRangePanic_ne_ok) h)
  · simp only [pure_bind] at hv
    split at hv
    · simp only [pure_eq_ok, Except.ok.injEq] at hv
      subst hv
      simp [renameValue]
    · exact absurd hv indexOutOfRangePanic_ne_ok

/-! ## Array element operations -/

theorem arrayIndexNat_sim (values : Array GoValue) (i : Int) :
    ExSim Eq (arrayIndexNat values i)
      (arrayIndexNat ((renameValueList ρ values.toList).toArray) i) := by
  unfold arrayIndexNat
  rw [renArray_size]
  exact ExSim.refl _

theorem arrayGet_sim (values : Array GoValue) (i : Int) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (arrayGet values i)
      (arrayGet ((renameValueList ρ values.toList).toArray) i) := by
  unfold arrayGet
  refine ExSim.bind (arrayIndexNat_sim ρ values i) ?_
  intro j j' hj
  subst hj
  rw [renArray_getElem?, renArray_size]
  cases hv : values[j]? with
  | some v => exact ExSim.ok rfl
  | none => exact exsim_self fun a ha => absurd ha indexOutOfRangePanic_ne_ok

theorem arraySet_sim (values : Array GoValue) (i : Int) (v : GoValue) :
    ExSim (fun out outF => outF = (renameValueList ρ out.toList).toArray)
      (arraySet values i v)
      (arraySet ((renameValueList ρ values.toList).toArray) i (renameValue ρ v)) := by
  unfold arraySet
  refine ExSim.bind (arrayIndexNat_sim ρ values i) ?_
  intro j j' hj
  subst hj
  rw [renArray_getElem?, renArray_size]
  cases hv : values[j]? with
  | some old =>
      refine ExSim.bind
        (S := fun (out outF : Array GoValue) =>
          outF = (renameValueList ρ out.toList).toArray)
        (exsim_of_ren (f := renameValue ρ)
          (fun c hc => coerceStoredValue_ren ρ old v c hc)
          (coerceStoredValue_ne_panic old v)) ?_
      intro c c' hc
      subst hc
      exact ExSim.pure' (renArray_set! ρ values j c)
  | none => exact exsim_self fun a ha => absurd ha indexOutOfRangePanic_ne_ok

/-! ## `forIn` transport (the loop shape of the op-table builders)

Simulation counterpart of `StateWf`'s `forIn_list_inv`: a successful
canonical list-`forIn` transports to the framed loop over the
element-wise renamed list, with the accumulator related by a renaming
function throughout. -/

private def renStep {β β' : Type} (ren : β → β') : ForInStep β → ForInStep β'
  | .done b => .done (ren b)
  | .yield b => .yield (ren b)

private theorem forIn_list_ren {α α' β β' : Type} {T : α → α'} {ren : β → β'} :
    ∀ {l : List α} {f : α → β → Except GoError (ForInStep β)}
      {g : α' → β' → Except GoError (ForInStep β')} {b₀ bf : β}
      {l' : List α'} {b₀' : β'},
      (∀ a ∈ l, ∀ b r, f a b = .ok r → g (T a) (ren b) = .ok (renStep ren r)) →
      l' = l.map T → b₀' = ren b₀ →
      forIn l b₀ f = .ok bf →
      forIn l' b₀' g = .ok (ren bf) := by
  intro l
  induction l with
  | nil =>
      intro f g b₀ bf l' b₀' _ hl hb h
      subst hl hb
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [List.forIn_nil, pure, Except.pure]
  | cons a as ih =>
      intro f g b₀ bf l' b₀' hstep hl hb h
      subst hl hb
      rw [List.forIn_cons, bind_eq_ok] at h
      obtain ⟨r, hr, hrest⟩ := h
      rw [List.map_cons, List.forIn_cons, bind_eq_ok]
      refine ⟨renStep ren r, hstep a (by simp) b₀ r hr, ?_⟩
      cases r with
      | done b =>
          simp only [pure, Except.pure, Except.ok.injEq] at hrest
          subst hrest
          simp [renStep, pure, Except.pure]
      | yield b =>
          exact ih (fun a' ha' => hstep a' (by simp [ha'])) rfl rfl hrest

/-- Same index list on both sides (range loops). -/
private theorem forIn_list_ren_same {α β β' : Type} {ren : β → β'}
    {l : List α} {f : α → β → Except GoError (ForInStep β)}
    {g : α → β' → Except GoError (ForInStep β')} {b₀ bf : β} {b₀' : β'}
    (hstep : ∀ a ∈ l, ∀ b r, f a b = .ok r → g a (ren b) = .ok (renStep ren r))
    (hb : b₀' = ren b₀) (h : forIn l b₀ f = .ok bf) :
    forIn l b₀' g = .ok (ren bf) :=
  forIn_list_ren (T := id) hstep (by simp) hb h

/-! ## Builders (state enters via the static tables only) -/

section Builders

variable {σ σF : ExecState} (htypes : σF.types = σ.types)

private theorem renFields_size (fs : Array (String × GoValue)) :
    ((renameValueFields ρ fs.toList).toArray).size = fs.size := by
  simp [renameValueFields_eq_map]

include htypes

theorem buildStructFields_ren :
    ∀ {fds : List FieldDef} {vs : List GoValue} {arr : Array (String × GoValue)},
      buildStructFields σ fds vs = .ok arr →
      buildStructFields σF fds (renameValueList ρ vs)
        = .ok ((renameValueFields ρ arr.toList).toArray) := by
  intro fds
  induction fds with
  | nil =>
      intro vs arr h
      simp only [buildStructFields, pure_eq_ok, Except.ok.injEq] at h
      subst h
      cases vs <;> simp [buildStructFields, renameValueList, renameValueFields]
  | cons fd rest ih =>
      intro vs arr h
      cases vs with
      | nil =>
          simp only [buildStructFields, pure_eq_ok, Except.ok.injEq] at h
          subst h
          simp [buildStructFields, renameValueList, renameValueFields]
      | cons v vrest =>
          simp only [buildStructFields, bind_eq_ok, pure_eq_ok,
            Except.ok.injEq] at h
          obtain ⟨head, hhead, tail, htail, rfl⟩ := h
          simp only [renameValueList, buildStructFields, bind_eq_ok]
          refine ⟨_, normalizeValueForTy_ren ρ htypes hhead, _, ih htail, ?_⟩
          simp [renameValueFields_eq_map]

theorem buildStructValueFuel_ren :
    ∀ (fuel : Nat) {ty : Ty} {args : Array GoValue} {r : GoValue},
      buildStructValueFuel fuel σ ty args = .ok r →
      buildStructValueFuel fuel σF ty ((renameValueList ρ args.toList).toArray)
        = .ok (renameValue ρ r) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty args r h
      rw [buildStructValueFuel.eq_def] at h
      split at h <;> simp_all
  | succ n ih =>
      intro ty args r h
      cases ty with
      | defined name =>
          simp only [buildStructValueFuel, htypes] at h ⊢
          cases hlook : TypeEnv.lookup σ.types name with
          | none => rw [hlook] at h; simp at h
          | some td =>
              rw [hlook] at h
              cases td with
              | struct fields =>
                  dsimp only at h ⊢
                  by_cases hsz : (fields.size != args.size) = true
                  · rw [if_pos hsz] at h
                    simp [Bind.bind, Except.bind] at h
                  · rw [if_neg hsz] at h
                    rw [if_neg (show ¬((fields.size !=
                        ((renameValueList ρ args.toList).toArray).size) = true) by
                      rw [renArray_size]; exact hsz)]
                    simp only [pure_bind] at h ⊢
                    rw [map_eq_ok] at h
                    obtain ⟨fs, hfs, rfl⟩ := h
                    rw [map_eq_ok]
                    exact ⟨_, buildStructFields_ren ρ htypes (by simpa using hfs),
                      by simp [renameValue]⟩
              | alias target => exact ih h
              | defined target => simp at h
              | interfaceDef ms => simp at h
              | unsupported f => simp at h
      | unsupported f => simp [buildStructValueFuel] at h
      | _ => simp [buildStructValueFuel] at h

theorem buildStructValue_ren {ty : Ty} {args : Array GoValue} {r : GoValue}
    (h : buildStructValue σ ty args = .ok r) :
    buildStructValue σF ty ((renameValueList ρ args.toList).toArray)
      = .ok (renameValue ρ r) := by
  rw [buildStructValue] at h ⊢
  exact buildStructValueFuel_ren ρ htypes _ h

/-! ### Array builders (the `for`-loop pair) -/

theorem buildArrayValue_ren {len : Nat} {elem : Ty}
    {args : Array (Int × GoValue)} {r : GoValue}
    (h : buildArrayValue σ len elem args = .ok r) :
    buildArrayValue σF len elem (renameValueEntriesKeyed ρ args)
      = .ok (renameValue ρ r) := by
  unfold buildArrayValue at h ⊢
  simp only [bind_eq_ok] at h
  obtain ⟨vs₁, hvs₁, st, hloop, hfin⟩ := h
  simp only [pure_eq_ok, Except.ok.injEq] at hfin
  subst hfin
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hvs₁
  rw [← Array.forIn_toList] at hloop
  simp only [bind_eq_ok]
  refine ⟨(renameValueList ρ vs₁.toList).toArray, ?_,
    ⟨st.1, (renameValueList ρ st.2.toList).toArray⟩, ?_, by simp [renameValue]⟩
  · -- default-fill loop: same range, loc-free defaults, renamed accumulator
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    refine forIn_list_ren_same
      (ren := fun vs : Array GoValue => (renameValueList ρ vs.toList).toArray)
      ?_ (by simp [renameValueList]) hvs₁
    intro a ha b rr hr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨d, hd, _, rfl, hrr⟩ := hr
    subst hrr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
    exact ⟨_, defaultValue_ren ρ htypes hd, _, rfl,
      by simp [renStep, renArray_push]⟩
  · -- keyed-entry loop: keys unchanged, values renamed
    rw [← Array.forIn_toList]
    refine forIn_list_ren
      (T := fun p : Int × GoValue => (p.1, renameValue ρ p.2))
      (ren := fun st : MProd (Array Int) (Array GoValue) =>
        ⟨st.1, (renameValueList ρ st.2.toList).toArray⟩)
      ?_ (by simp [renameValueEntriesKeyed]) rfl hloop
    intro a ha b rr hr
    obtain ⟨key, value⟩ := a
    obtain ⟨seen, values⟩ := b
    split at hr
    · simp [Bind.bind, Except.bind] at hr
    · rename_i hnc
      split at hr
      · simp [Bind.bind, Except.bind] at hr
      · rename_i hneg
        split at hr
        · rename_i old hold
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
          obtain ⟨_, _, _, _, nv, hnv, c, hc, _, _, hrr⟩ := hr
          subst hrr
          dsimp only
          rw [if_neg hnc]
          simp only [pure_bind]
          rw [if_neg hneg]
          simp only [pure_bind]
          rw [renArray_getElem?, hold]
          simp only [Option.map_some]
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
          refine ⟨_, normalizeValueForTy_ren ρ htypes hnv,
            _, coerceStoredValue_ren ρ old nv c hc, ?_⟩
          simp [renStep, renArray_set!]
        · simp [Bind.bind, Except.bind] at hr

theorem buildDefaultArrayValue_ren {len : Nat} {elem : Ty} {r : GoValue}
    (h : buildDefaultArrayValue σ len elem = .ok r) :
    buildDefaultArrayValue σF len elem = .ok (renameValue ρ r) := by
  unfold buildDefaultArrayValue at h ⊢
  have hb := buildArrayValue_ren ρ htypes (args := #[]) h
  simpa [renameValueEntriesKeyed] using hb

theorem buildAppendBackingValue_ren {elem : Ty}
    {oldValues elemValues : Array GoValue} {newCap : Nat} {r : GoValue}
    (h : buildAppendBackingValue σ elem oldValues elemValues newCap = .ok r) :
    buildAppendBackingValue σF elem
      ((renameValueList ρ oldValues.toList).toArray)
      ((renameValueList ρ elemValues.toList).toArray) newCap
      = .ok (renameValue ρ r) := by
  unfold buildAppendBackingValue at h ⊢
  simp only [bind_eq_ok] at h
  obtain ⟨vs₁, hloop1, h⟩ := h
  rw [← Array.forIn_toList] at hloop1
  simp only [bind_eq_ok]
  refine ⟨(renameValueList ρ vs₁.toList).toArray, ?_, ?_⟩
  · -- normalize loop over the concatenated inputs
    rw [← Array.forIn_toList]
    refine forIn_list_ren (T := renameValue ρ)
      (ren := fun vs : Array GoValue => (renameValueList ρ vs.toList).toArray)
      ?_ (by simp [Array.toList_append, renameValueList_eq_map])
      (by simp [renameValueList]) hloop1
    intro a ha b rr hr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨nv, hnv, _, rfl, hrr⟩ := hr
    subst hrr
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
    exact ⟨_, normalizeValueForTy_ren ρ htypes hnv, _, rfl,
      by simp [renStep, renArray_push]⟩
  · rw [renArray_size]
    split at h
    · simp [Bind.bind, Except.bind] at h
    · rename_i hcap
      rw [if_neg hcap]
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨_, _, vs₂, hloop2, hr⟩ := h
      subst hr
      simp only [pure_bind]
      rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hloop2 ⊢
      simp only [bind_eq_ok]
      refine ⟨(renameValueList ρ vs₂.toList).toArray, ?_, by simp [renameValue]⟩
      refine forIn_list_ren_same
        (ren := fun vs : Array GoValue => (renameValueList ρ vs.toList).toArray)
        ?_ rfl hloop2
      intro a ha b rr hr
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
      obtain ⟨d, hd, _, rfl, hrr⟩ := hr
      subst hrr
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
      refine ⟨d, by rw [defaultValue_congr htypes]; exact hd, _, rfl, ?_⟩
      have hp := renArray_push ρ b d
      rw [defaultValue_ren_id ρ hd] at hp
      simp [renStep, hp]

/-! ### Type assertion -/

theorem typeAssertValue_ren
    (hmethods : σF.methods = σ.methods)
    (hfuncs : σF.functions = σ.functions)
    (hmsets : σF.methodSets = σ.methodSets)
    {v : GoValue} {ty : Ty} {r : GoValue} {b : Bool}
    (h : typeAssertValue σ v ty = .ok (r, b)) :
    typeAssertValue σF (renameValue ρ v) ty = .ok (renameValue ρ r, b) := by
  unfold typeAssertValue at h ⊢
  simp only [bind_eq_ok] at h
  obtain ⟨failed, hfailed, h⟩ := h
  simp only [bind_eq_ok]
  refine ⟨renameValue ρ failed, defaultValue_ren ρ htypes hfailed, ?_⟩
  cases v with
  | nil =>
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [renameValue]
  | interface dynTy inner =>
      simp only [renameValue]
      rw [resolveDefinedAliases_congr htypes]
      cases hres : resolveDefinedAliases σ ty with
      | interface iname =>
          rw [hres] at h
          simp only [bind_eq_ok] at h
          obtain ⟨bb, hbb, h⟩ := h
          simp only [bind_eq_ok]
          refine ⟨bb,
            by rw [dynamicImplementsInterface_congr htypes hmethods hfuncs hmsets]
               exact hbb, ?_⟩
          cases bb with
          | true =>
              simp only [if_true, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl⟩ := h
              simp [renameValue]
          | false =>
              simp only [if_false, pure_eq_ok, Except.ok.injEq,
                Prod.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl⟩ := h
              simp
      | _ =>
          rw [hres] at h
          simp only [canonicalTy_congr htypes] at *
          split at h <;>
            (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             simp_all)
  | _ => simp [renameValue] at h ⊢

/-! ### Assert-panic messages (loc-free on the reachable shapes) -/

theorem dynamicTypeNameForMessage_ren
    {v : GoValue} (hshape : v = .nil ∨ ∃ t i, v = .interface t i) :
    dynamicTypeNameForMessage σF (renameValue ρ v)
      = dynamicTypeNameForMessage σ v := by
  rcases hshape with rfl | ⟨t, i, rfl⟩
  · rfl
  · simp only [renameValue, dynamicTypeNameForMessage]
    exact goTypeNameForMessage_congr htypes t

theorem typeAssertPanicMessage_ren {v : GoValue} {tgt : Ty}
    {src : Option Ty} {missing : Option String}
    (hshape : v = .nil ∨ ∃ t i, v = .interface t i) :
    typeAssertPanicMessage σF (renameValue ρ v) tgt src missing
      = typeAssertPanicMessage σ v tgt src missing := by
  unfold typeAssertPanicMessage
  rw [resolveDefinedAliases_congr htypes]
  have hsrc : (match src with
      | some t => goTypeNameForMessage σF t
      | none => "interface {}")
      = (match src with
      | some t => goTypeNameForMessage σ t
      | none => "interface {}") := by
    cases src <;> simp [goTypeNameForMessage_congr htypes]
  rcases hshape with rfl | ⟨t, i, rfl⟩
  · cases hres : resolveDefinedAliases σ tgt <;>
      simp [renameValue, hsrc, goTypeNameForMessage_congr htypes,
        dynamicTypeNameForMessage]
  · cases hres : resolveDefinedAliases σ tgt <;>
      simp [renameValue, hsrc, goTypeNameForMessage_congr htypes,
        dynamicTypeNameForMessage]

end Builders

end GoLean.Frame
