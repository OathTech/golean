import GoLeanProofs.Frame.Values

/-!
# The executable frame theorem: panic-freedom of the pure value walks

`ExSim`'s panic clause demands that a canonical panic transfer with the
SAME message. For helpers whose commutation is stated ok-transfer-only
(`coerceStoredValue_ren`, `normalizeValueForTy_ren`, …) the enclosing
op-level proofs additionally need to discharge the panic case — which is
vacuous, because these walks never `panic` (their errors are all
`stuck`/`unsupported`). This module proves exactly that, plus the
`ExSim`-introduction rule consuming the pair (ok-transfer +
panic-freedom ⇒ `ExSim`).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

/-- The computation never yields a `panic` error. -/
def NoPanic {α : Type} (x : Except GoError α) : Prop :=
  ∀ m, x ≠ .error (.panic m)

namespace NoPanic

variable {α β : Type}

theorem ok' {a : α} : NoPanic (.ok a : Except GoError α) := by
  intro m h; cases h

theorem pure' {a : α} : NoPanic (pure a : Except GoError α) := ok'

theorem stuck' {msg : String} :
    NoPanic (.error (.stuck msg) : Except GoError α) := by
  intro m h; cases h

theorem unsupported' {msg : String} :
    NoPanic (.error (.unsupported msg) : Except GoError α) := by
  intro m h; cases h

theorem internal' {msg : String} :
    NoPanic (.error (.internal msg) : Except GoError α) := by
  intro m h; cases h

theorem bind' {x : Except GoError α} {f : α → Except GoError β}
    (hx : NoPanic x) (hf : ∀ a, x = .ok a → NoPanic (f a)) :
    NoPanic (x >>= f) := by
  cases x with
  | ok a => simpa [Bind.bind, Except.bind] using hf a rfl
  | error e =>
      intro m h
      simp only [Bind.bind, Except.bind] at h
      injection h with he
      exact hx m (by rw [he])

theorem bind {x : Except GoError α} {f : α → Except GoError β}
    (hx : NoPanic x) (hf : ∀ a, NoPanic (f a)) : NoPanic (x >>= f) :=
  bind' hx (fun a _ => hf a)

theorem map {x : Except GoError α} {f : α → β} (hx : NoPanic x) :
    NoPanic (f <$> x) := by
  cases x with
  | ok a => intro m h; simp [Functor.map, Except.map] at h
  | error e =>
      intro m h
      simp only [Functor.map, Except.map] at h
      injection h with he
      exact hx m (by rw [he])

theorem ite' {c : Prop} [Decidable c] {x y : Except GoError α}
    (hx : NoPanic x) (hy : NoPanic y) : NoPanic (if c then x else y) := by
  split
  · exact hx
  · exact hy

end NoPanic

/-- ok-transfer + panic-freedom introduce `ExSim`. -/
theorem exSim_of_ren {α β : Type} {t : α → β} {x : Except GoError α}
    {y : Except GoError β}
    (hnp : NoPanic x) (htr : ∀ a, x = .ok a → y = .ok (t a)) :
    ExSim (fun a b => b = t a) x y := by
  cases x with
  | ok a => rw [htr a rfl]; exact ExSim.ok rfl
  | error e =>
      cases e with
      | panic m => exact absurd rfl (hnp m)
      | _ => trivial

/-! ## `coerceStoredValue` -/

theorem coerceStoredValue_noPanic :
    ∀ old v : GoValue, NoPanic (coerceStoredValue old v) := by
  refine fun old v => coerceStoredValue.induct
    (motive_1 := fun old v => NoPanic (coerceStoredValue old v))
    (motive_2 := fun oldFs newFs => NoPanic (coerceStruct oldFs newFs))
    (motive_3 := fun oldL newL => NoPanic (coerceArray oldL newL))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ old v
  · intro _ _ _ _; exact NoPanic.pure'
  · intro _ _ _ _ hk
    simp only [coerceStoredValue]
    rw [if_pos hk]
    exact NoPanic.pure'
  · intro _ _ _ _ hk
    simp only [coerceStoredValue]
    rw [if_neg hk]
    exact NoPanic.stuck'
  · intro _ _ hne
    simp only [coerceStoredValue]
    rw [if_pos hne]
    exact NoPanic.stuck'
  · intro _ _ hne ih
    simp only [coerceStoredValue]
    rw [if_neg hne]
    exact NoPanic.map ih
  · intro _ _ _ _ hne
    simp only [coerceStoredValue]
    rw [if_pos hne]
    exact NoPanic.stuck'
  · intro _ _ _ _ hne hsz
    simp only [coerceStoredValue]
    rw [if_neg hne, if_pos hsz]
    exact NoPanic.stuck'
  · intro _ _ _ _ hne hsz ih
    simp only [coerceStoredValue]
    rw [if_neg hne, if_neg hsz]
    exact NoPanic.map ih
  · intro t x hint hfloat harr hstruct
    rw [coerceStoredValue.eq_def]
    split
    · exact (hint _ _ _ _ rfl rfl).elim
    · exact (hfloat _ _ _ _ rfl rfl).elim
    · exact (harr _ _ rfl rfl).elim
    · exact (hstruct _ _ _ _ rfl rfl).elim
    · exact NoPanic.pure'
  · intro _ _ _ _ ih1 ih3
    simp only [coerceArray]
    exact NoPanic.bind ih1 fun _ =>
      NoPanic.bind ih3 fun _ => NoPanic.pure'
  · intro t x hnc
    rw [coerceArray.eq_def]
    split
    · exact (hnc _ _ _ _ rfl rfl).elim
    · exact NoPanic.pure'
  · intro _ _ _ _ _ _ hname _ih1 _ih2
    simp only [coerceStruct]
    rw [if_pos hname]
    exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
  · intro _ _ _ _ _ _ hname ih1 ih2
    simp only [coerceStruct]
    rw [if_neg hname]
    exact NoPanic.bind ih1 fun _ => NoPanic.bind ih2 fun _ => NoPanic.pure'
  · intro t x hnc
    rw [coerceStruct.eq_def]
    split
    · exact (hnc _ _ _ _ _ _ rfl rfl).elim
    · exact NoPanic.pure'

/-! ## The normalizer -/

theorem normalizeListWith_noPanic {f : GoValue → Except GoError GoValue}
    (hf : ∀ v, NoPanic (f v)) :
    ∀ l : List GoValue, NoPanic (normalizeListWith f l) := by
  intro l
  induction l with
  | nil => exact NoPanic.pure'
  | cons v vs ih =>
      simp only [normalizeListWith]
      exact NoPanic.bind (hf v) fun _ =>
        NoPanic.bind ih fun _ => NoPanic.pure'

theorem normalizeFieldsWith_noPanic {f : Ty → GoValue → Except GoError GoValue}
    (hf : ∀ ty v, NoPanic (f ty v)) :
    ∀ (fds : List FieldDef) (l : List (String × GoValue)),
      NoPanic (normalizeFieldsWith f fds l) := by
  intro fds
  induction fds with
  | nil => intro l; cases l <;> exact NoPanic.pure'
  | cons fd rest ih =>
      intro l
      cases l with
      | nil => exact NoPanic.pure'
      | cons p ps =>
          obtain ⟨pn, pv⟩ := p
          simp only [normalizeFieldsWith]
          split
          · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
          · exact NoPanic.bind (hf _ _) fun _ =>
              NoPanic.bind (ih ps) fun _ => NoPanic.pure'

theorem normalizeStructValueWith_noPanic
    {f : Ty → GoValue → Except GoError GoValue}
    (hf : ∀ ty v, NoPanic (f ty v))
    (name : TypeId) (fields : Array FieldDef) (v : GoValue) :
    NoPanic (normalizeStructValueWith f name fields v) := by
  cases v
  case struct actual fieldsValue =>
    simp only [normalizeStructValueWith]
    split
    · split
      · exact NoPanic.pure'
      · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
    · split
      · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
      · exact NoPanic.map (normalizeFieldsWith_noPanic hf _ _)
  all_goals exact NoPanic.stuck'

theorem normalizeValueForTyFuel_noPanic (σ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty) (v : GoValue),
      NoPanic (normalizeValueForTyFuel fuel σ ty v) := by
  intro fuel
  induction fuel with
  | zero => intro ty v; exact NoPanic.unsupported'
  | succ n ih =>
      intro ty v
      cases ty with
      | int kind =>
          cases v <;> simp only [normalizeValueForTyFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.stuck'
      | float kind =>
          cases v <;> simp only [normalizeValueForTyFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.stuck'
            | exact NoPanic.ite' NoPanic.pure' NoPanic.stuck'
      | array length elem =>
          cases v <;> simp only [normalizeValueForTyFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.stuck'
            | skip
          split
          · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
          · exact NoPanic.map (normalizeListWith_noPanic (fun v => ih _ v) _)
      | interface id => exact NoPanic.pure'
      | funcType ps rs _ =>
          cases v <;> simp only [normalizeValueForTyFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.stuck'
      | chan dir elem =>
          cases v <;> simp only [normalizeValueForTyFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.stuck'
      | sync kind =>
          cases v <;> simp only [normalizeValueForTyFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.stuck'
            | exact NoPanic.ite' NoPanic.pure' NoPanic.stuck'
      | defined name =>
          simp only [normalizeValueForTyFuel]
          cases TypeEnv.lookup σ.types name with
          | none => exact NoPanic.unsupported'
          | some td =>
              cases td with
              | alias target => exact ih _ _
              | defined target => exact ih _ _
              | struct fields =>
                  exact normalizeStructValueWith_noPanic (fun ty v => ih ty v)
                    name fields v
              | interfaceDef ms => exact NoPanic.unsupported'
              | unsupported f => exact NoPanic.unsupported'
      | unsupported f => exact NoPanic.unsupported'
      | bool => exact NoPanic.pure'
      | string => exact NoPanic.pure'
      | slice elem => exact NoPanic.pure'
      | map kt vt => exact NoPanic.pure'
      | pointer elem => exact NoPanic.pure'

theorem normalizeValueForTy_noPanic (σ : ExecState) (ty : Ty) (v : GoValue) :
    NoPanic (normalizeValueForTy σ ty v) := by
  rw [normalizeValueForTy]
  exact normalizeValueForTyFuel_noPanic σ _ ty v

end GoLean.Frame
