import GoLeanProofs.Frame.TypeCongr

/-!
# The executable frame theorem, module 5: comparison commutations

Structural equality (`GoValue.eqbFuel`/`eqb`), Go `==` at a type
(`valueEqFuel`/`valueEq`), ordering comparisons, the integer/float
operator result helpers, key hashability, and the map-entry search all
commute with the address renaming:

* structural equality is renaming-INVARIANT as a full equation — the
  fuel-structural `eqb` decides only shapes, scalars, and loc identity,
  and `renameLoc` is injective;
* Go `==` is state-congruent (types only) and renaming-invariant up to
  the same verdict (`ExSim Eq`) — panic messages name types, never
  addresses;
* the scalar operator helpers ok-transfer verbatim (results are ints or
  floats, on which the renaming is the identity); the shifts can panic
  on a negative amount (a FIXED message), so they ship in `ExSim` form.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## Derived-`BEq` transports for the loc-carrying records -/

section
variable {ρ : Nat → Nat} (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
include hinj

theorem renameSliceVal_beq (s t : SliceValue) :
    (({ s with base := s.base.map (renameLoc ρ) } : SliceValue)
      == { t with base := t.base.map (renameLoc ρ) }) = (s == t) := by
  obtain ⟨sb, so, sl, sc⟩ := s
  obtain ⟨tb, to, tl, tc⟩ := t
  show (sb.map (renameLoc ρ) == tb.map (renameLoc ρ)
      && (so == to && (sl == tl && sc == tc)))
    = (sb == tb && (so == to && (sl == tl && sc == tc)))
  rw [renameOptLoc_beq hinj]

theorem renameMapVal_beq (m n : MapValue) :
    (({ base := m.base.map (renameLoc ρ) } : MapValue)
      == { base := n.base.map (renameLoc ρ) }) = (m == n) := by
  obtain ⟨mb⟩ := m
  obtain ⟨nb⟩ := n
  show (mb.map (renameLoc ρ) == nb.map (renameLoc ρ)) = (mb == nb)
  exact renameOptLoc_beq hinj mb nb

theorem renameChanVal_beq (c d : ChanValue) :
    (({ base := c.base.map (renameLoc ρ) } : ChanValue)
      == { base := d.base.map (renameLoc ρ) }) = (c == d) := by
  obtain ⟨cb⟩ := c
  obtain ⟨db⟩ := d
  show (cb.map (renameLoc ρ) == db.map (renameLoc ρ)) = (cb == db)
  exact renameOptLoc_beq hinj cb db

/-! ## Structural equality commutes (a FULL equation) -/

omit hinj

private theorem eqbListWith_ren {n : Nat}
    (ih : ∀ v w : GoValue,
      GoValue.eqbFuel n (renameValue ρ v) (renameValue ρ w)
        = GoValue.eqbFuel n v w) :
    ∀ as bs : List GoValue,
      GoValue.eqbListWith (GoValue.eqbFuel n)
          (renameValueList ρ as) (renameValueList ρ bs)
        = GoValue.eqbListWith (GoValue.eqbFuel n) as bs := by
  intro as
  induction as with
  | nil =>
      intro bs
      cases bs <;> simp [renameValueList, GoValue.eqbListWith]
  | cons a as iha =>
      intro bs
      cases bs with
      | nil => simp [renameValueList, GoValue.eqbListWith]
      | cons b bs =>
          simp [renameValueList, GoValue.eqbListWith, ih, iha]

private theorem eqbPairsWith_ren {n : Nat}
    (ih : ∀ v w : GoValue,
      GoValue.eqbFuel n (renameValue ρ v) (renameValue ρ w)
        = GoValue.eqbFuel n v w) :
    ∀ as bs : List (GoValue × GoValue),
      GoValue.eqbPairsWith (GoValue.eqbFuel n)
          (renameValueEntries ρ as) (renameValueEntries ρ bs)
        = GoValue.eqbPairsWith (GoValue.eqbFuel n) as bs := by
  intro as
  induction as with
  | nil =>
      intro bs
      cases bs with
      | nil => simp [renameValueEntries, GoValue.eqbPairsWith]
      | cons b bs =>
          obtain ⟨bk, bv⟩ := b
          simp [renameValueEntries, GoValue.eqbPairsWith]
  | cons a as iha =>
      obtain ⟨ak, av⟩ := a
      intro bs
      cases bs with
      | nil => simp [renameValueEntries, GoValue.eqbPairsWith]
      | cons b bs =>
          obtain ⟨bk, bv⟩ := b
          simp [renameValueEntries, GoValue.eqbPairsWith, ih, iha]

private theorem eqbFieldsWith_ren {n : Nat}
    (ih : ∀ v w : GoValue,
      GoValue.eqbFuel n (renameValue ρ v) (renameValue ρ w)
        = GoValue.eqbFuel n v w) :
    ∀ as bs : List (String × GoValue),
      GoValue.eqbFieldsWith (GoValue.eqbFuel n)
          (renameValueFields ρ as) (renameValueFields ρ bs)
        = GoValue.eqbFieldsWith (GoValue.eqbFuel n) as bs := by
  intro as
  induction as with
  | nil =>
      intro bs
      cases bs with
      | nil => simp [renameValueFields, GoValue.eqbFieldsWith]
      | cons b bs =>
          obtain ⟨bn, bv⟩ := b
          simp [renameValueFields, GoValue.eqbFieldsWith]
  | cons a as iha =>
      obtain ⟨an, av⟩ := a
      intro bs
      cases bs with
      | nil => simp [renameValueFields, GoValue.eqbFieldsWith]
      | cons b bs =>
          obtain ⟨bn, bv⟩ := b
          simp [renameValueFields, GoValue.eqbFieldsWith, ih, iha]

include hinj

theorem renameValue_eqbFuel (fuel : Nat) (v w : GoValue) :
    GoValue.eqbFuel fuel (renameValue ρ v) (renameValue ρ w)
      = GoValue.eqbFuel fuel v w := by
  induction fuel generalizing v w with
  | zero =>
      cases v <;> cases w <;>
        simp only [renameValue, GoValue.eqbFuel, renameLoc_beq hinj,
          renameSliceVal_beq hinj, renameMapVal_beq hinj,
          renameChanVal_beq hinj]
  | succ n ih =>
      cases v <;> cases w <;>
        simp only [renameValue, GoValue.eqbFuel,
          renameLoc_beq hinj, renameSliceVal_beq hinj,
          renameMapVal_beq hinj, renameChanVal_beq hinj, ih,
          eqbListWith_ren ih, eqbPairsWith_ren ih, eqbFieldsWith_ren ih]

theorem renameValue_eqb (v w : GoValue) :
    (renameValue ρ v == renameValue ρ w) = (v == w) :=
  renameValue_eqbFuel hinj valueEqbFuel v w

end

/-! ## Ordering comparisons and operator results (ok-transfer)

Every `.ok` verdict of the scalar comparison/operator helpers is
computed from ints, floats, or strings — values on which the renaming
is the identity — so the canonical hypothesis transfers verbatim. The
`absurd` arms discharge the loc-carrying operand shapes, where the
canonical run is `stuck` and the hypothesis is impossible. -/

section
variable (ρ : Nat → Nat)

theorem valueLess_ren {l r : GoValue} {b : Bool} (h : valueLess l r = .ok b) :
    valueLess (renameValue ρ l) (renameValue ρ r) = .ok b := by
  cases l <;> cases r <;>
    simp only [renameValue, valueLess, floatCompareResult, stuck_eq,
      reduceCtorEq] at h ⊢ <;>
    exact h

theorem valueAtMost_ren {l r : GoValue} {b : Bool} (h : valueAtMost l r = .ok b) :
    valueAtMost (renameValue ρ l) (renameValue ρ r) = .ok b := by
  cases l <;> cases r <;>
    simp only [renameValue, valueAtMost, floatCompareResult, stuck_eq,
      reduceCtorEq] at h ⊢ <;>
    exact h

theorem valueGreater_ren {l r : GoValue} {b : Bool} (h : valueGreater l r = .ok b) :
    valueGreater (renameValue ρ l) (renameValue ρ r) = .ok b := by
  cases l <;> cases r <;>
    simp only [renameValue, valueGreater, floatCompareResult, stuck_eq,
      reduceCtorEq] at h ⊢ <;>
    exact h

theorem valueAtLeast_ren {l r : GoValue} {b : Bool} (h : valueAtLeast l r = .ok b) :
    valueAtLeast (renameValue ρ l) (renameValue ρ r) = .ok b := by
  cases l <;> cases r <;>
    simp only [renameValue, valueAtLeast, floatCompareResult, stuck_eq,
      reduceCtorEq] at h ⊢ <;>
    exact h

theorem anyFloatOperand_ren (vs : List GoValue) :
    anyFloatOperand (renameValueList ρ vs) = anyFloatOperand vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      simp only [renameValueList, anyFloatOperand, List.any_cons] at ih ⊢
      rw [ih]
      cases v <;> simp [renameValue]

theorem intBinaryResult_ren {nm : String} {op : Int → Int → Int}
    {l r v : GoValue} (h : intBinaryResult nm op l r = .ok v) :
    intBinaryResult nm op (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    simp only [renameValue, intBinaryResult, valueAsIntValue, stuck_eq,
      Bind.bind, Except.bind, pure, Except.pure, reduceCtorEq] at h ⊢ <;>
    exact h

theorem intBitwiseBinaryResult_ren {nm : String} {op : Nat → Nat → Nat}
    {l r v : GoValue} (h : intBitwiseBinaryResult nm op l r = .ok v) :
    intBitwiseBinaryResult nm op (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    simp only [renameValue, intBitwiseBinaryResult, valueAsIntValue, stuck_eq,
      Bind.bind, Except.bind, pure, Except.pure, reduceCtorEq] at h ⊢ <;>
    exact h

theorem intBitClearResult_ren {l r v : GoValue}
    (h : intBitClearResult l r = .ok v) :
    intBitClearResult (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    simp only [renameValue, intBitClearResult, valueAsIntValue, stuck_eq,
      Bind.bind, Except.bind, pure, Except.pure, reduceCtorEq] at h ⊢ <;>
    exact h

theorem intBitNegResult_ren {x v : GoValue} (h : intBitNegResult x = .ok v) :
    intBitNegResult (renameValue ρ x) = .ok v := by
  cases x <;>
    simp only [renameValue, intBitNegResult, valueAsIntValue, stuck_eq,
      Bind.bind, Except.bind, pure, Except.pure, reduceCtorEq] at h ⊢ <;>
    exact h

theorem floatBinaryResult_ren {nm : String} {op64 op32 : Nat → Nat → Nat}
    {l r v : GoValue} (h : floatBinaryResult nm op64 op32 l r = .ok v) :
    floatBinaryResult nm op64 op32 (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    simp only [renameValue, floatBinaryResult, stuck_eq,
      pure, Except.pure, reduceCtorEq] at h ⊢ <;>
    exact h

/-! ### Shifts (can PANIC on a negative amount — `ExSim` form) -/

/-- A computation whose `.ok` results the renaming fixes simulates
itself under the value-transfer relation. -/
private theorem exsim_ren_self {x : Except GoError GoValue}
    (hok : ∀ v, x = .ok v → renameValue ρ v = v) :
    ExSim (fun a b => b = renameValue ρ a) x x := by
  cases x with
  | ok a => exact (hok a rfl).symm
  | error e => cases e <;> first | exact rfl | trivial

theorem intShiftLeftResult_sim (l r : GoValue) :
    ExSim (fun a b => b = renameValue ρ a)
      (intShiftLeftResult l r)
      (intShiftLeftResult (renameValue ρ l) (renameValue ρ r)) := by
  cases l
  case int lv lk =>
    cases r
    case int rv rk =>
      simp only [renameValue]
      refine exsim_ren_self ρ ?_
      intro v h
      simp only [intShiftLeftResult, valueAsIntValue, shiftCountNat,
        valueAsInt, bind_eq_ok] at h
      obtain ⟨cnt, -, a, -, hv⟩ := h
      injection hv with hv
      subst hv
      simp [renameValue]
    all_goals exact ExSim.stuck'
  all_goals exact ExSim.stuck'

theorem intShiftRightResult_sim (l r : GoValue) :
    ExSim (fun a b => b = renameValue ρ a)
      (intShiftRightResult l r)
      (intShiftRightResult (renameValue ρ l) (renameValue ρ r)) := by
  cases l
  case int lv lk =>
    cases r
    case int rv rk =>
      simp only [renameValue]
      refine exsim_ren_self ρ ?_
      intro v h
      simp only [intShiftRightResult, valueAsIntValue, shiftCountNat,
        valueAsInt, bind_eq_ok] at h
      obtain ⟨cnt, -, a, -, hv⟩ := h
      injection hv with hv
      subst hv
      simp [renameValue]
    all_goals exact ExSim.stuck'
  all_goals exact ExSim.stuck'

end

/-! ## Hashability, `==` at a type, and the map-entry search -/

section
variable {ρ : Nat → Nat} (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
variable {σ σF : ExecState} (htypes : σF.types = σ.types)

include htypes in
/-- Hashability is state-congruent (types only) and renaming-invariant:
the interface arm reads `tyUncomparable`/`goTypeNameForMessage` (tables
only), struct/array arms recurse, and every other value is
`.hashable`. -/
theorem valueHashability_ren (v : GoValue) :
    valueHashability σF (renameValue ρ v) = valueHashability σ v := by
  refine valueHashability.induct σ
    (motive_1 := fun v =>
      valueHashability σF (renameValue ρ v) = valueHashability σ v)
    (motive_2 := fun l =>
      valueHashabilityList σF (renameValueList ρ l)
        = valueHashabilityList σ l)
    (motive_3 := fun fs =>
      valueHashabilityFields σF (renameValueFields ρ fs)
        = valueHashabilityFields σ fs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
  · -- interface, dynamic type uncomparable
    intro dynTy inner h
    simp only [renameValue, valueHashability, tyUncomparable_congr htypes,
      goTypeNameForMessage_congr htypes, h]
  · -- interface, dynamic type comparable: recurse
    intro dynTy inner h ih
    simp only [renameValue, valueHashability, tyUncomparable_congr htypes,
      h, ih]
  · -- interface, comparability unknown
    intro dynTy inner h
    simp only [renameValue, valueHashability, tyUncomparable_congr htypes,
      goTypeNameForMessage_congr htypes, h]
  · -- struct
    intro tid fields ih
    simp only [renameValue, valueHashability, ih]
  · -- array
    intro values ih
    simp only [renameValue, valueHashability, ih]
  · -- every other shape is hashable
    intro t h1 h2 h3
    cases t
    case interface dynTy inner => exact absurd rfl (h1 dynTy inner)
    case struct tid fields => exact absurd rfl (h2 tid fields)
    case array values => exact absurd rfl (h3 values)
    all_goals simp [renameValue, valueHashability]
  · -- list nil
    simp [renameValueList, valueHashabilityList]
  · -- list cons, head hashable
    intro v rest hh ih1 ih2
    simp only [renameValueList, valueHashabilityList, ih1, hh, ih2]
  · -- list cons, head not hashable
    intro v rest hnh ih1
    cases hcase : valueHashability σ v with
    | hashable => exact absurd hcase hnh
    | unhashable name =>
        simp only [renameValueList, valueHashabilityList, ih1, hcase]
    | unknown name =>
        simp only [renameValueList, valueHashabilityList, ih1, hcase]
  · -- fields nil
    simp [renameValueFields, valueHashabilityFields]
  · -- fields cons, head hashable
    intro fst v rest hh ih1 ih2
    simp only [renameValueFields, valueHashabilityFields, ih1, hh, ih2]
  · -- fields cons, head not hashable
    intro fst v rest hnh ih1
    cases hcase : valueHashability σ v with
    | hashable => exact absurd hcase hnh
    | unhashable name =>
        simp only [renameValueFields, valueHashabilityFields, ih1, hcase]
    | unknown name =>
        simp only [renameValueFields, valueHashabilityFields, ih1, hcase]

include htypes in
theorem checkKeyHashable_sim (key : GoValue) (isInsert nonEmpty : Bool) :
    ExSim (fun _ _ => True)
      (checkKeyHashable σ key isInsert nonEmpty)
      (checkKeyHashable σF (renameValue ρ key) isInsert nonEmpty) := by
  unfold checkKeyHashable
  rw [valueHashability_ren (ρ := ρ) htypes]
  cases valueHashability σ key with
  | unhashable name => exact ExSim.panic
  | unknown name => exact ExSim.unsupported'
  | hashable => exact ExSim.ok trivial

/-! ### `valueEqFuel`: Go `==` at a type, `ExSim Eq` form -/

omit hinj htypes

/-- A stuck-guard prefix (`if c then stuck msg` in `do` position, which
the `do` elaborator compiles by duplicating the continuation into both
branches) with the SAME condition on both sides transfers any
unconditional tail simulation: the guard either sticks the canonical
run (vacuous transfer) or passes through on both sides. -/
private theorem ExSim.guard {α β : Type} {R : α → β → Prop} {c : Prop}
    [Decidable c] {m₁ m₂ : String} {x : Except GoError α}
    {y : Except GoError β} (h : ExSim R x y) :
    ExSim R
      (if c then (stuck m₁ : Except GoError PUnit) >>= fun _ => x
        else pure PUnit.unit >>= fun _ => x)
      (if c then (stuck m₂ : Except GoError PUnit) >>= fun _ => y
        else pure PUnit.unit >>= fun _ => y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact ExSim.stuck'
  · rw [if_neg hc, if_neg hc]
    exact h

private theorem validateSlice_sim (ρ : Nat → Nat) (s : SliceValue) :
    ExSim (fun _ _ => True) (validateSlice s)
      (validateSlice { s with base := s.base.map (renameLoc ρ) }) := by
  obtain ⟨b, o, ln, cp⟩ := s
  simp only [validateSlice]
  refine ExSim.guard ?_
  cases b with
  | none =>
      simp only [Option.map_none]
      exact ExSim.ite_congr (fun _ => ExSim.ok trivial) (fun _ => ExSim.stuck')
  | some l => exact ExSim.ok trivial

private theorem valueEqListWith_sim {ρ : Nat → Nat}
    {f g : GoValue → GoValue → Except GoError Bool}
    (hfg : ∀ a b, ExSim Eq (f a b) (g (renameValue ρ a) (renameValue ρ b))) :
    ∀ as bs : List GoValue,
      ExSim Eq (valueEqListWith f as bs)
        (valueEqListWith g (renameValueList ρ as) (renameValueList ρ bs)) := by
  intro as
  induction as with
  | nil =>
      intro bs
      cases bs <;> simp only [renameValueList, valueEqListWith] <;>
        exact ExSim.ok rfl
  | cons a as iha =>
      intro bs
      cases bs with
      | nil =>
          simp only [renameValueList, valueEqListWith]
          exact ExSim.ok rfl
      | cons b bs =>
          simp only [renameValueList, valueEqListWith]
          refine ExSim.bind (hfg a b) fun x y hxy => ?_
          subst hxy
          cases x with
          | true => simpa using iha bs
          | false => exact ExSim.ok rfl

private theorem valueEqFieldsWith_sim {ρ : Nat → Nat}
    {f g : Ty → GoValue → GoValue → Except GoError Bool}
    (hfg : ∀ t a b, ExSim Eq (f t a b) (g t (renameValue ρ a) (renameValue ρ b))) :
    ∀ (fds : List FieldDef) (ls rs : List (String × GoValue)),
      ExSim Eq (valueEqFieldsWith f fds ls rs)
        (valueEqFieldsWith g fds (renameValueFields ρ ls)
          (renameValueFields ρ rs)) := by
  intro fds
  induction fds with
  | nil =>
      intro ls rs
      cases ls <;> cases rs <;> simp only [renameValueFields] <;>
        first
          | exact ExSim.ok rfl
          | (rename_i p _; obtain ⟨n, v⟩ := p
             simp only [renameValueFields]; exact ExSim.ok rfl)
          | (rename_i p _ q _; obtain ⟨n, v⟩ := p; obtain ⟨n', v'⟩ := q
             simp only [renameValueFields]; exact ExSim.ok rfl)
  | cons fd fds ihf =>
      intro ls rs
      cases ls with
      | nil =>
          cases rs with
          | nil => exact ExSim.ok rfl
          | cons q rs =>
              obtain ⟨n', v'⟩ := q
              simp only [renameValueFields, valueEqFieldsWith]
              exact ExSim.ok rfl
      | cons p ls =>
          obtain ⟨n, v⟩ := p
          cases rs with
          | nil =>
              simp only [renameValueFields, valueEqFieldsWith]
              exact ExSim.ok rfl
          | cons q rs =>
              obtain ⟨n', v'⟩ := q
              simp only [renameValueFields, valueEqFieldsWith]
              refine ExSim.guard (ExSim.guard ?_)
              refine ExSim.bind (hfg fd.typ v v') fun x y hxy => ?_
              subst hxy
              cases x with
              | true => simpa using ihf ls rs
              | false => exact ExSim.ok rfl

private theorem renList_toArray_size {ρ : Nat → Nat} (vs : Array GoValue) :
    ((renameValueList ρ vs.toList).toArray).size = vs.size := by
  simp [renameValueList_eq_map]

private theorem renFields_toArray_size {ρ : Nat → Nat}
    (fs : Array (String × GoValue)) :
    ((renameValueFields ρ fs.toList).toArray).size = fs.size := by
  simp [renameValueFields_eq_map]

private theorem emptyStructAssignable_ren {ρ : Nat → Nat} (a n : TypeId)
    (fds : Array FieldDef) (fs : Array (String × GoValue)) :
    emptyStructAssignable a n fds ((renameValueFields ρ fs.toList).toArray)
      = emptyStructAssignable a n fds fs := by
  simp [emptyStructAssignable, Array.isEmpty, renameValueFields_eq_map]

include hinj htypes in
set_option maxHeartbeats 3200000 in
/-- Go `==` at a type is renaming-invariant up to the same verdict:
panic messages name TYPES only (`comparing uncomparable type X`), and
every loc comparison goes through injective-renaming-invariant `BEq`
transports. Canonical stuck/unsupported arms transfer vacuously.
(The heartbeat bump is sheer case count — 14 type arms × up to 17×17
value shapes in ONE declaration — not any single hard goal.) -/
theorem valueEqFuel_sim (fuel : Nat) (ty : Ty) (l r : GoValue) :
    ExSim Eq (valueEqFuel fuel σ ty l r)
      (valueEqFuel fuel σF ty (renameValue ρ l) (renameValue ρ r)) := by
  induction fuel generalizing ty l r with
  | zero => exact ExSim.unsupported'
  | succ n ih =>
      cases ty with
      | bool =>
          cases l <;> cases r <;> simp only [renameValue, valueEqFuel] <;>
            first | exact ExSim.stuck' | exact ExSim.refl _
      | int kind =>
          cases l <;> cases r <;> simp only [renameValue, valueEqFuel] <;>
            first | exact ExSim.stuck' | exact ExSim.refl _
      | float kind =>
          cases l <;> cases r <;> simp only [renameValue, valueEqFuel] <;>
            first | exact ExSim.stuck' | exact ExSim.refl _
      | string =>
          cases l <;> cases r <;> simp only [renameValue, valueEqFuel] <;>
            first | exact ExSim.stuck' | exact ExSim.refl _
      | funcType params results =>
          cases l <;> cases r <;> simp only [renameValue, valueEqFuel] <;>
            first | exact ExSim.stuck' | exact ExSim.refl _
      | pointer elem =>
          cases l <;> cases r <;> simp only [renameValue, valueEqFuel] <;>
            first
              | exact ExSim.stuck'
              | exact ExSim.refl _
              | exact ExSim.ok ((renameLoc_beq hinj _ _).symm)
      | array length elem =>
          cases l <;> cases r
          case array.array a b =>
            simp only [renameValue, valueEqFuel, renList_toArray_size]
            refine ExSim.guard (ExSim.guard ?_)
            exact valueEqListWith_sim (fun x y => ih elem x y) a.toList b.toList
          all_goals
            simp only [renameValue, valueEqFuel] <;> exact ExSim.stuck'
      | slice elem =>
          cases l <;> cases r
          case slice.slice s t =>
            obtain ⟨sb, so, sl2, sc⟩ := s
            obtain ⟨tb, to2, tl2, tc⟩ := t
            simp only [renameValue, valueEqFuel]
            refine ExSim.bind (validateSlice_sim ρ ⟨sb, so, sl2, sc⟩)
              fun _ _ _ => ?_
            refine ExSim.bind (validateSlice_sim ρ ⟨tb, to2, tl2, tc⟩)
              fun _ _ _ => ?_
            cases sb <;> cases tb <;>
              simp only [Option.map_none, Option.map_some] <;>
              first | exact ExSim.ok rfl | exact ExSim.stuck'
          case slice.nil s =>
            obtain ⟨sb, so, sl2, sc⟩ := s
            simp only [renameValue, valueEqFuel]
            refine ExSim.bind (validateSlice_sim ρ ⟨sb, so, sl2, sc⟩)
              fun _ _ _ => ?_
            exact ExSim.ok (by cases sb <;> simp)
          case nil.slice t =>
            obtain ⟨tb, to2, tl2, tc⟩ := t
            simp only [renameValue, valueEqFuel]
            refine ExSim.bind (validateSlice_sim ρ ⟨tb, to2, tl2, tc⟩)
              fun _ _ _ => ?_
            exact ExSim.ok (by cases tb <;> simp)
          all_goals
            simp only [renameValue, valueEqFuel] <;> exact ExSim.stuck'
      | map keyTy valTy =>
          cases l <;> cases r
          case map.map m mm =>
            obtain ⟨mb⟩ := m
            obtain ⟨nb⟩ := mm
            simp only [renameValue, valueEqFuel]
            cases mb <;> cases nb <;>
              simp only [Option.map_none, Option.map_some] <;>
              first | exact ExSim.ok rfl | exact ExSim.stuck'
          case map.nil m =>
            obtain ⟨mb⟩ := m
            simp only [renameValue, valueEqFuel]
            exact ExSim.ok (by cases mb <;> simp)
          case nil.map m =>
            obtain ⟨mb⟩ := m
            simp only [renameValue, valueEqFuel]
            exact ExSim.ok (by cases mb <;> simp)
          all_goals
            simp only [renameValue, valueEqFuel] <;> exact ExSim.stuck'
      | chan dir elem =>
          cases l <;> cases r
          case chan.chan c d =>
            simp only [renameValue, valueEqFuel]
            exact ExSim.ok ((renameChanVal_beq hinj c d).symm)
          case chan.nil c =>
            obtain ⟨cb⟩ := c
            simp only [renameValue, valueEqFuel]
            exact ExSim.ok (by cases cb <;> simp)
          case nil.chan c =>
            obtain ⟨cb⟩ := c
            simp only [renameValue, valueEqFuel]
            exact ExSim.ok (by cases cb <;> simp)
          all_goals
            simp only [renameValue, valueEqFuel] <;>
              first | exact ExSim.stuck' | exact ExSim.refl _
      | interface iid =>
          cases l <;> cases r
          case interface.interface dynL innerL dynR innerR =>
            simp only [renameValue, valueEqFuel]
            refine ExSim.ite_congr (fun _ => ExSim.ok rfl) (fun _ => ?_)
            simp only [tyUncomparable_congr htypes,
              goTypeNameForMessage_congr htypes]
            cases htu : tyUncomparable σ dynL with
            | none =>
                simp only []
                exact ih dynL innerL innerR
            | some b =>
                cases b with
                | false =>
                    simp only []
                    exact ih dynL innerL innerR
                | true =>
                    simp only []
                    exact ExSim.panic
          all_goals
            simp only [renameValue, valueEqFuel] <;>
              first | exact ExSim.unsupported' | exact ExSim.refl _
      | sync kind =>
          simp only [valueEqFuel]
          exact ExSim.unsupported'
      | defined name =>
          simp only [valueEqFuel, htypes]
          cases hl : TypeEnv.lookup σ.types name with
          | none =>
              simp only []
              exact ExSim.unsupported'
          | some td =>
              cases td with
              | alias target =>
                  simp only []
                  exact ih target l r
              | defined target =>
                  simp only []
                  exact ih target l r
              | interfaceDef ms =>
                  simp only []
                  exact ExSim.unsupported'
              | unsupported ft =>
                  simp only []
                  exact ExSim.unsupported'
              | struct fds =>
                  simp only []
                  cases l <;> cases r
                  case struct.struct ltid lfs rtid rfs =>
                    simp only [renameValue, emptyStructAssignable_ren,
                      renFields_toArray_size]
                    refine ExSim.guard (ExSim.guard (ExSim.guard
                      (ExSim.guard ?_)))
                    exact valueEqFieldsWith_sim (fun t a b => ih t a b)
                      fds.toList lfs.toList rfs.toList
                  all_goals
                    simp only [renameValue] <;> exact ExSim.stuck'
      | unsupported feature =>
          simp only [valueEqFuel]
          exact ExSim.unsupported'

include hinj htypes in
theorem valueEq_sim (ty : Ty) (l r : GoValue) :
    ExSim Eq (valueEq σ ty l r)
      (valueEq σF ty (renameValue ρ l) (renameValue ρ r)) := by
  unfold valueEq
  exact valueEqFuel_sim hinj htypes typeResolutionFuel ty l r

/-! ### The map-entry search -/

omit hinj htypes

/-- `forIn` over an entry list and its pointwise-renamed image, with
`ExSim`-related bodies at every shared loop state, transfers — keeping
the loop state IDENTICAL (the search index never renames). -/
private theorem forIn_sim_entries {ρ : Nat → Nat} {β : Type}
    {body₁ body₂ : GoValue × GoValue → β → Except GoError (ForInStep β)}
    (hbody : ∀ k v s, ExSim Eq (body₁ (k, v) s)
      (body₂ (renameValue ρ k, renameValue ρ v) s)) :
    ∀ (l : List (GoValue × GoValue)) (s : β),
      ExSim Eq (forIn l s body₁) (forIn (renameValueEntries ρ l) s body₂) := by
  intro l
  induction l with
  | nil =>
      intro s
      simp only [renameValueEntries]
      rw [List.forIn_nil, List.forIn_nil]
      exact ExSim.ok rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      intro s
      simp only [renameValueEntries]
      rw [List.forIn_cons, List.forIn_cons]
      refine ExSim.bind (hbody k v s) fun st₁ st₂ hst => ?_
      subst hst
      cases st₁ with
      | done b => exact ExSim.ok rfl
      | yield b => exact ih b

private theorem renEntries_toArray_isEmpty {ρ : Nat → Nat}
    (es : Array (GoValue × GoValue)) :
    ((renameValueEntries ρ es.toList).toArray).isEmpty = es.isEmpty := by
  simp [Array.isEmpty, renameValueEntries_eq_map]

include hinj htypes in
/-- The map-entry search: entries and key rename pointwise; the found
index (if any) is IDENTICAL, and the hashability precheck's panic
message carries only type names. -/
theorem mapEntryIndex?_sim (kt : Ty) (entries : Array (GoValue × GoValue))
    (key : GoValue) (isInsert : Bool) :
    ExSim Eq (mapEntryIndex? σ kt entries key isInsert)
      (mapEntryIndex? σF kt
        ((renameValueEntries ρ entries.toList).toArray)
        (renameValue ρ key) isInsert) := by
  unfold mapEntryIndex?
  rw [renEntries_toArray_isEmpty]
  refine ExSim.bind (checkKeyHashable_sim htypes key isInsert _)
    fun _ _ _ => ?_
  dsimp only
  rw [← Array.forIn_toList, ← Array.forIn_toList, List.toList_toArray]
  refine ExSim.bind (forIn_sim_entries ?_ entries.toList _)
    fun r₁ r₂ hr => ?_
  · intro pk pv s
    dsimp only
    refine ExSim.bind (valueEq_sim hinj htypes kt pk key) fun b₁ b₂ hb => ?_
    subst hb
    exact ExSim.refl _
  · subst hr
    exact ExSim.refl _

end

end GoLean.Frame
