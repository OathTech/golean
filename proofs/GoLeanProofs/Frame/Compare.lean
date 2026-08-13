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
    first
      | (simp only [renameValue]; exact h)
      | exact absurd h
          (by simp [intBinaryResult, valueAsIntValue, Bind.bind, Except.bind])

theorem intBitwiseBinaryResult_ren {nm : String} {op : Nat → Nat → Nat}
    {l r v : GoValue} (h : intBitwiseBinaryResult nm op l r = .ok v) :
    intBitwiseBinaryResult nm op (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    first
      | (simp only [renameValue]; exact h)
      | exact absurd h
          (by simp [intBitwiseBinaryResult, valueAsIntValue, Bind.bind, Except.bind])

theorem intBitClearResult_ren {l r v : GoValue}
    (h : intBitClearResult l r = .ok v) :
    intBitClearResult (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    first
      | (simp only [renameValue]; exact h)
      | exact absurd h
          (by simp [intBitClearResult, valueAsIntValue, Bind.bind, Except.bind])

theorem intBitNegResult_ren {x v : GoValue} (h : intBitNegResult x = .ok v) :
    intBitNegResult (renameValue ρ x) = .ok v := by
  cases x <;>
    first
      | (simp only [renameValue]; exact h)
      | exact absurd h
          (by simp [intBitNegResult, valueAsIntValue, Bind.bind, Except.bind])

theorem floatBinaryResult_ren {nm : String} {op64 op32 : Nat → Nat → Nat}
    {l r v : GoValue} (h : floatBinaryResult nm op64 op32 l r = .ok v) :
    floatBinaryResult nm op64 op32 (renameValue ρ l) (renameValue ρ r) = .ok v := by
  cases l <;> cases r <;>
    first
      | (simp only [renameValue]; exact h)
      | exact absurd h (by simp [floatBinaryResult])

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
        valueAsInt, pure_bind, bind_eq_ok, pure_eq_ok] at h
      obtain ⟨cnt, hcnt, hv⟩ := h
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
        valueAsInt, pure_bind, bind_eq_ok, pure_eq_ok] at h
      obtain ⟨cnt, hcnt, hv⟩ := h
      subst hv
      simp [renameValue]
    all_goals exact ExSim.stuck'
  all_goals exact ExSim.stuck'

end

end GoLean.Frame
