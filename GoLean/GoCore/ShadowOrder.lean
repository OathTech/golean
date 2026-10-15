import GoLean.GoCore.Ops

/-! Equality and order of shadow keys. These laws concern structural keys;
canonicalization and memory overlap are different relations. -/
namespace GoLean.GoCore
open GoLean Std
attribute [local instance] lexOrd

instance : LawfulEqOrd SyncKind where
  compare_self {a} := by cases a <;> decide
  eq_of_compare {a b} := by cases a <;> cases b <;> decide

instance : TransOrd SyncKind where
  eq_swap := OrientedOrd.eq_swap (α := Nat)
  isLE_trans := TransOrd.isLE_trans (α := Nat)

instance : LawfulEqOrd SyncWordName where
  compare_self {a} := by cases a <;> decide
  eq_of_compare {a b} := by cases a <;> cases b <;> decide

instance : TransOrd SyncWordName where
  eq_swap := OrientedOrd.eq_swap (α := Nat)
  isLE_trans := TransOrd.isLE_trans (α := Nat)

/-- An order embedding exposing the existing derived constructor/component
order. The filler components are compared only within the same constructor. -/
def ShadowKey.orderCode : ShadowKey → Nat × (Loc × (Nat × Nat))
  | .data l => (0, l, 0, 0)
  | .syncWord l k word => (1, l, k.ctorIdx, word.ctorIdx)
  | .chanObj l => (2, l, 0, 0)

theorem ShadowKey.compare_orderCode (a b : ShadowKey) :
    compare a b = compare a.orderCode b.orderCode := by
  cases a <;> cases b <;>
    simp [compare, instOrdShadowKey.ord, ShadowKey.orderCode,
      compareLex, compareOn, instOrdSyncKind.ord,
      instOrdSyncWordName.ord, compareOfLessAndEq] <;> rfl

theorem ShadowKey.orderCode_injective {a b : ShadowKey}
    (h : a.orderCode = b.orderCode) : a = b := by
  cases a <;> cases b <;> simp_all [ShadowKey.orderCode]
  case syncWord.syncWord l k word l' k' word' =>
    rcases h with ⟨rfl, hk, hw⟩
    cases k <;> cases k' <;> cases word <;> cases word' <;> simp_all [SyncKind.ctorIdx, SyncWordName.ctorIdx]

instance : LawfulEqOrd ShadowKey where
  compare_self {a} := by rw [ShadowKey.compare_orderCode]; exact compare_self
  eq_of_compare h := ShadowKey.orderCode_injective
    (LawfulEqOrd.eq_of_compare (by rwa [ShadowKey.compare_orderCode] at h))

instance : TransOrd ShadowKey where
  eq_swap {a b} := by
    rw [ShadowKey.compare_orderCode, ShadowKey.compare_orderCode]
    exact OrientedOrd.eq_swap
  isLE_trans hab hbc := by
    rw [ShadowKey.compare_orderCode] at hab hbc ⊢
    exact TransOrd.isLE_trans hab hbc

instance : LawfulBEq SyncKind where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} := by cases a <;> cases b <;> decide

instance : LawfulBEq SyncWordName where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} := by cases a <;> cases b <;> decide

instance : LawfulBEq ShadowKey where
  rfl {a} := by
    cases a with
    | data l => show (l == l) = true; simp
    | chanObj l => show (l == l) = true; simp
    | syncWord l k word =>
      show (l == l && (k == k && word == word)) = true
      simp
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> try contradiction
    case data.data a b => exact congrArg ShadowKey.data (eq_of_beq h)
    case chanObj.chanObj a b => exact congrArg ShadowKey.chanObj (eq_of_beq h)
    case syncWord.syncWord l k word l' k' word' =>
      have h' : (l == l' && (k == k' && word == word')) = true := h
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      rcases h' with ⟨rfl, rfl, rfl⟩
      rfl

end GoLean.GoCore
