import GoLean.GoCore.Value
import Init.Data.Order.Ord
import Init.Data.String.Lemmas.Order

/-! Total, kernel-visible location comparison. Constructor and component order
match Lean 4.32.2's derived `Ord`: base < field < index; recurse on the base
before comparing the field type/name or index. -/
namespace GoLean.GoCore
open GoLean Std

deriving instance Ord for Addr
deriving instance Ord for TypeId

def instOrdLoc.ord : Loc → Loc → Ordering
  | .base a, .base b => compare a.id b.id
  | .base _, _ => .lt
  | _, .base _ => .gt
  | .field a t f, .field b u g =>
      (instOrdLoc.ord a b).then ((compare t.key u.key).then (compare f g))
  | .field .., .index .. => .lt
  | .index .., .field .. => .gt
  | .index a i, .index b j => (instOrdLoc.ord a b).then (compare i j)

instance instOrdLoc : Ord Loc := ⟨instOrdLoc.ord⟩

/-- The body emitted by the pinned toolchain's `deriving Ord`, with the
recursive call made explicit. This is a specification of that source
algorithm, not a theorem about the old opaque constant. -/
def locComparisonStep (rec : Loc → Loc → Ordering) : Loc → Loc → Ordering
  | .base a, .base b => (compare a b).then .eq
  | .base _, _ => .lt
  | _, .base _ => .gt
  | .field a t f, .field b u g =>
      (rec a b).then ((compare t u).then ((compare f g).then .eq))
  | .field .., .index .. => .lt
  | .index .., .field .. => .gt
  | .index a i, .index b j => (rec a b).then ((compare i j).then .eq)

theorem loc_compare_unfold (a b : Loc) :
    instOrdLoc.ord a b = locComparisonStep instOrdLoc.ord a b := by
  cases a <;> cases b <;>
    simp [instOrdLoc.ord, locComparisonStep, compare, instOrdAddr.ord, instOrdTypeId.ord]

/-- Any function satisfying the old generated source equations has exactly
this comparison result on every finite location. Applying this to the old
opaque constant would require its unavailable equations. -/
theorem loc_comparison_unique (cmp : Loc → Loc → Ordering)
    (equations : ∀ a b, cmp a b = locComparisonStep cmp a b) :
    ∀ a b, cmp a b = instOrdLoc.ord a b := by
  intro a
  induction a with
  | base a => intro b; rw [equations, loc_compare_unfold]; cases b <;> rfl
  | field a t f ih =>
    intro b; rw [equations, loc_compare_unfold]; cases b <;>
      simp only [locComparisonStep, ih]
  | index a i ih =>
    intro b; rw [equations, loc_compare_unfold]; cases b <;>
      simp only [locComparisonStep, ih]

private theorem addr_id_eq (a b : Addr) : a.id = b.id ↔ a = b := by
  cases a; cases b; simp

private theorem type_key_eq (a b : TypeId) : a.key = b.key ↔ a = b := by
  cases a; cases b; simp

@[simp] theorem loc_compare_eq_iff (a b : Loc) : compare a b = .eq ↔ a = b := by
  change instOrdLoc.ord a b = .eq ↔ a = b
  induction a generalizing b <;> cases b <;>
    simp_all [instOrdLoc.ord, addr_id_eq, type_key_eq]

instance : LawfulEqOrd Loc where
  compare_self := (loc_compare_eq_iff _ _).2 rfl
  eq_of_compare := (loc_compare_eq_iff _ _).1

theorem loc_compare_swap (a b : Loc) : compare a b = (compare b a).swap := by
  change instOrdLoc.ord a b = (instOrdLoc.ord b a).swap
  induction a generalizing b <;> cases b <;>
    simp only [instOrdLoc.ord, Ordering.swap_then] <;> try rfl
  · exact OrientedOrd.eq_swap
  · rw [show ∀ b, instOrdLoc.ord _ b = _ from ‹∀ b, _›]
    simp only [← OrientedOrd.eq_swap]
  · rw [show ∀ b, instOrdLoc.ord _ b = _ from ‹∀ b, _›]
    simp only [← OrientedOrd.eq_swap]

instance : OrientedOrd Loc where eq_swap := loc_compare_swap _ _

private theorem lex_lt_trans {α β : Type} [Ord β] [TransOrd β]
    (cmp : α → α → Ordering) (eq : ∀ a b, cmp a b = .eq ↔ a = b)
    {a b c : α} {x y z : β}
    (trans : cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    (ab : (cmp a b).then (compare x y) = .lt)
    (bc : (cmp b c).then (compare y z) = .lt) :
    (cmp a c).then (compare x z) = .lt := by
  rw [Ordering.then_eq_lt] at ab bc ⊢
  rcases ab with ab | ⟨ab, xy⟩ <;> rcases bc with bc | ⟨bc, yz⟩
  · exact Or.inl (trans ab bc)
  · obtain rfl := (eq _ _).1 bc; exact Or.inl ab
  · obtain rfl := (eq _ _).1 ab; exact Or.inl bc
  · obtain rfl := (eq _ _).1 ab
    obtain rfl := (eq _ _).1 bc
    exact Or.inr ⟨(eq _ _).2 rfl, TransCmp.lt_trans xy yz⟩

attribute [local instance] lexOrd

theorem loc_compare_lt_trans {a b c : Loc}
    (ab : compare a b = .lt) (bc : compare b c = .lt) : compare a c = .lt := by
  change instOrdLoc.ord a b = .lt at ab
  change instOrdLoc.ord b c = .lt at bc
  change instOrdLoc.ord a c = .lt
  induction a generalizing b c with
  | base a =>
    cases b <;> cases c <;> simp only [instOrdLoc.ord] at ab bc ⊢ <;>
      try contradiction <;> try rfl
    exact TransCmp.lt_trans ab bc
  | field a t f ih =>
    cases b <;> cases c <;> simp only [instOrdLoc.ord] at ab bc ⊢ <;>
      try contradiction <;> try rfl
    rename_i b u g c v h
    exact lex_lt_trans instOrdLoc.ord loc_compare_eq_iff ih
      (x := (t.key, f)) (y := (u.key, g)) (z := (v.key, h)) ab bc
  | index a i ih =>
    cases b <;> cases c <;> simp only [instOrdLoc.ord] at ab bc ⊢ <;>
      try contradiction <;> try rfl
    exact lex_lt_trans instOrdLoc.ord loc_compare_eq_iff ih ab bc

instance : TransOrd Loc where
  isLE_trans {a b c} hab hbc := by
    rw [Ordering.isLE_iff_eq_lt_or_eq_eq] at hab hbc ⊢
    rcases hab with hab | hab <;> rcases hbc with hbc | hbc
    · exact Or.inl (loc_compare_lt_trans hab hbc)
    · obtain rfl := (loc_compare_eq_iff _ _).1 hbc; exact Or.inl hab
    · obtain rfl := (loc_compare_eq_iff _ _).1 hab; exact Or.inl hbc
    · obtain rfl := (loc_compare_eq_iff _ _).1 hab; exact Or.inr hbc

end GoLean.GoCore
