import GoLean.GoCore.Multi

/-!
# Sound structural equality over the machine-state tower (POR slice P2)

The dedup certificate checker (`EnumDedupCheck.lean`, design note
`docs/2026-08-21_w32-por-design.md` §3) links a run's concrete successor
state to a certificate node by a Bool comparison, and its completeness
theorem needs that comparison to entail PROPOSITIONAL equality. The
derived `BEq`s on the nested inductives (`Ty`, `GoValue`, `Expr`,
`Stmt`, `Cont`, `Config`) are logically opaque (the documented
partial-stub class, `Value.lean`), and `deriving DecidableEq` fails on
nested inductives — so this layer provides fuel-structural `eqb`s in
`GoValue.eqbFuel`'s exact mold with ONE-DIRECTIONAL soundness theorems:

    eqb a b = true → a = b

Completeness is deliberately NOT claimed: an `eqb` returning `false` on
equal values (fuel exhaustion) makes the checker REFUSE — fail closed,
never unsound. This file has the generic helpers, the flat-type
`==`-soundness lemmas, and soundness for the two EXISTING fuel eqbs
(`Ty.eqbFuel`, `GoValue.eqbFuel`); `SyntaxEqb.lean` and
`MachineEqb.lean` build the `Expr`/`Stmt`/`Cont`/`Config`/state layers
on these.
-/

namespace GoLean

open GoCore

/-! ## Generic parametric helpers (the de-WF recipe: elements free) -/

/-- Pairwise list equality with a free element comparator. -/
def eqbListP {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && eqbListP f as bs
  | _, _ => false

/-- Array equality via `toList`. -/
def eqbArrayP {α : Type} (f : α → α → Bool) (as bs : Array α) : Bool :=
  eqbListP f as.toList bs.toList

/-- Option equality with a free comparator. -/
def eqbOptionP {α : Type} (f : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some a, some b => f a b
  | _, _ => false

/-- Pair equality with free comparators. -/
def eqbProdP {α β : Type} (f : α → α → Bool) (g : β → β → Bool)
    (a : α × β) (b : α × β) : Bool :=
  f a.1 b.1 && g a.2 b.2

theorem eqbListP_sound {α : Type} {f : α → α → Bool}
    (hf : ∀ a b, f a b = true → a = b) :
    ∀ {as bs : List α}, eqbListP f as bs = true → as = bs := by
  intro as
  induction as with
  | nil => intro bs h; cases bs with
    | nil => rfl
    | cons b bs => simp [eqbListP] at h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => simp [eqbListP] at h
    | cons b bs =>
      simp only [eqbListP, Bool.and_eq_true] at h
      cases hf _ _ h.1; cases ih h.2; rfl

theorem array_toList_inj {α : Type} {as bs : Array α}
    (h : as.toList = bs.toList) : as = bs := by
  cases as; cases bs; simpa using h

theorem eqbArrayP_sound {α : Type} {f : α → α → Bool}
    (hf : ∀ a b, f a b = true → a = b) {as bs : Array α}
    (h : eqbArrayP f as bs = true) : as = bs :=
  array_toList_inj (eqbListP_sound hf h)

theorem eqbOptionP_sound {α : Type} {f : α → α → Bool}
    (hf : ∀ a b, f a b = true → a = b) :
    ∀ {a? b? : Option α}, eqbOptionP f a? b? = true → a? = b? := by
  intro a? b? h
  cases a? <;> cases b? <;> simp_all [eqbOptionP]
  exact hf _ _ h

theorem eqbProdP_sound {α β : Type} {f : α → α → Bool} {g : β → β → Bool}
    (hf : ∀ a b, f a b = true → a = b)
    (hg : ∀ a b, g a b = true → a = b)
    {a b : α × β} (h : eqbProdP f g a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [eqbProdP, Bool.and_eq_true] at h
  cases hf _ _ h.1; cases hg _ _ h.2; rfl

/-! ## Flat-type `==` soundness (derived `BEq`s reduce definitionally on
constructor applications: off-diagonal to `false` — `Bool.noConfusion` —
and diagonal to component `==`s). -/

theorem GoCore.IntKind.beq_sound {a b : GoCore.IntKind}
    (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact congrArg _ (eq_of_beq h)
    | exact Bool.noConfusion h

theorem GoCore.FloatKind.beq_sound {a b : GoCore.FloatKind}
    (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

theorem GoCore.SyncKind.beq_sound {a b : GoCore.SyncKind}
    (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

theorem GoCore.ChanDir.beq_sound {a b : GoCore.ChanDir}
    (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

theorem GoString.beq_sound {a b : GoString} (h : (a == b) = true) : a = b := by
  cases a; cases b
  exact congrArg _ (eq_of_beq h)

theorem SliceValue.beq_sound {a b : SliceValue} (h : (a == b) = true) :
    a = b := by
  obtain ⟨ab, ao, al, ac⟩ := a
  obtain ⟨bb, bo, bl, bc⟩ := b
  have h' : (ab == bb && (ao == bo && (al == bl && ac == bc))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  cases eq_of_beq h1; cases eq_of_beq h2; cases eq_of_beq h3
  cases eq_of_beq h4; rfl

theorem MapValue.beq_sound {a b : MapValue} (h : (a == b) = true) : a = b := by
  cases a; cases b
  exact congrArg _ (eq_of_beq h)

theorem ChanValue.beq_sound {a b : ChanValue} (h : (a == b) = true) :
    a = b := by
  cases a; cases b
  exact congrArg _ (eq_of_beq h)

theorem GoCore.FuncId.beq_sound {a b : GoCore.FuncId}
    (h : (a == b) = true) : a = b := by
  cases a; cases b
  exact congrArg _ (eq_of_beq h)

theorem SyncPrim.beq_sound {a b : SyncPrim} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case mutex.mutex x y =>
    cases eq_of_beq (show (x == y) = true from h); rfl
  case rwmutex.rwmutex x1 x2 x3 y1 y2 y3 =>
    have h' : (x1 == y1 && (x2 == y2 && x3 == y3)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    cases eq_of_beq h1; cases eq_of_beq h2; cases eq_of_beq h3; rfl
  case waitGroup.waitGroup x1 x2 y1 y2 =>
    have h' : (x1 == y1 && x2 == y2) = true := h
    simp only [Bool.and_eq_true] at h'
    cases eq_of_beq h'.1; cases eq_of_beq h'.2; rfl
  case once.once x1 x2 y1 y2 =>
    have h' : (x1 == y1 && x2 == y2) = true := h
    simp only [Bool.and_eq_true] at h'
    cases eq_of_beq h'.1; cases eq_of_beq h'.2; rfl

/-! ## `Ty` soundness (the existing mutual fuel eqb) -/

theorem Ty.eqbFuel_sound_all :
    ∀ f, (∀ a b : GoCore.Ty, Ty.eqbFuel f a b = true → a = b)
       ∧ (∀ as bs : List GoCore.Ty, Ty.eqbListFuel f as bs = true → as = bs) := by
  intro f
  induction f with
  | zero =>
    constructor
    · intro a b h
      cases a <;> cases b <;>
        simp_all [Ty.eqbFuel] <;>
        first
          | exact GoCore.IntKind.beq_sound h
          | exact GoCore.FloatKind.beq_sound h
          | exact GoCore.SyncKind.beq_sound h
    · intro as bs h
      cases as <;> cases bs <;> simp_all [Ty.eqbListFuel]
  | succ f ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro a b h
      cases a <;> cases b <;>
        simp_all [Ty.eqbFuel] <;>
        first
          | exact GoCore.IntKind.beq_sound h
          | exact GoCore.FloatKind.beq_sound h
          | exact GoCore.SyncKind.beq_sound h
          | exact ih1 _ _ h
          | exact ⟨ih1 _ _ h.1, ih1 _ _ h.2⟩
          | exact ⟨GoCore.ChanDir.beq_sound h.1, ih1 _ _ h.2⟩
          | exact ⟨ih2 _ _ h.1, ih2 _ _ h.2⟩
          -- funcType: `v₁ == v₂ && eqbList p && eqbList r` flattens to
          -- `(v₁ = v₂ ∧ P) ∧ R` (BUG-067 added the variadic conjunct;
          -- the Bool equality is consumed by simp_all, the lists by ih2).
          | exact ⟨ih2 _ _ h.1.2, ih2 _ _ h.2⟩
          | exact ⟨ih2 _ _ h.1.2, ih2 _ _ h.2.1, h.2.2⟩
          | exact ih1 _ _ h.2
    · intro as bs h
      cases as <;> cases bs <;> simp_all [Ty.eqbListFuel]
      exact ⟨ih1 _ _ h.1, ih2 _ _ h.2⟩

theorem Ty.eqb_sound {a b : GoCore.Ty} (h : Ty.eqb a b = true) : a = b :=
  (Ty.eqbFuel_sound_all tyEqFuel).1 a b h

/-- `Ty`'s `==` IS `Ty.eqb` (the instance in `Value.lean`). -/
theorem Ty.beq_sound {a b : GoCore.Ty} (h : (a == b) = true) : a = b :=
  Ty.eqb_sound h

/-! ## `GoValue` soundness (the existing fuel eqb + its list helpers) -/

theorem GoValue.eqbListWith_sound {f : GoValue → GoValue → Bool}
    (hf : ∀ a b, f a b = true → a = b) :
    ∀ {as bs : List GoValue}, GoValue.eqbListWith f as bs = true → as = bs := by
  intro as
  induction as with
  | nil => intro bs h; cases bs with
    | nil => rfl
    | cons b bs => simp [GoValue.eqbListWith] at h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => simp [GoValue.eqbListWith] at h
    | cons b bs =>
      simp only [GoValue.eqbListWith, Bool.and_eq_true] at h
      cases hf _ _ h.1; cases ih h.2; rfl

theorem GoValue.eqbPairsWith_sound {f : GoValue → GoValue → Bool}
    (hf : ∀ a b, f a b = true → a = b) :
    ∀ {as bs : List (GoValue × GoValue)},
      GoValue.eqbPairsWith f as bs = true → as = bs := by
  intro as
  induction as with
  | nil => intro bs h; cases bs with
    | nil => rfl
    | cons b bs => simp [GoValue.eqbPairsWith] at h
  | cons a as ih =>
    intro bs h
    obtain ⟨k₁, v₁⟩ := a
    cases bs with
    | nil => simp [GoValue.eqbPairsWith] at h
    | cons b bs =>
      obtain ⟨k₂, v₂⟩ := b
      simp only [GoValue.eqbPairsWith, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      cases hf _ _ h1; cases hf _ _ h2
      exact congrArg _ (ih h3)

theorem GoValue.eqbFieldsWith_sound {f : GoValue → GoValue → Bool}
    (hf : ∀ a b, f a b = true → a = b) :
    ∀ {as bs : List (String × GoValue)},
      GoValue.eqbFieldsWith f as bs = true → as = bs := by
  intro as
  induction as with
  | nil => intro bs h; cases bs with
    | nil => rfl
    | cons b bs => simp [GoValue.eqbFieldsWith] at h
  | cons a as ih =>
    intro bs h
    obtain ⟨n₁, v₁⟩ := a
    cases bs with
    | nil => simp [GoValue.eqbFieldsWith] at h
    | cons b bs =>
      obtain ⟨n₂, v₂⟩ := b
      simp only [GoValue.eqbFieldsWith, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      cases eq_of_beq h1; cases hf _ _ h2
      exact congrArg _ (ih h3)

theorem GoValue.eqbFuel_sound :
    ∀ f (a b : GoValue), GoValue.eqbFuel f a b = true → a = b := by
  intro f
  induction f with
  | zero =>
    intro a b h
    cases a <;> cases b <;> (try exact Bool.noConfusion h)
    case unit.unit => rfl
    case nil.nil => rfl
    case bool.bool x y =>
      cases eq_of_beq (show (x == y) = true from h); rfl
    case int.int v₁ k₁ v₂ k₂ =>
      have hxx : _ = true := (show (v₁ == v₂ && k₁ == k₂) = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases eq_of_beq h1; cases GoCore.IntKind.beq_sound h2; rfl
    case float.float b₁ k₁ b₂ k₂ =>
      have hxx : _ = true := (show (b₁ == b₂ && k₁ == k₂) = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases eq_of_beq h1; cases GoCore.FloatKind.beq_sound h2; rfl
    case string.string x y =>
      cases GoString.beq_sound (show (x == y) = true from h); rfl
    case addr.addr x y =>
      cases eq_of_beq (show (x == y) = true from h); rfl
    case slice.slice x y =>
      cases SliceValue.beq_sound (show (x == y) = true from h); rfl
    case map.map x y =>
      cases MapValue.beq_sound (show (x == y) = true from h); rfl
    case chan.chan x y =>
      cases ChanValue.beq_sound (show (x == y) = true from h); rfl
    case syncData.syncData x y =>
      cases SyncPrim.beq_sound (show (x == y) = true from h); rfl
  | succ f ih =>
    intro a b h
    cases a <;> cases b <;> (try exact Bool.noConfusion h)
    case unit.unit => rfl
    case nil.nil => rfl
    case bool.bool x y =>
      cases eq_of_beq (show (x == y) = true from h); rfl
    case int.int v₁ k₁ v₂ k₂ =>
      have hxx : _ = true := (show (v₁ == v₂ && k₁ == k₂) = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases eq_of_beq h1; cases GoCore.IntKind.beq_sound h2; rfl
    case float.float b₁ k₁ b₂ k₂ =>
      have hxx : _ = true := (show (b₁ == b₂ && k₁ == k₂) = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases eq_of_beq h1; cases GoCore.FloatKind.beq_sound h2; rfl
    case string.string x y =>
      cases GoString.beq_sound (show (x == y) = true from h); rfl
    case addr.addr x y =>
      cases eq_of_beq (show (x == y) = true from h); rfl
    case slice.slice x y =>
      cases SliceValue.beq_sound (show (x == y) = true from h); rfl
    case map.map x y =>
      cases MapValue.beq_sound (show (x == y) = true from h); rfl
    case chan.chan x y =>
      cases ChanValue.beq_sound (show (x == y) = true from h); rfl
    case syncData.syncData x y =>
      cases SyncPrim.beq_sound (show (x == y) = true from h); rfl
    case interface.interface t₁ v₁ t₂ v₂ =>
      have hxx : _ = true := (show (GoCore.Ty.eqb t₁ t₂ && GoValue.eqbFuel f v₁ v₂) = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases Ty.eqb_sound h1; cases ih _ _ h2; rfl
    case struct.struct id₁ fs₁ id₂ fs₂ =>
      have hxx : _ = true := (show (id₁ == id₂
          && GoValue.eqbFieldsWith (GoValue.eqbFuel f) fs₁.toList fs₂.toList)
          = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases eq_of_beq h1
      cases array_toList_inj (GoValue.eqbFieldsWith_sound ih h2); rfl
    case array.array x y =>
      cases array_toList_inj (GoValue.eqbListWith_sound ih
        (show GoValue.eqbListWith (GoValue.eqbFuel f) x.toList y.toList = true
          from h)); rfl
    case mapData.mapData x y =>
      cases array_toList_inj (GoValue.eqbPairsWith_sound ih
        (show GoValue.eqbPairsWith (GoValue.eqbFuel f) x.toList y.toList = true
          from h)); rfl
    case chanData.chanData b₁ c₁ k₁ b₂ c₂ k₂ =>
      have hxx : _ = true := (show ((c₁ == c₂ && k₁ == k₂)
          && GoValue.eqbListWith (GoValue.eqbFuel f) b₁.toList b₂.toList)
          = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxx
      cases eq_of_beq h1; cases eq_of_beq h2
      cases array_toList_inj (GoValue.eqbListWith_sound ih h3); rfl
    case funcVal.funcVal id₁ c₁ id₂ c₂ =>
      have hxx : _ = true := (show (id₁ == id₂
          && GoValue.eqbListWith (GoValue.eqbFuel f) c₁ c₂) = true from h)
      simp only [Bool.and_eq_true] at hxx
      obtain ⟨h1, h2⟩ := hxx
      cases GoCore.FuncId.beq_sound h1
      cases GoValue.eqbListWith_sound ih h2; rfl

theorem GoValue.eqb_sound {a b : GoValue} (h : GoValue.eqb a b = true) :
    a = b :=
  GoValue.eqbFuel_sound valueEqbFuel a b h

/-- `GoValue`'s `==` IS `GoValue.eqb` (the instance in `Value.lean`). -/
theorem GoValue.beq_sound {a b : GoValue} (h : (a == b) = true) : a = b :=
  GoValue.eqb_sound h

end GoLean
