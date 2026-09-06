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
nested inductives — so this layer provides structural `eqb`s in
`GoValue.eqb`'s exact mold (mutual structural recursion over the nested
inductives since C2, 2026-09-05; the fuel-structural `eqbFuel`s they
replaced are gone) with ONE-DIRECTIONAL soundness theorems:

    eqb a b = true → a = b

Completeness is deliberately NOT claimed: an `eqb` returning `false` on
equal values makes the checker REFUSE — fail closed, never unsound. This
file has the generic helpers, the flat-type `==`-soundness lemmas, and
soundness for the two EXISTING structural eqbs of `Value.lean`
(`Ty.eqb`, `GoValue.eqb`: `Ty.eqb_sound_all`, `GoValue.eqb_sound_all`
by `mutual_induct`); `SyntaxEqb.lean` and
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

/-- Soundness of the structural `Ty` equality and its list companion, by
the mutual functional induction the structural definition generates (C2:
the fuel induction went with the fuel). One case per match arm, in the
definition's order. -/
theorem Ty.eqb_sound_all :
    (∀ a b : GoCore.Ty, Ty.eqb a b = true → a = b)
      ∧ (∀ as bs : List GoCore.Ty, Ty.eqbList as bs = true → as = bs) := by
  apply Ty.eqb.mutual_induct
  all_goals intros
  all_goals simp only [Ty.eqb, Ty.eqbList, Bool.and_eq_true] at *
  all_goals try rfl
  case case2 => rename_i h; exact congrArg _ (GoCore.IntKind.beq_sound h)
  case case3 => rename_i h; exact congrArg _ (GoCore.FloatKind.beq_sound h)
  case case5 => rename_i ih h; rw [eq_of_beq h.1, ih h.2]
  case case6 => rename_i ih h; exact congrArg _ (ih h)
  case case7 => rename_i ih2 ih1 h; rw [ih2 h.1, ih1 h.2]
  case case8 => rename_i ih h; rw [GoCore.ChanDir.beq_sound h.1, ih h.2]
  case case9 => rename_i ih h; exact congrArg _ (ih h)
  case case10 =>
    rename_i ih2 ih1 h
    obtain ⟨⟨hv, hp⟩, hr⟩ := h
    rw [eq_of_beq hv, ih2 hp, ih1 hr]
  case case11 => rename_i h; exact congrArg _ (eq_of_beq h)
  case case12 => rename_i h; exact congrArg _ (eq_of_beq h)
  case case13 => rename_i h; exact congrArg _ (eq_of_beq h)
  case case14 => rename_i h; exact congrArg _ (GoCore.SyncKind.beq_sound h)
  case case15 => exact Bool.noConfusion ‹false = true›
  case case17 => rename_i ih2 ih1 h; rw [ih2 h.1, ih1 h.2]
  case case18 => exact Bool.noConfusion ‹false = true›

theorem Ty.eqb_sound {a b : GoCore.Ty} (h : Ty.eqb a b = true) : a = b :=
  Ty.eqb_sound_all.1 a b h

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

theorem GoValue.eqbTriplesWith_sound {f : GoValue → GoValue → Bool}
    (hf : ∀ a b, f a b = true → a = b) :
    ∀ {as bs : List (Nat × GoValue × GoValue)},
      GoValue.eqbTriplesWith f as bs = true → as = bs := by
  intro as
  induction as with
  | nil => intro bs h; cases bs with
    | nil => rfl
    | cons b bs => simp [GoValue.eqbTriplesWith] at h
  | cons a as ih =>
    intro bs h
    obtain ⟨i₁, k₁, v₁⟩ := a
    cases bs with
    | nil => simp [GoValue.eqbTriplesWith] at h
    | cons b bs =>
      obtain ⟨i₂, k₂, v₂⟩ := b
      simp only [GoValue.eqbTriplesWith, Bool.and_eq_true] at h
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
      cases eq_of_beq h0; cases hf _ _ h1; cases hf _ _ h2
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

/-- Soundness of the structural `GoValue` equality and its two list
companions, by the mutual functional induction (C2). One case per match
arm, in the definition's order. -/
theorem GoValue.eqb_sound_all :
    (∀ a b : GoValue, GoValue.eqb a b = true → a = b)
      ∧ (∀ as bs : List GoValue, GoValue.eqbList as bs = true → as = bs)
      ∧ (∀ as bs : List (String × GoValue), GoValue.eqbFieldList as bs = true → as = bs) := by
  apply GoValue.eqb.mutual_induct
  all_goals intros
  all_goals simp only [GoValue.eqb, GoValue.eqbList, GoValue.eqbFieldList, Bool.and_eq_true] at *
  all_goals try rfl
  case case2 => rename_i h; exact congrArg _ (eq_of_beq h)
  case case3 =>
    rename_i h
    rw [eq_of_beq h.1, GoCore.IntKind.beq_sound h.2]
  case case4 =>
    rename_i h
    rw [eq_of_beq h.1, GoCore.FloatKind.beq_sound h.2]
  case case5 => rename_i h; exact congrArg _ (GoString.beq_sound h)
  case case6 => rename_i h; exact congrArg _ (eq_of_beq h)
  case case8 => rename_i ih h; rw [Ty.eqb_sound h.1, ih h.2]
  case case9 =>
    rename_i ih h
    rw [eq_of_beq h.1, ih h.2]
  case case10 => rename_i ih h; rw [ih h]
  case case11 => rename_i h; exact congrArg _ (SliceValue.beq_sound h)
  case case12 => rename_i h; exact congrArg _ (MapValue.beq_sound h)
  case case13 => rename_i h; exact congrArg _ (ChanValue.beq_sound h)
  case case14 =>
    rename_i ih h
    rw [GoCore.FuncId.beq_sound h.1, ih h.2]
  case case15 => rename_i h; exact congrArg _ (SyncPrim.beq_sound h)
  all_goals first
    | exact Bool.noConfusion ‹false = true›
    | (rename_i ih2 ih1 h; rw [ih2 h.1, ih1 h.2])
    | (rename_i ih2 ih1 h
       obtain ⟨⟨hn, hv⟩, hrest⟩ := h
       rw [eq_of_beq hn, ih2 hv, ih1 hrest])

theorem GoValue.eqb_sound {a b : GoValue} (h : GoValue.eqb a b = true) :
    a = b :=
  GoValue.eqb_sound_all.1 a b h

/-- `GoValue`'s `==` IS `GoValue.eqb` (the instance in `Value.lean`). -/
theorem GoValue.beq_sound {a b : GoValue} (h : (a == b) = true) : a = b :=
  GoValue.eqb_sound h

end GoLean
