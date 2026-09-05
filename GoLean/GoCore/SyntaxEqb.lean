import GoLean.GoCore.StateEqb

/-!
# Sound structural equality over the Go SYNTAX tower (POR slice P2)

`StateEqb.lean` builds the value/state half of the sound-`eqb` layer
(design note `docs/2026-08-21_w32-por-design.md` §3); this file is the
SYNTAX half — `Expr`, `Assignee`, `SelectClauseHead`, `Stmt`, and the
declaration-level records (`Param`, `FieldDef`, `MethodSig`, `TypeDef`,
`GlobalDef`, `MethodInfo`, `MethodSetRecord`, `Func`).

Same contract, same mould (`GoValue.eqbFuel`): fuel-structural `eqb`s
with ONE-DIRECTIONAL soundness,

    eqb a b = true → a = b

and completeness deliberately NOT claimed. Fuel exhaustion makes an
`eqb` answer `false`, which makes every consumer REFUSE — fail closed,
never unsound. `deriving DecidableEq` is unavailable here (`Expr` and
`Stmt` are NESTED inductives, through `Array`/`Prod`) and the derived
`BEq`s are logically opaque, which is exactly the gap this layer fills.

Every constructor of every covered type has an explicit diagonal arm;
the only catch-alls are the terminal `| _, _ => false` of each match.
-/

namespace GoLean.GoCore

/-! ## Conjunction splitters

The diagonal arms are LEFT-associated `&&` chains (`A && B && C` is
`(A && B) && C`). These splitters let a soundness case name the
component hypotheses without respelling the arm: unification reduces
the `eqb` application on two equal constructors to the arm's body. -/

theorem andSplit2 {A B : Bool} (h : (A && B) = true) :
    A = true ∧ B = true := by
  simp only [Bool.and_eq_true] at h; exact h

theorem andSplit3 {A B C : Bool} (h : (A && B && C) = true) :
    A = true ∧ B = true ∧ C = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem andSplit4 {A B C D : Bool} (h : (A && B && C && D) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem andSplit5 {A B C D E : Bool} (h : (A && B && C && D && E) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem andSplit6 {A B C D E F : Bool}
    (h : (A && B && C && D && E && F) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## The field-free enums (derived `BEq`, no `LawfulBEq` instance) -/

theorem SyncStmtOp.beq_sound {a b : SyncStmtOp} (h : (a == b) = true) :
    a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

theorem AtomicStmtOp.beq_sound {a b : AtomicStmtOp} (h : (a == b) = true) :
    a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

theorem FloatBitsOp.beq_sound {a b : FloatBitsOp} (h : (a == b) = true) :
    a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

theorem MethodSetCoverage.beq_sound {a b : MethodSetCoverage}
    (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact Bool.noConfusion h

/-! ## `Expr` -/

/-- Fuel-structural `Expr` equality. Recursive positions descend at
`f`; flat fields use their (lawful, or separately sound) `==`; `Ty`
fields use `Ty.eqb`. Fuel 0 answers `false` — refuse, never guess. -/
def Expr.eqbF : Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match a, b with
    | .var x, .var y => x == y
    | .nil t1, .nil t2 => eqbOptionP Ty.eqb t1 t2
    | .intLit v1 k1, .intLit v2 k2 => v1 == v2 && k1 == k2
    | .floatLit n1 d1 k1, .floatLit n2 d2 k2 =>
        n1 == n2 && d1 == d2 && k1 == k2
    | .stringLit s1, .stringLit s2 => s1 == s2
    | .boolLit b1, .boolLit b2 => b1 == b2
    | .convert t1 o1, .convert t2 o2 => Ty.eqb t1 t2 && Expr.eqbF f o1 o2
    | .bytesFromString o1, .bytesFromString o2 => Expr.eqbF f o1 o2
    | .stringFromByteSlice o1, .stringFromByteSlice o2 => Expr.eqbF f o1 o2
    | .stringFromRune o1, .stringFromRune o2 => Expr.eqbF f o1 o2
    | .add l1 r1, .add l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .sub l1 r1, .sub l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .mul l1 r1, .mul l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .div l1 r1, .div l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .mod l1 r1, .mod l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .shiftLeft l1 r1, .shiftLeft l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .shiftRight l1 r1, .shiftRight l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .bitAnd l1 r1, .bitAnd l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .bitOr l1 r1, .bitOr l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .bitXor l1 r1, .bitXor l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .bitClear l1 r1, .bitClear l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .bitNeg o1, .bitNeg o2 => Expr.eqbF f o1 o2
    | .neg o1, .neg o2 => Expr.eqbF f o1 o2
    | .eqCmp t1 l1 r1, .eqCmp t2 l2 r2 =>
        Ty.eqb t1 t2 && Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .neqCmp t1 l1 r1, .neqCmp t2 l2 r2 =>
        Ty.eqb t1 t2 && Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .atMostCmp l1 r1, .atMostCmp l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .atLeastCmp l1 r1, .atLeastCmp l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .lessCmp l1 r1, .lessCmp l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .greaterCmp l1 r1, .greaterCmp l2 r2 =>
        Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .and l1 r1, .and l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .or l1 r1, .or l2 r2 => Expr.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .not o1, .not o2 => Expr.eqbF f o1 o2
    | .ref x, .ref y => x == y
    | .funcVal i1 c1, .funcVal i2 c2 =>
        i1 == i2 && eqbArrayP (Expr.eqbF f) c1 c2
    | .global g1, .global g2 => g1 == g2
    | .deref p1 t1, .deref p2 t2 => Expr.eqbF f p1 p2 && Ty.eqb t1 t2
    | .addrOfDeref p1, .addrOfDeref p2 => Expr.eqbF f p1 p2
    | .structLit t1 a1, .structLit t2 a2 =>
        Ty.eqb t1 t2 && eqbArrayP (Expr.eqbF f) a1 a2
    | .fieldGet r1 i1 n1, .fieldGet r2 i2 n2 =>
        Expr.eqbF f r1 r2 && i1 == i2 && n1 == n2
    | .fieldAddr b1 i1 n1, .fieldAddr b2 i2 n2 =>
        Expr.eqbF f b1 b2 && i1 == i2 && n1 == n2
    | .arrayLit n1 e1 a1, .arrayLit n2 e2 a2 =>
        n1 == n2 && Ty.eqb e1 e2
          && eqbArrayP (eqbProdP (· == ·) (Expr.eqbF f)) a1 a2
    | .defaultValue t1, .defaultValue t2 => Ty.eqb t1 t2
    | .toInterface g1 d1 o1, .toInterface g2 d2 o2 =>
        Ty.eqb g1 g2 && Ty.eqb d1 d2 && Expr.eqbF f o1 o2
    | .typeAssert o1 t1 s1, .typeAssert o2 t2 s2 =>
        Expr.eqbF f o1 o2 && Ty.eqb t1 t2 && eqbOptionP Ty.eqb s1 s2
    | .indexGet b1 i1, .indexGet b2 i2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f i1 i2
    | .indexAddr b1 i1, .indexAddr b2 i2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f i1 i2
    | .mapGet b1 i1 k1 v1, .mapGet b2 i2 k2 v2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f i1 i2 && Ty.eqb k1 k2 && Ty.eqb v1 v2
    | .slice b1 lo1 hi1 m1, .slice b2 lo2 hi2 m2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f lo1 lo2 && Expr.eqbF f hi1 hi2
          && eqbOptionP (Expr.eqbF f) m1 m2
    | .length o1 t1, .length o2 t2 =>
        Expr.eqbF f o1 o2 && eqbOptionP Ty.eqb t1 t2
    | .capacity o1 t1, .capacity o2 t2 =>
        Expr.eqbF f o1 o2 && eqbOptionP Ty.eqb t1 t2
    | .minOf a1, .minOf a2 => eqbArrayP (Expr.eqbF f) a1 a2
    | .maxOf a1, .maxOf a2 => eqbArrayP (Expr.eqbF f) a1 a2
    | .runeAt s1 o1, .runeAt s2 o2 => Expr.eqbF f s1 s2 && Expr.eqbF f o1 o2
    | .runeSizeAt s1 o1, .runeSizeAt s2 o2 =>
        Expr.eqbF f s1 s2 && Expr.eqbF f o1 o2
    | .runesFromString o1, .runesFromString o2 => Expr.eqbF f o1 o2
    | .stringFromRuneSlice o1, .stringFromRuneSlice o2 => Expr.eqbF f o1 o2
    | .floatBits p1 o1, .floatBits p2 o2 => p1 == p2 && Expr.eqbF f o1 o2
    | .recoverCall, .recoverCall => true
    | .unsupported x, .unsupported y => x == y
    | _, _ => false

set_option maxHeartbeats 1600000 in
theorem Expr.eqbF_sound : ∀ f (a b : Expr), Expr.eqbF f a b = true → a = b := by
  intro f
  induction f with
  | zero => intro a b h; exact Bool.noConfusion h
  | succ f ih =>
    intro a b h
    cases a <;> cases b <;> (try exact Bool.noConfusion h)
    case var.var x y => cases eq_of_beq (show (x == y) = true from h); rfl
    case nil.nil t1 t2 =>
      cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h; rfl
    case intLit.intLit v1 k1 v2 k2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eq_of_beq h1; cases IntKind.beq_sound h2; rfl
    case floatLit.floatLit n1 d1 k1 n2 d2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eq_of_beq h1; cases eq_of_beq h2; cases FloatKind.beq_sound h3; rfl
    case stringLit.stringLit s1 s2 =>
      cases GoString.beq_sound (show (s1 == s2) = true from h); rfl
    case boolLit.boolLit b1 b2 =>
      cases eq_of_beq (show (b1 == b2) = true from h); rfl
    case convert.convert t1 o1 t2 o2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Ty.eqb_sound h1; cases ih _ _ h2; rfl
    case bytesFromString.bytesFromString o1 o2 => cases ih _ _ h; rfl
    case stringFromByteSlice.stringFromByteSlice o1 o2 => cases ih _ _ h; rfl
    case stringFromRune.stringFromRune o1 o2 => cases ih _ _ h; rfl
    case add.add l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case sub.sub l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case mul.mul l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case div.div l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case mod.mod l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case shiftLeft.shiftLeft l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case shiftRight.shiftRight l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case bitAnd.bitAnd l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case bitOr.bitOr l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case bitXor.bitXor l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case bitClear.bitClear l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case bitNeg.bitNeg o1 o2 => cases ih _ _ h; rfl
    case neg.neg o1 o2 => cases ih _ _ h; rfl
    case eqCmp.eqCmp t1 l1 r1 t2 l2 r2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Ty.eqb_sound h1; cases ih _ _ h2; cases ih _ _ h3; rfl
    case neqCmp.neqCmp t1 l1 r1 t2 l2 r2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Ty.eqb_sound h1; cases ih _ _ h2; cases ih _ _ h3; rfl
    case atMostCmp.atMostCmp l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case atLeastCmp.atLeastCmp l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case lessCmp.lessCmp l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case greaterCmp.greaterCmp l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case and.and l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case or.or l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case not.not o1 o2 => cases ih _ _ h; rfl
    case ref.ref x y => cases eq_of_beq (show (x == y) = true from h); rfl
    case funcVal.funcVal i1 c1 i2 c2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases FuncId.beq_sound h1; cases eqbArrayP_sound ih h2; rfl
    case global.global g1 g2 =>
      cases eq_of_beq (show (g1 == g2) = true from h); rfl
    case deref.deref p1 t1 p2 t2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases ih _ _ h1; cases Ty.eqb_sound h2; rfl
    case addrOfDeref.addrOfDeref p1 p2 => cases ih _ _ h; rfl
    case structLit.structLit t1 a1 t2 a2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Ty.eqb_sound h1; cases eqbArrayP_sound ih h2; rfl
    case fieldGet.fieldGet r1 i1 n1 r2 i2 n2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases ih _ _ h1; cases eq_of_beq h2; cases eq_of_beq h3; rfl
    case fieldAddr.fieldAddr b1 i1 n1 b2 i2 n2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases ih _ _ h1; cases eq_of_beq h2; cases eq_of_beq h3; rfl
    case arrayLit.arrayLit n1 e1 a1 n2 e2 a2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eq_of_beq h1; cases Ty.eqb_sound h2
      cases eqbArrayP_sound
        (fun _ _ hh => eqbProdP_sound (fun _ _ k => eq_of_beq k) ih hh) h3
      rfl
    case defaultValue.defaultValue t1 t2 =>
      cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
    case toInterface.toInterface g1 d1 o1 g2 d2 o2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Ty.eqb_sound h1; cases Ty.eqb_sound h2; cases ih _ _ h3; rfl
    case typeAssert.typeAssert o1 t1 s1 o2 t2 s2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases ih _ _ h1; cases Ty.eqb_sound h2
      cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h3; rfl
    case indexGet.indexGet b1 i1 b2 i2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case indexAddr.indexAddr b1 i1 b2 i2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case mapGet.mapGet b1 i1 k1 v1 b2 i2 k2 v2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases ih _ _ h1; cases ih _ _ h2
      cases Ty.eqb_sound h3; cases Ty.eqb_sound h4; rfl
    case slice.slice b1 lo1 hi1 m1 b2 lo2 hi2 m2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases ih _ _ h1; cases ih _ _ h2; cases ih _ _ h3
      cases eqbOptionP_sound ih h4; rfl
    case length.length o1 t1 o2 t2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases ih _ _ h1
      cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h2; rfl
    case capacity.capacity o1 t1 o2 t2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases ih _ _ h1
      cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h2; rfl
    case minOf.minOf a1 a2 => cases eqbArrayP_sound ih h; rfl
    case maxOf.maxOf a1 a2 => cases eqbArrayP_sound ih h; rfl
    case runeAt.runeAt s1 o1 s2 o2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case runeSizeAt.runeSizeAt s1 o1 s2 o2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h; cases ih _ _ h1; cases ih _ _ h2; rfl
    case runesFromString.runesFromString o1 o2 => cases ih _ _ h; rfl
    case stringFromRuneSlice.stringFromRuneSlice o1 o2 => cases ih _ _ h; rfl
    case floatBits.floatBits p1 o1 p2 o2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases FloatBitsOp.beq_sound h1; cases ih _ _ h2; rfl
    case recoverCall.recoverCall => rfl
    case unsupported.unsupported x y =>
      cases eq_of_beq (show (x == y) = true from h); rfl

/-! ## `Assignee` and `SelectClauseHead`

Neither is self-recursive: both bottom out in `Expr`/`Ty`, so the fuel
is merely threaded through to `Expr.eqbF` (they are always invoked with
an already-decremented fuel). -/

def Assignee.eqbF : Nat → Assignee → Assignee → Bool
  | f, a, b =>
    match a, b with
    | .var x, .var y => x == y
    | .addr l1, .addr l2 => Expr.eqbF f l1 l2
    | .mapElem b1 i1 k1 v1, .mapElem b2 i2 k2 v2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f i1 i2 && Ty.eqb k1 k2 && Ty.eqb v1 v2
    | .unsupported x, .unsupported y => x == y
    | _, _ => false

theorem Assignee.eqbF_sound :
    ∀ f (a b : Assignee), Assignee.eqbF f a b = true → a = b := by
  intro f a b h
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case var.var x y => cases eq_of_beq (show (x == y) = true from h); rfl
  case addr.addr l1 l2 => cases Expr.eqbF_sound _ _ _ h; rfl
  case mapElem.mapElem b1 i1 k1 v1 b2 i2 k2 v2 =>
    obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
    cases Expr.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
    cases Ty.eqb_sound h3; cases Ty.eqb_sound h4; rfl
  case unsupported.unsupported x y =>
    cases eq_of_beq (show (x == y) = true from h); rfl

def SelectClauseHead.eqbF :
    Nat → SelectClauseHead → SelectClauseHead → Bool
  | f, a, b =>
    match a, b with
    | .send c1 v1 e1, .send c2 v2 e2 =>
        Expr.eqbF f c1 c2 && Expr.eqbF f v1 v2 && Ty.eqb e1 e2
    | .recv t1 c1 e1, .recv t2 c2 e2 =>
        eqbArrayP (Assignee.eqbF f) t1 t2 && Expr.eqbF f c1 c2 && Ty.eqb e1 e2
    | _, _ => false

theorem SelectClauseHead.eqbF_sound :
    ∀ f (a b : SelectClauseHead), SelectClauseHead.eqbF f a b = true → a = b := by
  intro f a b h
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case send.send c1 v1 e1 c2 v2 e2 =>
    obtain ⟨h1, h2, h3⟩ := andSplit3 h
    cases Expr.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
    cases Ty.eqb_sound h3; rfl
  case recv.recv t1 c1 e1 t2 c2 e2 =>
    obtain ⟨h1, h2, h3⟩ := andSplit3 h
    cases eqbArrayP_sound (Assignee.eqbF_sound f) h1
    cases Expr.eqbF_sound _ _ _ h2; cases Ty.eqb_sound h3; rfl

/-! ## The declaration-level records (no recursion through `Stmt`) -/

def Param.eqb (a b : Param) : Bool :=
  a.id == b.id && Ty.eqb a.typ b.typ

theorem Param.eqb_sound (a b : Param) (h : Param.eqb a b = true) : a = b := by
  obtain ⟨i1, t1⟩ := a
  obtain ⟨i2, t2⟩ := b
  obtain ⟨h1, h2⟩ := andSplit2 h
  cases eq_of_beq h1; cases Ty.eqb_sound h2; rfl

def FieldDef.eqb (a b : FieldDef) : Bool :=
  a.name == b.name && Ty.eqb a.typ b.typ && a.embedded == b.embedded

theorem FieldDef.eqb_sound (a b : FieldDef) (h : FieldDef.eqb a b = true) :
    a = b := by
  obtain ⟨n1, t1, e1⟩ := a
  obtain ⟨n2, t2, e2⟩ := b
  obtain ⟨h1, h2, h3⟩ := andSplit3 h
  cases eq_of_beq h1; cases Ty.eqb_sound h2; cases eq_of_beq h3; rfl

def MethodSig.eqb (a b : MethodSig) : Bool :=
  a.name == b.name && eqbArrayP Ty.eqb a.params b.params
    && eqbArrayP Ty.eqb a.results b.results && a.variadic == b.variadic

theorem MethodSig.eqb_sound (a b : MethodSig) (h : MethodSig.eqb a b = true) :
    a = b := by
  obtain ⟨n1, p1, r1, v1⟩ := a
  obtain ⟨n2, p2, r2, v2⟩ := b
  obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
  cases eq_of_beq h1
  cases eqbArrayP_sound (fun _ _ hh => Ty.eqb_sound hh) h2
  cases eqbArrayP_sound (fun _ _ hh => Ty.eqb_sound hh) h3
  cases eq_of_beq h4; rfl

def TypeDef.eqb : TypeDef → TypeDef → Bool
  | .struct f1, .struct f2 => eqbArrayP FieldDef.eqb f1 f2
  | .alias t1, .alias t2 => Ty.eqb t1 t2
  | .interfaceDef m1, .interfaceDef m2 => eqbArrayP MethodSig.eqb m1 m2
  | .defined u1, .defined u2 => Ty.eqb u1 u2
  | .opaqueDecl x, .opaqueDecl y => x == y
  | _, _ => false

theorem TypeDef.eqb_sound (a b : TypeDef) (h : TypeDef.eqb a b = true) :
    a = b := by
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case struct.struct f1 f2 =>
    cases eqbArrayP_sound FieldDef.eqb_sound h; rfl
  case alias.alias t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case interfaceDef.interfaceDef m1 m2 =>
    cases eqbArrayP_sound MethodSig.eqb_sound h; rfl
  case defined.defined u1 u2 =>
    cases Ty.eqb_sound (show Ty.eqb u1 u2 = true from h); rfl
  case opaqueDecl.opaqueDecl x y =>
    cases eq_of_beq (show (x == y) = true from h); rfl

def GlobalDef.eqb (a b : GlobalDef) : Bool :=
  a.name == b.name && Ty.eqb a.typ b.typ

theorem GlobalDef.eqb_sound (a b : GlobalDef) (h : GlobalDef.eqb a b = true) :
    a = b := by
  obtain ⟨n1, t1⟩ := a
  obtain ⟨n2, t2⟩ := b
  obtain ⟨h1, h2⟩ := andSplit2 h
  cases eq_of_beq h1; cases Ty.eqb_sound h2; rfl

def MethodInfo.eqb (a b : MethodInfo) : Bool :=
  a.name == b.name && a.funcId == b.funcId && Ty.eqb a.recv b.recv

theorem MethodInfo.eqb_sound (a b : MethodInfo)
    (h : MethodInfo.eqb a b = true) : a = b := by
  obtain ⟨n1, f1, r1⟩ := a
  obtain ⟨n2, f2, r2⟩ := b
  obtain ⟨h1, h2, h3⟩ := andSplit3 h
  cases eq_of_beq h1; cases FuncId.beq_sound h2; cases Ty.eqb_sound h3; rfl

theorem MethodSetRecord.beq_sound {a b : MethodSetRecord}
    (h : (a == b) = true) : a = b := by
  obtain ⟨k1, c1⟩ := a
  obtain ⟨k2, c2⟩ := b
  obtain ⟨h1, h2⟩ := andSplit2 h
  cases eq_of_beq h1; cases MethodSetCoverage.beq_sound h2; rfl

/-! ## `Stmt` -/

/-- Fuel-structural `Stmt` equality: self-recursive on the fuel, with
`Expr`/`Assignee`/`SelectClauseHead` compared at the same decremented
fuel. Fuel 0 answers `false`. -/
def Stmt.eqbF : Nat → Stmt → Stmt → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match a, b with
    | .seqn s1, .seqn s2 => eqbArrayP (Stmt.eqbF f) s1 s2
    | .block d1 s1, .block d2 s2 =>
        eqbArrayP Param.eqb d1 d2 && eqbArrayP (Stmt.eqbF f) s1 s2
    | .breakable b1, .breakable b2 => Stmt.eqbF f b1 b2
    | .initialization v1, .initialization v2 => Param.eqb v1 v2
    | .assign l1 r1, .assign l2 r2 =>
        Assignee.eqbF f l1 l2 && Expr.eqbF f r1 r2
    | .assignMany l1 r1, .assignMany l2 r2 =>
        eqbArrayP (Assignee.eqbF f) l1 l2 && eqbArrayP (Expr.eqbF f) r1 r2
    | .allocNew t1 v1 y1, .allocNew t2 v2 y2 =>
        Assignee.eqbF f t1 t2 && Expr.eqbF f v1 v2 && Ty.eqb y1 y2
    | .makeSlice t1 e1 l1 c1, .makeSlice t2 e2 l2 c2 =>
        Assignee.eqbF f t1 t2 && Ty.eqb e1 e2 && Expr.eqbF f l1 l2
          && eqbOptionP (Expr.eqbF f) c1 c2
    | .makeMap t1 k1 v1 i1, .makeMap t2 k2 v2 i2 =>
        Assignee.eqbF f t1 t2 && Ty.eqb k1 k2 && Ty.eqb v1 v2
          && eqbOptionP (Expr.eqbF f) i1 i2
    | .mapAssign b1 i1 v1 k1 w1, .mapAssign b2 i2 v2 k2 w2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f i1 i2 && Expr.eqbF f v1 v2
          && Ty.eqb k1 k2 && Ty.eqb w1 w2
    | .mapDelete b1 i1 k1, .mapDelete b2 i2 k2 =>
        Expr.eqbF f b1 b2 && Expr.eqbF f i1 i2 && Ty.eqb k1 k2
    | .clearMap b1, .clearMap b2 => Expr.eqbF f b1 b2
    | .clearSlice b1 e1, .clearSlice b2 e2 =>
        Expr.eqbF f b1 b2 && Ty.eqb e1 e2
    | .sortSlice b1 e1, .sortSlice b2 e2 =>
        Expr.eqbF f b1 b2 && Ty.eqb e1 e2
    | .mapLookup t1 o1 b1 i1 k1 v1, .mapLookup t2 o2 b2 i2 k2 v2 =>
        Assignee.eqbF f t1 t2 && Assignee.eqbF f o1 o2 && Expr.eqbF f b1 b2
          && Expr.eqbF f i1 i2 && Ty.eqb k1 k2 && Ty.eqb v1 v2
    | .typeAssert t1 o1 e1 y1, .typeAssert t2 o2 e2 y2 =>
        Assignee.eqbF f t1 t2 && Assignee.eqbF f o1 o2 && Expr.eqbF f e1 e2
          && Ty.eqb y1 y2
    | .appendSlice t1 e1 s1 l1, .appendSlice t2 e2 s2 l2 =>
        Assignee.eqbF f t1 t2 && Ty.eqb e1 e2 && Expr.eqbF f s1 s2
          && Expr.eqbF f l1 l2
    | .copySlice t1 d1 s1, .copySlice t2 d2 s2 =>
        Assignee.eqbF f t1 t2 && Expr.eqbF f d1 d2 && Expr.eqbF f s1 s2
    | .call t1 n1 a1, .call t2 n2 a2 =>
        eqbArrayP (Assignee.eqbF f) t1 t2 && n1 == n2
          && eqbArrayP (Expr.eqbF f) a1 a2
    | .callValue t1 c1 a1, .callValue t2 c2 a2 =>
        eqbArrayP (Assignee.eqbF f) t1 t2 && Expr.eqbF f c1 c2
          && eqbArrayP (Expr.eqbF f) a1 a2
    | .deferCall c1 a1, .deferCall c2 a2 =>
        Expr.eqbF f c1 c2 && eqbArrayP (Expr.eqbF f) a1 a2
    | .ifThenElse c1 t1 e1, .ifThenElse c2 t2 e2 =>
        Expr.eqbF f c1 c2 && Stmt.eqbF f t1 t2 && Stmt.eqbF f e1 e2
    | .while c1 b1, .while c2 b2 => Expr.eqbF f c1 c2 && Stmt.eqbF f b1 b2
    | .mapRange k1 v1 m1 kt1 vt1 b1, .mapRange k2 v2 m2 kt2 vt2 b2 =>
        eqbOptionP (· == ·) k1 k2 && eqbOptionP (· == ·) v1 v2
          && Expr.eqbF f m1 m2 && Ty.eqb kt1 kt2 && Ty.eqb vt1 vt2
          && Stmt.eqbF f b1 b2
    | .returnStmt, .returnStmt => true
    | .breakStmt, .breakStmt => true
    | .continueStmt, .continueStmt => true
    | .labeled l1 b1, .labeled l2 b2 => l1 == l2 && Stmt.eqbF f b1 b2
    | .breakTo l1, .breakTo l2 => l1 == l2
    | .continueTo l1, .continueTo l2 => l1 == l2
    | .panicStmt p1, .panicStmt p2 => Expr.eqbF f p1 p2
    | .inertLabel n1, .inertLabel n2 => n1 == n2
    | .makeChan t1 e1 c1, .makeChan t2 e2 c2 =>
        Assignee.eqbF f t1 t2 && Ty.eqb e1 e2
          && eqbOptionP (Expr.eqbF f) c1 c2
    | .chanSend c1 v1 e1, .chanSend c2 v2 e2 =>
        Expr.eqbF f c1 c2 && Expr.eqbF f v1 v2 && Ty.eqb e1 e2
    | .chanRecv t1 c1 e1, .chanRecv t2 c2 e2 =>
        eqbArrayP (Assignee.eqbF f) t1 t2 && Expr.eqbF f c1 c2 && Ty.eqb e1 e2
    | .closeChan c1, .closeChan c2 => Expr.eqbF f c1 c2
    | .selectStmt cl1 d1, .selectStmt cl2 d2 =>
        eqbArrayP (eqbProdP (SelectClauseHead.eqbF f) (Stmt.eqbF f)) cl1 cl2
          && eqbOptionP (Stmt.eqbF f) d1 d2
    | .goStmt c1 a1, .goStmt c2 a2 =>
        Expr.eqbF f c1 c2 && eqbArrayP (Expr.eqbF f) a1 a2
    | .unsupported x, .unsupported y => x == y
    | .syncStmt o1 a1 t1, .syncStmt o2 a2 t2 =>
        o1 == o2 && eqbArrayP (Expr.eqbF f) a1 a2
          && eqbArrayP (Assignee.eqbF f) t1 t2
    | .atomicStmt o1 k1 a1 t1, .atomicStmt o2 k2 a2 t2 =>
        o1 == o2 && k1 == k2 && eqbArrayP (Expr.eqbF f) a1 a2
          && eqbArrayP (Assignee.eqbF f) t1 t2
    | .print n1 a1, .print n2 a2 => n1 == n2 && eqbArrayP (Expr.eqbF f) a1 a2
    | _, _ => false

set_option maxHeartbeats 1600000 in
theorem Stmt.eqbF_sound : ∀ f (a b : Stmt), Stmt.eqbF f a b = true → a = b := by
  intro f
  induction f with
  | zero => intro a b h; exact Bool.noConfusion h
  | succ f ih =>
    intro a b h
    cases a <;> cases b <;> (try exact Bool.noConfusion h)
    case seqn.seqn s1 s2 => cases eqbArrayP_sound ih h; rfl
    case block.block d1 s1 d2 s2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eqbArrayP_sound Param.eqb_sound h1
      cases eqbArrayP_sound ih h2; rfl
    case breakable.breakable b1 b2 => cases ih _ _ h; rfl
    case initialization.initialization v1 v2 =>
      cases Param.eqb_sound _ _ (show Param.eqb v1 v2 = true from h); rfl
    case assign.assign l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2; rfl
    case assignMany.assignMany l1 r1 l2 r2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eqbArrayP_sound (Assignee.eqbF_sound f) h1
      cases eqbArrayP_sound (Expr.eqbF_sound f) h2; rfl
    case allocNew.allocNew t1 v1 y1 t2 v2 y2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
      cases Ty.eqb_sound h3; rfl
    case makeSlice.makeSlice t1 e1 l1 c1 t2 e2 l2 c2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Ty.eqb_sound h2
      cases Expr.eqbF_sound _ _ _ h3
      cases eqbOptionP_sound (Expr.eqbF_sound f) h4; rfl
    case makeMap.makeMap t1 k1 v1 i1 t2 k2 v2 i2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Assignee.eqbF_sound _ _ _ h1
      cases Ty.eqb_sound h2; cases Ty.eqb_sound h3
      cases eqbOptionP_sound (Expr.eqbF_sound f) h4; rfl
    case mapAssign.mapAssign b1 i1 v1 k1 w1 b2 i2 v2 k2 w2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases Expr.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
      cases Expr.eqbF_sound _ _ _ h3
      cases Ty.eqb_sound h4; cases Ty.eqb_sound h5; rfl
    case mapDelete.mapDelete b1 i1 k1 b2 i2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Expr.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
      cases Ty.eqb_sound h3; rfl
    case clearMap.clearMap b1 b2 => cases Expr.eqbF_sound _ _ _ h; rfl
    case clearSlice.clearSlice b1 e1 b2 e2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Expr.eqbF_sound _ _ _ h1; cases Ty.eqb_sound h2; rfl
    case sortSlice.sortSlice b1 e1 b2 e2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Expr.eqbF_sound _ _ _ h1; cases Ty.eqb_sound h2; rfl
    case mapLookup.mapLookup t1 o1 b1 i1 k1 v1 t2 o2 b2 i2 k2 v2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Assignee.eqbF_sound _ _ _ h2
      cases Expr.eqbF_sound _ _ _ h3; cases Expr.eqbF_sound _ _ _ h4
      cases Ty.eqb_sound h5; cases Ty.eqb_sound h6; rfl
    case typeAssert.typeAssert t1 o1 e1 y1 t2 o2 e2 y2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Assignee.eqbF_sound _ _ _ h2
      cases Expr.eqbF_sound _ _ _ h3; cases Ty.eqb_sound h4; rfl
    case appendSlice.appendSlice t1 e1 s1 l1 t2 e2 s2 l2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Ty.eqb_sound h2
      cases Expr.eqbF_sound _ _ _ h3; cases Expr.eqbF_sound _ _ _ h4; rfl
    case copySlice.copySlice t1 d1 s1 t2 d2 s2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
      cases Expr.eqbF_sound _ _ _ h3; rfl
    case call.call t1 n1 a1 t2 n2 a2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eqbArrayP_sound (Assignee.eqbF_sound f) h1
      cases FuncId.beq_sound h2
      cases eqbArrayP_sound (Expr.eqbF_sound f) h3; rfl
    case callValue.callValue t1 c1 a1 t2 c2 a2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eqbArrayP_sound (Assignee.eqbF_sound f) h1
      cases Expr.eqbF_sound _ _ _ h2
      cases eqbArrayP_sound (Expr.eqbF_sound f) h3; rfl
    case deferCall.deferCall c1 a1 c2 a2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Expr.eqbF_sound _ _ _ h1
      cases eqbArrayP_sound (Expr.eqbF_sound f) h2; rfl
    case ifThenElse.ifThenElse c1 t1 e1 c2 t2 e2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Expr.eqbF_sound _ _ _ h1; cases ih _ _ h2; cases ih _ _ h3; rfl
    case «while».«while» c1 b1 c2 b2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Expr.eqbF_sound _ _ _ h1; cases ih _ _ h2; rfl
    case mapRange.mapRange k1 v1 m1 kt1 vt1 b1 k2 v2 m2 kt2 vt2 b2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h1
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h2
      cases Expr.eqbF_sound _ _ _ h3
      cases Ty.eqb_sound h4; cases Ty.eqb_sound h5
      cases ih _ _ h6; rfl
    case returnStmt.returnStmt => rfl
    case breakStmt.breakStmt => rfl
    case continueStmt.continueStmt => rfl
    case labeled.labeled l1 b1 l2 b2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eq_of_beq h1; cases ih _ _ h2; rfl
    case breakTo.breakTo l1 l2 =>
      cases eq_of_beq (show (l1 == l2) = true from h); rfl
    case continueTo.continueTo l1 l2 =>
      cases eq_of_beq (show (l1 == l2) = true from h); rfl
    case panicStmt.panicStmt p1 p2 => cases Expr.eqbF_sound _ _ _ h; rfl
    case inertLabel.inertLabel n1 n2 =>
      cases eq_of_beq (show (n1 == n2) = true from h); rfl
    case makeChan.makeChan t1 e1 c1 t2 e2 c2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Assignee.eqbF_sound _ _ _ h1; cases Ty.eqb_sound h2
      cases eqbOptionP_sound (Expr.eqbF_sound f) h3; rfl
    case chanSend.chanSend c1 v1 e1 c2 v2 e2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Expr.eqbF_sound _ _ _ h1; cases Expr.eqbF_sound _ _ _ h2
      cases Ty.eqb_sound h3; rfl
    case chanRecv.chanRecv t1 c1 e1 t2 c2 e2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eqbArrayP_sound (Assignee.eqbF_sound f) h1
      cases Expr.eqbF_sound _ _ _ h2; cases Ty.eqb_sound h3; rfl
    case closeChan.closeChan c1 c2 => cases Expr.eqbF_sound _ _ _ h; rfl
    case selectStmt.selectStmt cl1 d1 cl2 d2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eqbArrayP_sound
        (fun _ _ hh =>
          eqbProdP_sound (SelectClauseHead.eqbF_sound f) ih hh) h1
      cases eqbOptionP_sound ih h2; rfl
    case goStmt.goStmt c1 a1 c2 a2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases Expr.eqbF_sound _ _ _ h1
      cases eqbArrayP_sound (Expr.eqbF_sound f) h2; rfl
    case unsupported.unsupported x y =>
      cases eq_of_beq (show (x == y) = true from h); rfl
    case syncStmt.syncStmt o1 a1 t1 o2 a2 t2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases SyncStmtOp.beq_sound h1
      cases eqbArrayP_sound (Expr.eqbF_sound f) h2
      cases eqbArrayP_sound (Assignee.eqbF_sound f) h3; rfl
    case atomicStmt.atomicStmt o1 k1 a1 t1 o2 k2 a2 t2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases AtomicStmtOp.beq_sound h1
      cases IntKind.beq_sound h2
      cases eqbArrayP_sound (Expr.eqbF_sound f) h3
      cases eqbArrayP_sound (Assignee.eqbF_sound f) h4; rfl
    case print.print n1 a1 n2 a2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eq_of_beq h1
      cases eqbArrayP_sound (Expr.eqbF_sound f) h2; rfl

/-! ## `Func` -/

/-- Fuel-structural `Func` equality: the fuel is spent entirely inside
the body `Stmt`. -/
def Func.eqbF (fuel : Nat) (a b : Func) : Bool :=
  a.id == b.id
    && eqbArrayP Param.eqb a.args b.args
    && eqbArrayP Param.eqb a.results b.results
    && Stmt.eqbF fuel a.body b.body
    && a.variadic == b.variadic
    && a.wrapper == b.wrapper

theorem Func.eqbF_sound :
    ∀ f (a b : Func), Func.eqbF f a b = true → a = b := by
  intro f a b h
  obtain ⟨i1, ar1, re1, bo1, v1, w1⟩ := a
  obtain ⟨i2, ar2, re2, bo2, v2, w2⟩ := b
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
  cases FuncId.beq_sound h1
  cases eqbArrayP_sound Param.eqb_sound h2
  cases eqbArrayP_sound Param.eqb_sound h3
  cases Stmt.eqbF_sound _ _ _ h4
  cases eq_of_beq h5; cases eq_of_beq h6; rfl

end GoLean.GoCore
