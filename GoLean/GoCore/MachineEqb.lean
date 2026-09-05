import GoLean.GoCore.SyntaxEqb
import GoLean.GoCore.EnumDedupCheck

/-!
# Sound structural equality over the MACHINE-STATE tower (POR slice P2)

`StateEqb.lean` builds the value half and `SyntaxEqb.lean` the syntax
half of the sound-`eqb` layer (design note
`docs/2026-08-21_w32-por-design.md` §3); this file is the MACHINE half —
the op tables (`StrictOp`, `StmtOp`, `TargetStep`/`TargetShape`/
`TargetRef`, `RhsOp`, `ChanStOp`, `SyncOp`, `EvClause`, `PanicEntry`),
the continuation/configuration pair (`Cont`, `Config`), the state layer
(`HeapCell`, `ExecState`), the detector state (`RaceState` and its
components) and the pool top (`MultiConfig`, `DedupNode`).

Same contract, same mould (`GoValue.eqbFuel`): fuel-structural `eqb`s
with ONE-DIRECTIONAL soundness,

    eqb a b = true → a = b

and completeness deliberately NOT claimed. Fuel exhaustion makes an
`eqb` answer `false`, which makes every consumer REFUSE — fail closed,
never unsound.

Every constructor of every covered type has an explicit diagonal arm;
the only catch-alls are the terminal `| _, _ => false` of each match.
The `Race` layer is FLAT (no nested inductive), so `deriving
DecidableEq` works there and the comparison is `decide (a = b)` with
`of_decide_eq_true` as its soundness — no hand-rolled `eqb` needed.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-! ## Conjunction splitters (continuing `SyntaxEqb`'s `andSplit2..6`)

`Cont`'s widest frames carry up to ELEVEN fields (`tgtOpK`), so the
splitter family runs out to 11. Source `&&` is LEFT-associated. -/

theorem andSplit7 {A B C D E F G : Bool}
    (h : (A && B && C && D && E && F && G) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true
      ∧ G = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

theorem andSplit8 {A B C D E F G H : Bool}
    (h : (A && B && C && D && E && F && G && H) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true
      ∧ G = true ∧ H = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem andSplit9 {A B C D E F G H I : Bool}
    (h : (A && B && C && D && E && F && G && H && I) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true
      ∧ G = true ∧ H = true ∧ I = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem andSplit10 {A B C D E F G H I J : Bool}
    (h : (A && B && C && D && E && F && G && H && I && J) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true
      ∧ G = true ∧ H = true ∧ I = true ∧ J = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

theorem andSplit11 {A B C D E F G H I J K : Bool}
    (h : (A && B && C && D && E && F && G && H && I && J && K) = true) :
    A = true ∧ B = true ∧ C = true ∧ D = true ∧ E = true ∧ F = true
      ∧ G = true ∧ H = true ∧ I = true ∧ J = true ∧ K = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The fuel every STATE-layer comparison instantiates its fuel-structural
components at. Generous: fuel bounds structural DEPTH, and the deepest
real `Cont`/`Stmt` spines are orders of magnitude shallower. Exhaustion
is fail-closed (`false` ⇒ the consumer refuses), never unsound. -/
def stateEqbFuel : Nat := 4096

/-! ## `StrictOp` — the defunctionalized expression-op table (48 ctors) -/

/-- Structural `StrictOp` equality. Not recursive: every field is a
`Ty`/`Option Ty`/flat scalar, so no fuel is threaded. -/
def StrictOp.eqb : StrictOp → StrictOp → Bool
  | .add, .add => true
  | .sub, .sub => true
  | .mul, .mul => true
  | .div, .div => true
  | .mod, .mod => true
  | .shiftLeft, .shiftLeft => true
  | .shiftRight, .shiftRight => true
  | .bitAnd, .bitAnd => true
  | .bitOr, .bitOr => true
  | .bitXor, .bitXor => true
  | .bitClear, .bitClear => true
  | .bitNeg, .bitNeg => true
  | .not, .not => true
  | .neg, .neg => true
  | .floatLit n1 d1 k1, .floatLit n2 d2 k2 => n1 == n2 && d1 == d2 && k1 == k2
  | .eqCmp t1, .eqCmp t2 => Ty.eqb t1 t2
  | .neqCmp t1, .neqCmp t2 => Ty.eqb t1 t2
  | .atMostCmp, .atMostCmp => true
  | .atLeastCmp, .atLeastCmp => true
  | .lessCmp, .lessCmp => true
  | .greaterCmp, .greaterCmp => true
  | .convert t1, .convert t2 => Ty.eqb t1 t2
  | .bytesFromString, .bytesFromString => true
  | .stringFromByteSlice, .stringFromByteSlice => true
  | .stringFromRune, .stringFromRune => true
  | .deref t1, .deref t2 => Ty.eqb t1 t2
  | .addrOfDeref, .addrOfDeref => true
  | .fieldGet i1 n1, .fieldGet i2 n2 => i1 == i2 && n1 == n2
  | .fieldAddr i1 n1, .fieldAddr i2 n2 => i1 == i2 && n1 == n2
  | .structLit t1, .structLit t2 => Ty.eqb t1 t2
  | .arrayLit l1 e1 k1, .arrayLit l2 e2 k2 =>
      l1 == l2 && Ty.eqb e1 e2 && eqbListP (· == ·) k1 k2
  | .toInterface t1 d1, .toInterface t2 d2 => Ty.eqb t1 t2 && Ty.eqb d1 d2
  | .typeAssert t1 s1, .typeAssert t2 s2 =>
      Ty.eqb t1 t2 && eqbOptionP Ty.eqb s1 s2
  | .indexGet, .indexGet => true
  | .indexAddr, .indexAddr => true
  | .mapGet k1 v1, .mapGet k2 v2 => Ty.eqb k1 k2 && Ty.eqb v1 v2
  | .sliceExpr m1, .sliceExpr m2 => m1 == m2
  | .lengthOf t1, .lengthOf t2 => eqbOptionP Ty.eqb t1 t2
  | .capacityOf t1, .capacityOf t2 => eqbOptionP Ty.eqb t1 t2
  | .defaultValueOf t1, .defaultValueOf t2 => Ty.eqb t1 t2
  | .nilLit t1, .nilLit t2 => eqbOptionP Ty.eqb t1 t2
  | .funcValOf f1, .funcValOf f2 => f1 == f2
  | .minOf, .minOf => true
  | .maxOf, .maxOf => true
  | .runeAt, .runeAt => true
  | .runeSizeAt, .runeSizeAt => true
  | .runesFromString, .runesFromString => true
  | .stringFromRuneSlice, .stringFromRuneSlice => true
  | .floatBits o1, .floatBits o2 => o1 == o2
  | _, _ => false

set_option maxHeartbeats 1600000 in
theorem StrictOp.eqb_sound :
    ∀ (a b : StrictOp), StrictOp.eqb a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;>
    (try (first | rfl | exact Bool.noConfusion h))
  case floatLit.floatLit n1 d1 k1 n2 d2 k2 =>
    obtain ⟨h1, h2, h3⟩ := andSplit3 h
    cases eq_of_beq h1; cases eq_of_beq h2; cases FloatKind.beq_sound h3; rfl
  case eqCmp.eqCmp t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case neqCmp.neqCmp t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case convert.convert t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case deref.deref t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case fieldGet.fieldGet i1 n1 i2 n2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases eq_of_beq h1; cases eq_of_beq h2; rfl
  case fieldAddr.fieldAddr i1 n1 i2 n2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases eq_of_beq h1; cases eq_of_beq h2; rfl
  case structLit.structLit t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case floatBits.floatBits o1 o2 =>
    cases FloatBitsOp.beq_sound (show (o1 == o2) = true from h); rfl
  case arrayLit.arrayLit l1 e1 k1 l2 e2 k2 =>
    obtain ⟨h1, h2, h3⟩ := andSplit3 h
    cases eq_of_beq h1; cases Ty.eqb_sound h2
    cases eqbListP_sound (fun _ _ hh => eq_of_beq hh) h3; rfl
  case toInterface.toInterface t1 d1 t2 d2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases Ty.eqb_sound h2; rfl
  case typeAssert.typeAssert t1 s1 t2 s2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1
    cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h2; rfl
  case mapGet.mapGet k1 v1 k2 v2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases Ty.eqb_sound h2; rfl
  case sliceExpr.sliceExpr m1 m2 =>
    cases eq_of_beq (show (m1 == m2) = true from h); rfl
  case lengthOf.lengthOf t1 t2 =>
    cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h; rfl
  case capacityOf.capacityOf t1 t2 =>
    cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h; rfl
  case defaultValueOf.defaultValueOf t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl
  case nilLit.nilLit t1 t2 =>
    cases eqbOptionP_sound (fun _ _ hh => Ty.eqb_sound hh) h; rfl
  case funcValOf.funcValOf f1 f2 =>
    cases FuncId.beq_sound (show (f1 == f2) = true from h); rfl

/-! ## `StmtOp` — the wide-statement op table (11 ctors) -/

def StmtOp.eqb : StmtOp → StmtOp → Bool
  | .allocNew t1, .allocNew t2 => Ty.eqb t1 t2
  | .makeSlice e1 c1, .makeSlice e2 c2 => Ty.eqb e1 e2 && c1 == c2
  | .makeMap s1, .makeMap s2 => s1 == s2
  | .makeChan e1 c1, .makeChan e2 c2 => Ty.eqb e1 e2 && c1 == c2
  | .mapAssign k1 v1, .mapAssign k2 v2 => Ty.eqb k1 k2 && Ty.eqb v1 v2
  | .appendSlice e1, .appendSlice e2 => Ty.eqb e1 e2
  | .copySlice, .copySlice => true
  | .mapDelete k1, .mapDelete k2 => Ty.eqb k1 k2
  | .clearMap, .clearMap => true
  | .clearSlice e1, .clearSlice e2 => Ty.eqb e1 e2
  | .sortSlice e1, .sortSlice e2 => Ty.eqb e1 e2
  | .print n1, .print n2 => n1 == n2
  | _, _ => false

theorem StmtOp.eqb_sound : ∀ (a b : StmtOp), StmtOp.eqb a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> (try (first | rfl | exact Bool.noConfusion h))
  case allocNew.allocNew t1 t2 =>
    cases Ty.eqb_sound h; rfl
  case makeSlice.makeSlice e1 c1 e2 c2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases eq_of_beq h2; rfl
  case makeMap.makeMap s1 s2 =>
    cases eq_of_beq (show (s1 == s2) = true from h); rfl
  case makeChan.makeChan e1 c1 e2 c2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases eq_of_beq h2; rfl
  case mapAssign.mapAssign k1 v1 k2 v2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases Ty.eqb_sound h2; rfl
  case appendSlice.appendSlice e1 e2 =>
    cases Ty.eqb_sound (show Ty.eqb e1 e2 = true from h); rfl
  case mapDelete.mapDelete k1 k2 =>
    cases Ty.eqb_sound (show Ty.eqb k1 k2 = true from h); rfl
  case clearSlice.clearSlice e1 e2 =>
    cases Ty.eqb_sound (show Ty.eqb e1 e2 = true from h); rfl
  case sortSlice.sortSlice e1 e2 =>
    cases Ty.eqb_sound (show Ty.eqb e1 e2 = true from h); rfl
  case print.print n1 n2 =>
    cases eq_of_beq (show (n1 == n2) = true from h); rfl

/-! ## Assignment targets -/

/-- `TargetStep` is flat (a `TypeId` and a `String`), so its DERIVED
`BEq` is already the structural comparison; only soundness is owed. -/
theorem TargetStep.beq_sound {a b : TargetStep} (h : (a == b) = true) :
    a = b := by
  cases a <;> cases b <;> (try (first | rfl | exact Bool.noConfusion h))
  case field.field i1 n1 i2 n2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases eq_of_beq h1; cases eq_of_beq h2; rfl

def TargetShape.eqb : TargetShape → TargetShape → Bool
  | .chain s1, .chain s2 => eqbListP (· == ·) s1 s2
  | .mapElem k1 v1, .mapElem k2 v2 => Ty.eqb k1 k2 && Ty.eqb v1 v2
  | _, _ => false

theorem TargetShape.eqb_sound :
    ∀ (a b : TargetShape), TargetShape.eqb a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case chain.chain s1 s2 =>
    cases eqbListP_sound (fun _ _ hh => TargetStep.beq_sound hh) h; rfl
  case mapElem.mapElem k1 v1 k2 v2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases Ty.eqb_sound h2; rfl

def TargetRef.eqb : TargetRef → TargetRef → Bool
  | .chain a1 i1 s1, .chain a2 i2 s2 =>
      GoValue.eqb a1 a2 && eqbListP GoValue.eqb i1 i2
        && eqbListP (· == ·) s1 s2
  | .mapElem b1 k1 kt1 vt1, .mapElem b2 k2 kt2 vt2 =>
      GoValue.eqb b1 b2 && GoValue.eqb k1 k2 && Ty.eqb kt1 kt2
        && Ty.eqb vt1 vt2
  | _, _ => false

theorem TargetRef.eqb_sound :
    ∀ (a b : TargetRef), TargetRef.eqb a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case chain.chain a1 i1 s1 a2 i2 s2 =>
    obtain ⟨h1, h2, h3⟩ := andSplit3 h
    cases GoValue.eqb_sound h1
    cases eqbListP_sound (fun _ _ hh => GoValue.eqb_sound hh) h2
    cases eqbListP_sound (fun _ _ hh => TargetStep.beq_sound hh) h3; rfl
  case mapElem.mapElem b1 k1 kt1 vt1 b2 k2 kt2 vt2 =>
    obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
    cases GoValue.eqb_sound h1; cases GoValue.eqb_sound h2
    cases Ty.eqb_sound h3; cases Ty.eqb_sound h4; rfl

/-! ## `RhsOp` -/

def RhsOp.eqb : RhsOp → RhsOp → Bool
  | .vals, .vals => true
  | .mapLookup k1 v1, .mapLookup k2 v2 => Ty.eqb k1 k2 && Ty.eqb v1 v2
  | .typeAssert t1, .typeAssert t2 => Ty.eqb t1 t2
  | _, _ => false

theorem RhsOp.eqb_sound : ∀ (a b : RhsOp), RhsOp.eqb a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> (try (first | rfl | exact Bool.noConfusion h))
  case mapLookup.mapLookup k1 v1 k2 v2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases Ty.eqb_sound h1; cases Ty.eqb_sound h2; rfl
  case typeAssert.typeAssert t1 t2 =>
    cases Ty.eqb_sound (show Ty.eqb t1 t2 = true from h); rfl

/-! ## `ChanStOp` and `SyncOp` (carry `Assignee` payloads ⇒ fuel) -/

def ChanStOp.eqbF (f : Nat) : ChanStOp → ChanStOp → Bool
  | .send e1, .send e2 => Ty.eqb e1 e2
  | .recv t1 e1, .recv t2 e2 =>
      eqbListP (Assignee.eqbF f) t1 t2 && Ty.eqb e1 e2
  | .close, .close => true
  | _, _ => false

theorem ChanStOp.eqbF_sound :
    ∀ f (a b : ChanStOp), ChanStOp.eqbF f a b = true → a = b := by
  intro f a b h
  cases a <;> cases b <;> (try (first | rfl | exact Bool.noConfusion h))
  case send.send e1 e2 =>
    cases Ty.eqb_sound (show Ty.eqb e1 e2 = true from h); rfl
  case recv.recv t1 e1 t2 e2 =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases eqbListP_sound (Assignee.eqbF_sound f) h1
    cases Ty.eqb_sound h2; rfl

def SyncOp.eqbF (f : Nat) : SyncOp → SyncOp → Bool
  | .lock, .lock => true
  | .unlock, .unlock => true
  | .rlock, .rlock => true
  | .runlock, .runlock => true
  | .wlock, .wlock => true
  | .wunlock, .wunlock => true
  | .wgAdd, .wgAdd => true
  | .wgWait, .wgWait => true
  | .onceBegin t1, .onceBegin t2 => eqbListP (Assignee.eqbF f) t1 t2
  | .onceComplete, .onceComplete => true
  | .tryLock t1, .tryLock t2 => eqbListP (Assignee.eqbF f) t1 t2
  | .tryRLock t1, .tryRLock t2 => eqbListP (Assignee.eqbF f) t1 t2
  | .tryWLock t1, .tryWLock t2 => eqbListP (Assignee.eqbF f) t1 t2
  | _, _ => false

theorem SyncOp.eqbF_sound :
    ∀ f (a b : SyncOp), SyncOp.eqbF f a b = true → a = b := by
  intro f a b h
  cases a <;> cases b <;> (try (first | rfl | exact Bool.noConfusion h))
  case onceBegin.onceBegin t1 t2 =>
    cases eqbListP_sound (Assignee.eqbF_sound f) h; rfl
  case tryLock.tryLock t1 t2 =>
    cases eqbListP_sound (Assignee.eqbF_sound f) h; rfl
  case tryRLock.tryRLock t1 t2 =>
    cases eqbListP_sound (Assignee.eqbF_sound f) h; rfl
  case tryWLock.tryWLock t1 t2 =>
    cases eqbListP_sound (Assignee.eqbF_sound f) h; rfl

/-- `AtomicOp` (atomics arc wave 1): head and kind are field-free enums
(`AtomicStmtOp.beq_sound`, `IntKind.beq_sound`); the result target
list carries `Assignee` payloads ⇒ fuel. -/
def AtomicOp.eqbF (f : Nat) (a b : AtomicOp) : Bool :=
  a.head == b.head && a.kind == b.kind && eqbListP (Assignee.eqbF f) a.targets b.targets

theorem AtomicOp.eqbF_sound :
    ∀ f (a b : AtomicOp), AtomicOp.eqbF f a b = true → a = b := by
  intro f a b h
  obtain ⟨h1, h2, h3⟩ := andSplit3 h
  cases a; cases b
  simp only at h1 h2 h3
  cases AtomicStmtOp.beq_sound h1
  cases IntKind.beq_sound h2
  cases eqbListP_sound (Assignee.eqbF_sound f) h3; rfl

/-! ## `EvClause` and `PanicEntry` -/

def EvClause.eqbF (f : Nat) : EvClause → EvClause → Bool
  | .sendEv c1 v1 e1 b1, .sendEv c2 v2 e2 b2 =>
      GoValue.eqb c1 c2 && GoValue.eqb v1 v2 && Ty.eqb e1 e2
        && Stmt.eqbF f b1 b2
  | .recvEv c1 t1 e1 b1, .recvEv c2 t2 e2 b2 =>
      GoValue.eqb c1 c2 && eqbListP (Assignee.eqbF f) t1 t2 && Ty.eqb e1 e2
        && Stmt.eqbF f b1 b2
  | _, _ => false

theorem EvClause.eqbF_sound :
    ∀ f (a b : EvClause), EvClause.eqbF f a b = true → a = b := by
  intro f a b h
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case sendEv.sendEv c1 v1 e1 b1 c2 v2 e2 b2 =>
    obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
    cases GoValue.eqb_sound h1; cases GoValue.eqb_sound h2
    cases Ty.eqb_sound h3; cases Stmt.eqbF_sound _ _ _ h4; rfl
  case recvEv.recvEv c1 t1 e1 b1 c2 t2 e2 b2 =>
    obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
    cases GoValue.eqb_sound h1
    cases eqbListP_sound (Assignee.eqbF_sound f) h2
    cases Ty.eqb_sound h3; cases Stmt.eqbF_sound _ _ _ h4; rfl

def PanicEntry.eqb (a b : PanicEntry) : Bool :=
  GoValue.eqb a.value b.value && a.recovered == b.recovered

theorem PanicEntry.eqb_sound (a b : PanicEntry) (h : PanicEntry.eqb a b = true) :
    a = b := by
  obtain ⟨v1, r1⟩ := a
  obtain ⟨v2, r2⟩ := b
  obtain ⟨h1, h2⟩ := andSplit2 h
  cases GoValue.eqb_sound h1; cases eq_of_beq h2; rfl

/-! ## `Cont` — the continuation tower (30 constructors) -/

/-- Fuel-structural `Cont` equality: self-recursive on the fuel, with
`Stmt`/`Expr`/`Assignee`/`SelectClauseHead` and the `Assignee`-carrying
op heads compared at the same decremented fuel. `LocalEnv` (=
`List (List (String × Loc))`) is all-flat with a componentwise-lawful
`BEq`, so it uses `==`. Fuel 0 answers `false`. -/
def Cont.eqbF : Nat → Cont → Cont → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match a, b with
    | .stop, .stop => true
    | .seq r1 e1 k1, .seq r2 e2 k2 =>
        eqbListP (Stmt.eqbF f) r1 r2 && e1 == e2 && Cont.eqbF f k1 k2
    | .loop c1 b1 e1 k1, .loop c2 b2 e2 k2 =>
        Expr.eqbF f c1 c2 && Stmt.eqbF f b1 b2 && e1 == e2
          && Cont.eqbF f k1 k2
    | .frame t1 te1 r1 d1 k1 w1, .frame t2 te2 r2 d2 k2 w2 =>
        eqbListP (eqbProdP TargetShape.eqb (eqbListP (Expr.eqbF f))) t1 t2
          && te1 == te2
          && eqbListP (· == ·) r1 r2
          && eqbListP (eqbProdP GoValue.eqb (eqbListP GoValue.eqb)) d1 d2
          && Cont.eqbF f k1 k2
          && w1 == w2
    | .deferCalleeK a1 e1 k1, .deferCalleeK a2 e2 k2 =>
        eqbListP (Expr.eqbF f) a1 a2 && e1 == e2 && Cont.eqbF f k1 k2
    | .deferArgsK c1 v1 p1 e1 k1, .deferArgsK c2 v2 p2 e2 k2 =>
        GoValue.eqb c1 c2 && eqbListP GoValue.eqb v1 v2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .breakableK k1, .breakableK k2 => Cont.eqbF f k1 k2
    | .labelK l1 k1, .labelK l2 k2 => l1 == l2 && Cont.eqbF f k1 k2
    | .callValCalleeK t1 a1 e1 k1, .callValCalleeK t2 a2 e2 k2 =>
        eqbListP (eqbProdP TargetShape.eqb (eqbListP (Expr.eqbF f))) t1 t2
          && eqbListP (Expr.eqbF f) a1 a2 && e1 == e2 && Cont.eqbF f k1 k2
    | .callValArgsK c1 t1 v1 p1 e1 k1, .callValArgsK c2 t2 v2 p2 e2 k2 =>
        GoValue.eqb c1 c2
          && eqbListP (eqbProdP TargetShape.eqb (eqbListP (Expr.eqbF f))) t1 t2
          && eqbListP GoValue.eqb v1 v2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .strictK o1 d1 p1 e1 k1, .strictK o2 d2 p2 e2 k2 =>
        StrictOp.eqb o1 o2 && eqbListP GoValue.eqb d1 d2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .andK r1 e1 k1, .andK r2 e2 k2 =>
        Expr.eqbF f r1 r2 && e1 == e2 && Cont.eqbF f k1 k2
    | .orK r1 e1 k1, .orK r2 e2 k2 =>
        Expr.eqbF f r1 r2 && e1 == e2 && Cont.eqbF f k1 k2
    | .boolK k1, .boolK k2 => Cont.eqbF f k1 k2
    | .ifK t1 el1 e1 k1, .ifK t2 el2 e2 k2 =>
        Stmt.eqbF f t1 t2 && Stmt.eqbF f el1 el2 && e1 == e2
          && Cont.eqbF f k1 k2
    | .whileK c1 b1 e1 k1, .whileK c2 b2 e2 k2 =>
        Expr.eqbF f c1 c2 && Stmt.eqbF f b1 b2 && e1 == e2
          && Cont.eqbF f k1 k2
    | .callArgsK i1 t1 v1 p1 e1 k1, .callArgsK i2 t2 v2 p2 e2 k2 =>
        i1 == i2
          && eqbListP (eqbProdP TargetShape.eqb (eqbListP (Expr.eqbF f))) t1 t2
          && eqbListP GoValue.eqb v1 v2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .stmtOpK o1 n1 d1 p1 e1 k1, .stmtOpK o2 n2 d2 p2 e2 k2 =>
        StmtOp.eqb o1 o2 && n1 == n2 && eqbListP GoValue.eqb d1 d2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .mapRangeK kv1 vv1 kt1 vt1 b1 e1 k1, .mapRangeK kv2 vv2 kt2 vt2 b2 e2 k2 =>
        eqbOptionP (· == ·) kv1 kv2 && eqbOptionP (· == ·) vv1 vv2
          && Ty.eqb kt1 kt2 && Ty.eqb vt1 vt2 && Stmt.eqbF f b1 b2
          && e1 == e2 && Cont.eqbF f k1 k2
    | .mapIterK kv1 vv1 kt1 vt1 b1 ba1 pr1 st1 e1 k1,
      .mapIterK kv2 vv2 kt2 vt2 b2 ba2 pr2 st2 e2 k2 =>
        eqbOptionP (· == ·) kv1 kv2 && eqbOptionP (· == ·) vv1 vv2
          && Ty.eqb kt1 kt2 && Ty.eqb vt1 vt2 && Stmt.eqbF f b1 b2
          && eqbOptionP (· == ·) ba1 ba2
          && eqbArrayP (· == ·) pr1 pr2
          && eqbArrayP (· == ·) st1 st2
          && e1 == e2 && Cont.eqbF f k1 k2
    | .panicArgK k1, .panicArgK k2 => Cont.eqbF f k1 k2
    | .panicResumeK c1 k1, .panicResumeK c2 k2 =>
        eqbListP PanicEntry.eqb c1 c2 && Cont.eqbF f k1 k2
    | .chanStK o1 d1 p1 e1 k1, .chanStK o2 d2 p2 e2 k2 =>
        ChanStOp.eqbF f o1 o2 && eqbListP GoValue.eqb d1 d2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .selectOpsK c1 df1 d1 p1 e1 k1, .selectOpsK c2 df2 d2 p2 e2 k2 =>
        eqbListP (eqbProdP (SelectClauseHead.eqbF f) (Stmt.eqbF f)) c1 c2
          && eqbOptionP (Stmt.eqbF f) df1 df2
          && eqbListP GoValue.eqb d1 d2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .tgtOpK sh1 op1 p1 rf1 t1 ro1 rh1 v1 b1 e1 k1,
      .tgtOpK sh2 op2 p2 rf2 t2 ro2 rh2 v2 b2 e2 k2 =>
        TargetShape.eqb sh1 sh2 && eqbListP GoValue.eqb op1 op2
          && eqbListP (Expr.eqbF f) p1 p2
          && eqbListP TargetRef.eqb rf1 rf2
          && eqbListP (eqbProdP TargetShape.eqb (eqbListP (Expr.eqbF f))) t1 t2
          && RhsOp.eqb ro1 ro2
          && eqbListP (Expr.eqbF f) rh1 rh2
          && eqbListP GoValue.eqb v1 v2
          && Stmt.eqbF f b1 b2 && e1 == e2 && Cont.eqbF f k1 k2
    | .rhsK ro1 rf1 d1 p1 b1 e1 k1, .rhsK ro2 rf2 d2 p2 b2 e2 k2 =>
        RhsOp.eqb ro1 ro2 && eqbListP TargetRef.eqb rf1 rf2
          && eqbListP GoValue.eqb d1 d2 && eqbListP (Expr.eqbF f) p1 p2
          && Stmt.eqbF f b1 b2 && e1 == e2 && Cont.eqbF f k1 k2
    | .storeK rf1 v1 b1 e1 k1, .storeK rf2 v2 b2 e2 k2 =>
        eqbListP TargetRef.eqb rf1 rf2 && eqbListP GoValue.eqb v1 v2
          && Stmt.eqbF f b1 b2 && e1 == e2 && Cont.eqbF f k1 k2
    | .goCalleeK a1 e1 k1, .goCalleeK a2 e2 k2 =>
        eqbListP (Expr.eqbF f) a1 a2 && e1 == e2 && Cont.eqbF f k1 k2
    | .goArgsK c1 v1 p1 e1 k1, .goArgsK c2 v2 p2 e2 k2 =>
        GoValue.eqb c1 c2 && eqbListP GoValue.eqb v1 v2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .syncStK o1 d1 p1 e1 k1, .syncStK o2 d2 p2 e2 k2 =>
        SyncOp.eqbF f o1 o2 && eqbListP GoValue.eqb d1 d2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | .atomicStK o1 d1 p1 e1 k1, .atomicStK o2 d2 p2 e2 k2 =>
        AtomicOp.eqbF f o1 o2 && eqbListP GoValue.eqb d1 d2
          && eqbListP (Expr.eqbF f) p1 p2 && e1 == e2 && Cont.eqbF f k1 k2
    | _, _ => false

/-- Soundness of the target-plan list comparator, lifted once (it
appears in five `Cont` frames). -/
private theorem targetPlans_sound (f : Nat) :
    ∀ {as bs : List (TargetShape × List Expr)},
      eqbListP (eqbProdP TargetShape.eqb (eqbListP (Expr.eqbF f))) as bs = true →
        as = bs :=
  fun hh =>
    eqbListP_sound
      (fun _ _ k =>
        eqbProdP_sound (fun _ _ k' => TargetShape.eqb_sound _ _ k')
          (fun _ _ k' => eqbListP_sound (Expr.eqbF_sound f) k') k) hh

private theorem goValues_sound :
    ∀ {as bs : List GoValue}, eqbListP GoValue.eqb as bs = true → as = bs :=
  fun hh => eqbListP_sound (fun _ _ k => GoValue.eqb_sound k) hh

private theorem exprs_sound (f : Nat) :
    ∀ {as bs : List Expr}, eqbListP (Expr.eqbF f) as bs = true → as = bs :=
  fun hh => eqbListP_sound (Expr.eqbF_sound f) hh

set_option maxHeartbeats 1600000 in
theorem Cont.eqbF_sound : ∀ f (a b : Cont), Cont.eqbF f a b = true → a = b := by
  intro f
  induction f with
  | zero => intro a b h; exact Bool.noConfusion h
  | succ f ih =>
    intro a b h
    cases a <;> cases b <;> (try exact Bool.noConfusion h)
    case stop.stop => rfl
    case seq.seq r1 e1 k1 r2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eqbListP_sound (Stmt.eqbF_sound f) h1
      cases eq_of_beq h2; cases ih _ _ h3; rfl
    case loop.loop c1 b1 e1 k1 c2 b2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Expr.eqbF_sound _ _ _ h1; cases Stmt.eqbF_sound _ _ _ h2
      cases eq_of_beq h3; cases ih _ _ h4; rfl
    case frame.frame t1 te1 r1 d1 k1 w1 t2 te2 r2 d2 k2 w2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases targetPlans_sound f h1
      cases eq_of_beq h2
      cases eqbListP_sound (fun _ _ hh => eq_of_beq hh) h3
      cases eqbListP_sound
        (fun _ _ hh =>
          eqbProdP_sound (fun _ _ k => GoValue.eqb_sound k)
            (fun _ _ k => goValues_sound k) hh) h4
      cases ih _ _ h5; cases eq_of_beq h6; rfl
    case deferCalleeK.deferCalleeK a1 e1 k1 a2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases exprs_sound f h1; cases eq_of_beq h2; cases ih _ _ h3; rfl
    case deferArgsK.deferArgsK c1 v1 p1 e1 k1 c2 v2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases GoValue.eqb_sound h1; cases goValues_sound h2
      cases exprs_sound f h3; cases eq_of_beq h4; cases ih _ _ h5; rfl
    case breakableK.breakableK k1 k2 => cases ih _ _ h; rfl
    case labelK.labelK l1 k1 l2 k2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eq_of_beq h1; cases ih _ _ h2; rfl
    case callValCalleeK.callValCalleeK t1 a1 e1 k1 t2 a2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases targetPlans_sound f h1; cases exprs_sound f h2
      cases eq_of_beq h3; cases ih _ _ h4; rfl
    case callValArgsK.callValArgsK c1 t1 v1 p1 e1 k1 c2 t2 v2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases GoValue.eqb_sound h1; cases targetPlans_sound f h2
      cases goValues_sound h3; cases exprs_sound f h4
      cases eq_of_beq h5; cases ih _ _ h6; rfl
    case strictK.strictK o1 d1 p1 e1 k1 o2 d2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases StrictOp.eqb_sound _ _ h1; cases goValues_sound h2
      cases exprs_sound f h3; cases eq_of_beq h4; cases ih _ _ h5; rfl
    case andK.andK r1 e1 k1 r2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Expr.eqbF_sound _ _ _ h1; cases eq_of_beq h2; cases ih _ _ h3; rfl
    case orK.orK r1 e1 k1 r2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Expr.eqbF_sound _ _ _ h1; cases eq_of_beq h2; cases ih _ _ h3; rfl
    case boolK.boolK k1 k2 => cases ih _ _ h; rfl
    case ifK.ifK t1 el1 e1 k1 t2 el2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Stmt.eqbF_sound _ _ _ h1; cases Stmt.eqbF_sound _ _ _ h2
      cases eq_of_beq h3; cases ih _ _ h4; rfl
    case whileK.whileK c1 b1 e1 k1 c2 b2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases Expr.eqbF_sound _ _ _ h1; cases Stmt.eqbF_sound _ _ _ h2
      cases eq_of_beq h3; cases ih _ _ h4; rfl
    case callArgsK.callArgsK i1 t1 v1 p1 e1 k1 i2 t2 v2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases FuncId.beq_sound h1; cases targetPlans_sound f h2
      cases goValues_sound h3; cases exprs_sound f h4
      cases eq_of_beq h5; cases ih _ _ h6; rfl
    case stmtOpK.stmtOpK o1 n1 d1 p1 e1 k1 o2 n2 d2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases StmtOp.eqb_sound _ _ h1; cases eq_of_beq h2
      cases goValues_sound h3; cases exprs_sound f h4
      cases eq_of_beq h5; cases ih _ _ h6; rfl
    case mapRangeK.mapRangeK kv1 vv1 kt1 vt1 b1 e1 k1 kv2 vv2 kt2 vt2 b2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := andSplit7 h
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h1
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h2
      cases Ty.eqb_sound h3; cases Ty.eqb_sound h4
      cases Stmt.eqbF_sound _ _ _ h5; cases eq_of_beq h6; cases ih _ _ h7; rfl
    case mapIterK.mapIterK kv1 vv1 kt1 vt1 b1 ba1 pr1 st1 e1 k1
        kv2 vv2 kt2 vt2 b2 ba2 pr2 st2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := andSplit10 h
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h1
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h2
      cases Ty.eqb_sound h3; cases Ty.eqb_sound h4
      cases Stmt.eqbF_sound _ _ _ h5
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h6
      cases eqbArrayP_sound (fun _ _ hh => eq_of_beq hh) h7
      cases eqbArrayP_sound (fun _ _ hh => eq_of_beq hh) h8
      cases eq_of_beq h9; cases ih _ _ h10; rfl
    case panicArgK.panicArgK k1 k2 => cases ih _ _ h; rfl
    case panicResumeK.panicResumeK c1 k1 c2 k2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eqbListP_sound PanicEntry.eqb_sound h1
      cases ih _ _ h2; rfl
    case chanStK.chanStK o1 d1 p1 e1 k1 o2 d2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases ChanStOp.eqbF_sound _ _ _ h1; cases goValues_sound h2
      cases exprs_sound f h3; cases eq_of_beq h4; cases ih _ _ h5; rfl
    case selectOpsK.selectOpsK c1 df1 d1 p1 e1 k1 c2 df2 d2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := andSplit6 h
      cases eqbListP_sound
        (fun _ _ hh =>
          eqbProdP_sound (SelectClauseHead.eqbF_sound f)
            (Stmt.eqbF_sound f) hh) h1
      cases eqbOptionP_sound (Stmt.eqbF_sound f) h2
      cases goValues_sound h3; cases exprs_sound f h4
      cases eq_of_beq h5; cases ih _ _ h6; rfl
    case tgtOpK.tgtOpK sh1 op1 p1 rf1 t1 ro1 rh1 v1 b1 e1 k1
        sh2 op2 p2 rf2 t2 ro2 rh2 v2 b2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := andSplit11 h
      cases TargetShape.eqb_sound _ _ h1; cases goValues_sound h2
      cases exprs_sound f h3
      cases eqbListP_sound TargetRef.eqb_sound h4
      cases targetPlans_sound f h5
      cases RhsOp.eqb_sound _ _ h6
      cases exprs_sound f h7; cases goValues_sound h8
      cases Stmt.eqbF_sound _ _ _ h9; cases eq_of_beq h10; cases ih _ _ h11; rfl
    case rhsK.rhsK ro1 rf1 d1 p1 b1 e1 k1 ro2 rf2 d2 p2 b2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := andSplit7 h
      cases RhsOp.eqb_sound _ _ h1
      cases eqbListP_sound TargetRef.eqb_sound h2
      cases goValues_sound h3; cases exprs_sound f h4
      cases Stmt.eqbF_sound _ _ _ h5; cases eq_of_beq h6; cases ih _ _ h7; rfl
    case storeK.storeK rf1 v1 b1 e1 k1 rf2 v2 b2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases eqbListP_sound TargetRef.eqb_sound h1
      cases goValues_sound h2; cases Stmt.eqbF_sound _ _ _ h3
      cases eq_of_beq h4; cases ih _ _ h5; rfl
    case goCalleeK.goCalleeK a1 e1 k1 a2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases exprs_sound f h1; cases eq_of_beq h2; cases ih _ _ h3; rfl
    case goArgsK.goArgsK c1 v1 p1 e1 k1 c2 v2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases GoValue.eqb_sound h1; cases goValues_sound h2
      cases exprs_sound f h3; cases eq_of_beq h4; cases ih _ _ h5; rfl
    case syncStK.syncStK o1 d1 p1 e1 k1 o2 d2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases SyncOp.eqbF_sound _ _ _ h1; cases goValues_sound h2
      cases exprs_sound f h3; cases eq_of_beq h4; cases ih _ _ h5; rfl
    case atomicStK.atomicStK o1 d1 p1 e1 k1 o2 d2 p2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases AtomicOp.eqbF_sound _ _ _ h1; cases goValues_sound h2
      cases exprs_sound f h3; cases eq_of_beq h4; cases ih _ _ h5; rfl

/-! ## `Config` — the control configuration (16 constructors)

Self-recursive through `.opDone (sched : ChoiceSite) (inner : Config)`.
`ChoiceSite` derives `DecidableEq` and NO `BEq`, so the comparison is
`decide (· = ·)` with `of_decide_eq_true` as its soundness. -/

def Config.eqbF : Nat → Config → Config → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match a, b with
    | .exec s1 e1 k1, .exec s2 e2 k2 =>
        Stmt.eqbF f s1 s2 && e1 == e2 && Cont.eqbF f k1 k2
    | .evalE x1 e1 k1, .evalE x2 e2 k2 =>
        Expr.eqbF f x1 x2 && e1 == e2 && Cont.eqbF f k1 k2
    | .retV v1 k1, .retV v2 k2 => GoValue.eqb v1 v2 && Cont.eqbF f k1 k2
    | .next k1, .next k2 => Cont.eqbF f k1 k2
    | .signal sg1 k1, .signal sg2 k2 => sg1 == sg2 && Cont.eqbF f k1 k2
    | .panicking c1 k1, .panicking c2 k2 =>
        eqbListP PanicEntry.eqb c1 c2 && Cont.eqbF f k1 k2
    | .panicked m1, .panicked m2 => m1 == m2
    | .blockedSend c1 v1 k1, .blockedSend c2 v2 k2 =>
        eqbOptionP (· == ·) c1 c2 && GoValue.eqb v1 v2 && Cont.eqbF f k1 k2
    | .blockedRecv c1 t1 el1 e1 k1, .blockedRecv c2 t2 el2 e2 k2 =>
        eqbOptionP (· == ·) c1 c2 && eqbListP (Assignee.eqbF f) t1 t2
          && Ty.eqb el1 el2 && e1 == e2 && Cont.eqbF f k1 k2
    | .blockedSelect cl1 e1 k1, .blockedSelect cl2 e2 k2 =>
        eqbListP (EvClause.eqbF f) cl1 cl2 && e1 == e2 && Cont.eqbF f k1 k2
    | .opDone s1 i1, .opDone s2 i2 =>
        decide (s1 = s2) && Config.eqbF f i1 i2
    | .blockedSync o1 l1 e1 k1, .blockedSync o2 l2 e2 k2 =>
        SyncOp.eqbF f o1 o2 && l1 == l2 && e1 == e2 && Cont.eqbF f k1 k2
    | _, _ => false

set_option maxHeartbeats 1600000 in
theorem Config.eqbF_sound :
    ∀ f (a b : Config), Config.eqbF f a b = true → a = b := by
  intro f
  induction f with
  | zero => intro a b h; exact Bool.noConfusion h
  | succ f ih =>
    intro a b h
    cases a <;> cases b <;> (try exact Bool.noConfusion h)
    case exec.exec s1 e1 k1 s2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Stmt.eqbF_sound _ _ _ h1; cases eq_of_beq h2
      cases Cont.eqbF_sound _ _ _ h3; rfl
    case evalE.evalE x1 e1 k1 x2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases Expr.eqbF_sound _ _ _ h1; cases eq_of_beq h2
      cases Cont.eqbF_sound _ _ _ h3; rfl
    case retV.retV v1 k1 v2 k2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases GoValue.eqb_sound h1; cases Cont.eqbF_sound _ _ _ h2; rfl
    case next.next k1 k2 => cases Cont.eqbF_sound _ _ _ h; rfl
    case signal.signal sg1 k1 sg2 k2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eq_of_beq h1; cases Cont.eqbF_sound _ _ _ h2; rfl
    case panicking.panicking c1 k1 c2 k2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases eqbListP_sound PanicEntry.eqb_sound h1
      cases Cont.eqbF_sound _ _ _ h2; rfl
    case panicked.panicked m1 m2 =>
      cases eq_of_beq (show (m1 == m2) = true from h); rfl
    case blockedSend.blockedSend c1 v1 k1 c2 v2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h1
      cases GoValue.eqb_sound h2; cases Cont.eqbF_sound _ _ _ h3; rfl
    case blockedRecv.blockedRecv c1 t1 el1 e1 k1 c2 t2 el2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := andSplit5 h
      cases eqbOptionP_sound (fun _ _ hh => eq_of_beq hh) h1
      cases eqbListP_sound (Assignee.eqbF_sound f) h2
      cases Ty.eqb_sound h3; cases eq_of_beq h4
      cases Cont.eqbF_sound _ _ _ h5; rfl
    case blockedSelect.blockedSelect cl1 e1 k1 cl2 e2 k2 =>
      obtain ⟨h1, h2, h3⟩ := andSplit3 h
      cases eqbListP_sound (EvClause.eqbF_sound f) h1
      cases eq_of_beq h2; cases Cont.eqbF_sound _ _ _ h3; rfl
    case opDone.opDone s1 i1 s2 i2 =>
      obtain ⟨h1, h2⟩ := andSplit2 h
      cases of_decide_eq_true h1; cases ih _ _ h2; rfl
    case blockedSync.blockedSync o1 l1 e1 k1 o2 l2 e2 k2 =>
      obtain ⟨h1, h2, h3, h4⟩ := andSplit4 h
      cases SyncOp.eqbF_sound _ _ _ h1; cases eq_of_beq h2
      cases eq_of_beq h3; cases Cont.eqbF_sound _ _ _ h4; rfl

/-! ## The state layer -/

def HeapCell.eqb : HeapCell → HeapCell → Bool
  | .value t₁ v₁, .value t₂ v₂ => GoValue.eqb v₁ v₂ && Ty.eqb t₁ t₂
  | .mapPayload e₁ n₁, .mapPayload e₂ n₂ =>
      n₁ == n₂ && GoValue.eqbTriplesWith GoValue.eqb e₁.toList e₂.toList
  | .chanPayload b₁ c₁ k₁, .chanPayload b₂ c₂ k₂ =>
      c₁ == c₂ && k₁ == k₂ && eqbArrayP GoValue.eqb b₁ b₂
  | _, _ => false

theorem HeapCell.eqb_sound (a b : HeapCell) (h : HeapCell.eqb a b = true) :
    a = b := by
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case value.value t₁ v₁ t₂ v₂ =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases GoValue.eqb_sound h1; cases Ty.eqb_sound h2; rfl
  case mapPayload.mapPayload e₁ n₁ e₂ n₂ =>
    obtain ⟨h1, h2⟩ := andSplit2 h
    cases eq_of_beq h1
    cases array_toList_inj
      (GoValue.eqbTriplesWith_sound (fun _ _ hh => GoValue.eqb_sound hh) h2); rfl
  case chanPayload.chanPayload b₁ c₁ k₁ b₂ c₂ k₂ =>
    obtain ⟨h1, h2, h3⟩ := andSplit3 h
    cases eq_of_beq h1; cases eq_of_beq h2
    cases eqbArrayP_sound (fun _ _ hh => GoValue.eqb_sound hh) h3; rfl

/-- Structural `ExecState` equality. The conjunction is ordered
CHEAP-MUTABLE-FIRST — `heap`/`nextAddr` are what differs between two
states of one run, while `types`/`functions`/`methods`/`methodSets` are
program context, identical across every node of a single program's state
graph and expensive to walk. `&&` short-circuits, so an unequal heap
costs nothing more. -/
def ExecState.eqb (a b : ExecState) : Bool :=
  eqbArrayP HeapCell.eqb a.heap b.heap
    && eqbListP (eqbProdP (· == ·) TypeDef.eqb) a.types b.types
    && eqbArrayP (Func.eqbF stateEqbFuel) a.functions b.functions
    && eqbArrayP MethodInfo.eqb a.methods b.methods
    && eqbArrayP (· == ·) a.methodSets b.methodSets
    && eqbArrayP (eqbProdP (· == ·) (· == ·)) a.typeDisplays b.typeDisplays

theorem ExecState.eqb_sound (a b : ExecState) (h : ExecState.eqb a b = true) :
    a = b := by
  obtain ⟨ty1, fn1, me1, ms1, td1, hp1⟩ := a
  obtain ⟨ty2, fn2, me2, ms2, td2, hp2⟩ := b
  obtain ⟨h1, h3, h4, h5, h6, h7⟩ := andSplit6 h
  cases eqbArrayP_sound HeapCell.eqb_sound h1
  cases eqbListP_sound
    (fun _ _ hh =>
      eqbProdP_sound (fun _ _ k => eq_of_beq k) TypeDef.eqb_sound hh) h3
  cases eqbArrayP_sound (Func.eqbF_sound stateEqbFuel) h4
  cases eqbArrayP_sound MethodInfo.eqb_sound h5
  cases eqbArrayP_sound (fun _ _ hh => MethodSetRecord.beq_sound hh) h6
  cases eqbArrayP_sound
    (fun _ _ hh =>
      eqbProdP_sound (fun _ _ k => eq_of_beq k) (fun _ _ k => TypeDisplay.beq_sound k) hh) h7
  rfl

/-! ## The detector state

`RaceState` and its components are FLAT (`VClock = Array Nat`, `Loc`
already has `DecidableEq`), so `deriving DecidableEq` succeeds and the
comparison is `decide (· = ·)` — no fuel, no hand-rolled traversal. -/

deriving instance DecidableEq for ShadowCell
deriving instance DecidableEq for ChanClocks
deriving instance DecidableEq for SyncClocks
deriving instance DecidableEq for RaceState

def RaceState.eqb (a b : RaceState) : Bool := decide (a = b)

theorem RaceState.eqb_sound {a b : RaceState} (h : RaceState.eqb a b = true) :
    a = b := of_decide_eq_true h

/-! ## The pool top and the certificate node -/

/-- Structural `MultiConfig` equality, cheap-first: the running-goroutine
index, then the per-goroutine controls, then the shared state. -/
def MultiConfig.eqb (a b : MultiConfig) : Bool :=
  a.cur == b.cur
    && eqbArrayP (Config.eqbF stateEqbFuel) a.threads b.threads
    && ExecState.eqb a.shared b.shared

theorem MultiConfig.eqb_sound (a b : MultiConfig)
    (h : MultiConfig.eqb a b = true) : a = b := by
  obtain ⟨t1, s1, c1⟩ := a
  obtain ⟨t2, s2, c2⟩ := b
  obtain ⟨h1, h2, h3⟩ := andSplit3 h
  cases eq_of_beq h1
  cases eqbArrayP_sound (Config.eqbF_sound stateEqbFuel) h2
  cases ExecState.eqb_sound _ _ h3; rfl

/-- Certificate-node equality: the pool state and the detector state. -/
def dedupNodeEqb (a b : DedupNode) : Bool :=
  MultiConfig.eqb a.m b.m && RaceState.eqb a.r b.r

theorem dedupNodeEqb_sound (a b : DedupNode) (h : dedupNodeEqb a b = true) :
    a = b := by
  obtain ⟨m1, r1⟩ := a
  obtain ⟨m2, r2⟩ := b
  obtain ⟨h1, h2⟩ := andSplit2 h
  cases MultiConfig.eqb_sound _ _ h1
  cases RaceState.eqb_sound h2; rfl

end GoLean.GoCore.Machine
