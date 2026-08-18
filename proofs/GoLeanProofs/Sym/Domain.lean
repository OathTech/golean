import GoLean.GoCore.StepFn

/-!
# The mirror symbolic evaluator — the scalar domain (WP arc slice 4, phase 1)

Design of record: `docs/2026-08-16_symbolic-domain-design.md` (user gate
discharged 2026-08-18 — approved as recommended, OQ1–OQ6 per the
operator's takes). This module is deliverable 1: the deep first-order
term languages `SymInt`/`SymBool`, the valuation `γ`, the closedness
evaluators, the fine-grained scalar-domain interface `ScalarDom`
(design §1.3 option 1b), and its two instances — the CONCRETE domain
`cdom` (payloads are `Int`/`Bool`, inspections always answer) and the
SYMBOLIC domain `symDom` (payloads are terms, inspections answer
exactly on closed terms).

**Outside the TCB by construction.** Everything in `GoLean.Sym` is
proof-land automation infrastructure under Route B: GoCore is
untouched, and no constant from this namespace may enter a designated
headline statement closure — enforced mechanically by the third
refusal class of the statement-TCB walker (`proofs/Audit.lean`), which
refuses the whole `GoLean.Sym` prefix, plus the arc-cadence deletion
test (design §8).

Two recorded mechanization deltas vs the design note's sketch (log:
`docs/wp-arc-log/s4.md` JC-1/JC-2):
- `ScalarDom` carries an `Atom : Type` field (symbolic `Nat`, concrete
  `Empty`) so the opaque-cell constructor lives in the shared value
  grammar while the concrete embedding stays TOTAL;
- the sketched "table accessors" are realized as the Q4 quit sites —
  v1 shared code consults program tables NOWHERE (that is what makes
  emitted windows program-generic); the accessor pair is the recorded
  v2 conditioned-facts lever (OQ6), not a dead v1 field.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore

/-- Deep first-order symbolic integers (design §2.1). The op set is the
consumer-driven v1 minimum (OQ5): what the 24 shipped examples' windows
exercise. No smart constructors, no normalization inside the term
language — terms record the machine's computation history verbatim,
which keeps the commutation lemmas one-step and γ-images syntactically
identical to the hand-written statement shapes (`IntKind.normalize …`).
Growth is one constructor + one γ equation + one commutation leaf per
op. `divC`/`modC` take a CONCRETE divisor (design §1.2: the op
constructs iff every payload its control decisions read is closed —
`t / u` at symbolic `u` is a Q5 quit, never a term). -/
inductive SymInt where
  | lit (n : Int)
  | var (i : Nat)
  | add (a b : SymInt)
  | sub (a b : SymInt)
  | mul (a b : SymInt)
  | divC (a : SymInt) (k : Int)
  | modC (a : SymInt) (k : Int)
  | neg (a : SymInt)
  | norm (kind : IntKind) (a : SymInt)
  deriving DecidableEq, Repr

/-- Deep first-order symbolic booleans (design §2.1): literals,
variables, negation, and the integer comparisons as values. `>`/`≥`
are realized by operand swap at the consuming sites (`valueGreater'`),
matching the machine's own `Int` reading. No `eqB` former in v1
(nothing in the corpus compares symbolic bools with `==`; flags are
branched on — a Q1 window boundary — never compared). -/
inductive SymBool where
  | lit (b : Bool)
  | var (i : Nat)
  | not (a : SymBool)
  | eqI (a b : SymInt)
  | ltI (a b : SymInt)
  | leI (a b : SymInt)
  deriving DecidableEq, Repr

/-- The valuation (design §2.1): scalar symbols to their values, plus
the opaque-cell atoms (`Value.atom i ↦ ρ.vals i` — whole heap cells the
window never inspects, riding through exactly as they ride through
today's `rfl` windows). -/
structure Valuation where
  ints : Nat → Int
  bools : Nat → Bool
  vals : Nat → GoValue

/-- Concretize a symbolic integer at a valuation. Structural; the
`@[simp]` display equations below are the simp-normal form emitted
statements reduce through (design §2.2). The `neg`/`divC`/`modC`
readings (`0 - ·`, `Int.tdiv`, `Int.tmod`) are the machine's own
spellings (`Machine.lean:297`, `applyStrictOp` div/mod arms), so
γ-images are byte-shaped like the hand lemmas. -/
def γI (ρ : Valuation) : SymInt → Int
  | .lit n => n
  | .var i => ρ.ints i
  | .add a b => γI ρ a + γI ρ b
  | .sub a b => γI ρ a - γI ρ b
  | .mul a b => γI ρ a * γI ρ b
  | .divC a k => Int.tdiv (γI ρ a) k
  | .modC a k => Int.tmod (γI ρ a) k
  | .neg a => 0 - γI ρ a
  | .norm kind a => kind.normalize (γI ρ a)

/-- Concretize a symbolic boolean at a valuation. The comparison
readings (`==`, `decide (· < ·)`, `decide (· ≤ ·)`) are exactly what
the machine's `valueEq`/`valueLess`/`valueAtMost` int arms return, so
γ-images are byte-shaped like the hand lemmas (`decide (iv < nv)`). -/
def γB (ρ : Valuation) : SymBool → Bool
  | .lit b => b
  | .var i => ρ.bools i
  | .not a => !(γB ρ a)
  | .eqI a b => γI ρ a == γI ρ b
  | .ltI a b => decide (γI ρ a < γI ρ b)
  | .leI a b => decide (γI ρ a ≤ γI ρ b)

/-! ### Simp-normal display forms (one equation per constructor) -/

@[simp] theorem γI_lit (ρ : Valuation) (n : Int) : γI ρ (.lit n) = n := rfl
@[simp] theorem γI_var (ρ : Valuation) (i : Nat) : γI ρ (.var i) = ρ.ints i := rfl
@[simp] theorem γI_add (ρ : Valuation) (a b : SymInt) :
    γI ρ (.add a b) = γI ρ a + γI ρ b := rfl
@[simp] theorem γI_sub (ρ : Valuation) (a b : SymInt) :
    γI ρ (.sub a b) = γI ρ a - γI ρ b := rfl
@[simp] theorem γI_mul (ρ : Valuation) (a b : SymInt) :
    γI ρ (.mul a b) = γI ρ a * γI ρ b := rfl
@[simp] theorem γI_divC (ρ : Valuation) (a : SymInt) (k : Int) :
    γI ρ (.divC a k) = Int.tdiv (γI ρ a) k := rfl
@[simp] theorem γI_modC (ρ : Valuation) (a : SymInt) (k : Int) :
    γI ρ (.modC a k) = Int.tmod (γI ρ a) k := rfl
@[simp] theorem γI_neg (ρ : Valuation) (a : SymInt) :
    γI ρ (.neg a) = 0 - γI ρ a := rfl
@[simp] theorem γI_norm (ρ : Valuation) (kind : IntKind) (a : SymInt) :
    γI ρ (.norm kind a) = kind.normalize (γI ρ a) := rfl

@[simp] theorem γB_lit (ρ : Valuation) (b : Bool) : γB ρ (.lit b) = b := rfl
@[simp] theorem γB_var (ρ : Valuation) (i : Nat) : γB ρ (.var i) = ρ.bools i := rfl
@[simp] theorem γB_not (ρ : Valuation) (a : SymBool) :
    γB ρ (.not a) = !(γB ρ a) := rfl
@[simp] theorem γB_eqI (ρ : Valuation) (a b : SymInt) :
    γB ρ (.eqI a b) = (γI ρ a == γI ρ b) := rfl
@[simp] theorem γB_ltI (ρ : Valuation) (a b : SymInt) :
    γB ρ (.ltI a b) = decide (γI ρ a < γI ρ b) := rfl
@[simp] theorem γB_leI (ρ : Valuation) (a b : SymInt) :
    γB ρ (.leI a b) = decide (γI ρ a ≤ γI ρ b) := rfl

/-! ### Closedness evaluators (the symbolic instance's inspections)

An inspection first tries to CLOSE the term, so fully-concrete windows
never quit where today's `rfl` succeeds (design §2.1). Structural;
explicit matches (no `Option` do-notation) so the soundness proofs
split mechanically. -/

/-- Evaluate a symbolic integer if it contains no variables. -/
def closedI? : SymInt → Option Int
  | .lit n => some n
  | .var _ => none
  | .add a b =>
      match closedI? a, closedI? b with
      | some x, some y => some (x + y)
      | _, _ => none
  | .sub a b =>
      match closedI? a, closedI? b with
      | some x, some y => some (x - y)
      | _, _ => none
  | .mul a b =>
      match closedI? a, closedI? b with
      | some x, some y => some (x * y)
      | _, _ => none
  | .divC a k =>
      match closedI? a with
      | some x => some (Int.tdiv x k)
      | none => none
  | .modC a k =>
      match closedI? a with
      | some x => some (Int.tmod x k)
      | none => none
  | .neg a =>
      match closedI? a with
      | some x => some (0 - x)
      | none => none
  | .norm kind a =>
      match closedI? a with
      | some x => some (kind.normalize x)
      | none => none

/-- Evaluate a symbolic boolean if it contains no variables. -/
def closedB? : SymBool → Option Bool
  | .lit b => some b
  | .var _ => none
  | .not a =>
      match closedB? a with
      | some x => some (!x)
      | none => none
  | .eqI a b =>
      match closedI? a, closedI? b with
      | some x, some y => some (x == y)
      | _, _ => none
  | .ltI a b =>
      match closedI? a, closedI? b with
      | some x, some y => some (decide (x < y))
      | _, _ => none
  | .leI a b =>
      match closedI? a, closedI? b with
      | some x, some y => some (decide (x ≤ y))
      | _, _ => none

/-- A closed term evaluates to its closure under EVERY valuation — the
γ-leaf every conditional-constructor commutation case rests on. -/
theorem closedI?_sound (ρ : Valuation) :
    ∀ {t : SymInt} {n : Int}, closedI? t = some n → γI ρ t = n := by
  intro t
  induction t with
  | lit m => intro n h; simpa [closedI?] using h
  | var i => intro n h; simp [closedI?] at h
  | add a b iha ihb =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x y hx hy =>
          cases h; simp [iha hx, ihb hy]
      · exact absurd h (by simp)
  | sub a b iha ihb =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x y hx hy => cases h; simp [iha hx, ihb hy]
      · exact absurd h (by simp)
  | mul a b iha ihb =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x y hx hy => cases h; simp [iha hx, ihb hy]
      · exact absurd h (by simp)
  | divC a k iha =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x hx => cases h; simp [iha hx]
      · exact absurd h (by simp)
  | modC a k iha =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x hx => cases h; simp [iha hx]
      · exact absurd h (by simp)
  | neg a iha =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x hx => cases h; simp [iha hx]
      · exact absurd h (by simp)
  | norm kind a iha =>
      intro n h
      simp only [closedI?] at h
      split at h
      · next x hx => cases h; simp [iha hx]
      · exact absurd h (by simp)

@[inherit_doc closedI?_sound]
theorem closedB?_sound (ρ : Valuation) :
    ∀ {t : SymBool} {b : Bool}, closedB? t = some b → γB ρ t = b := by
  intro t
  induction t with
  | lit x => intro b h; simpa [closedB?] using h
  | var i => intro b h; simp [closedB?] at h
  | not a iha =>
      intro b h
      simp only [closedB?] at h
      split at h
      · next x hx => cases h; simp [iha hx]
      · exact absurd h (by simp)
  | eqI a c =>
      intro b h
      simp only [closedB?] at h
      split at h
      · next x y hx hy =>
          cases h; simp [closedI?_sound ρ hx, closedI?_sound ρ hy]
      · exact absurd h (by simp)
  | ltI a c =>
      intro b h
      simp only [closedB?] at h
      split at h
      · next x y hx hy =>
          cases h; simp [closedI?_sound ρ hx, closedI?_sound ρ hy]
      · exact absurd h (by simp)
  | leI a c =>
      intro b h
      simp only [closedB?] at h
      split at h
      · next x y hx hy =>
          cases h; simp [closedI?_sound ρ hx, closedI?_sound ρ hy]
      · exact absurd h (by simp)

/-! ### The scalar-domain interface (design §1.3, option 1b — ruled OQ1) -/

/-- The fine-grained scalar-domain interface: the class abstracts ONLY
the scalar theory; everything above it (the value grammar, the heap,
the mirrored step function) is shared parametric code written once over
`D`. Class-A machine sites (payload-blind term production) call the
total CONSTRUCTORS; class-B sites (payload-consulting control
decisions) call the partial INSPECTIONS and quit on `none` — so the
`toInt?`/`toBool?` call sites in `Mirror.lean` are grep-ably the
complete inspection census (what makes the Q1–Q11 quit catalog a
checkable claim).

A plain structure, not a typeclass: the mirror threads `D` explicitly,
keeping instance resolution out of kernel-reduction paths.

`Atom` is the opaque-cell payload type (JC-2): cells a window never
inspects ride through as atoms. Concrete instance: `Empty` (no opaque
cells exist concretely — the drift embedding is total). Symbolic
instance: `Nat` (the design's `atom (i : Nat)`, γ-mapped through
`Valuation.vals`).

Program-table accessors are deliberately ABSENT in v1 (JC-1): every
table-consult site quits Q4 in the shared code, which is what makes
emitted windows program-generic by construction. -/
structure ScalarDom where
  IntR : Type
  BoolR : Type
  Atom : Type
  litI : Int → IntR
  litB : Bool → BoolR
  add : IntR → IntR → IntR
  sub : IntR → IntR → IntR
  mul : IntR → IntR → IntR
  /-- Division by a CONCRETE divisor (`Int.tdiv` reading); the caller
  guarantees `k ≠ 0` (the zero check is a control decision and happens
  before construction — a symbolic divisor is a Q5 quit). -/
  divC : IntR → Int → IntR
  /-- Modulo by a concrete divisor (`Int.tmod` reading); see `divC`. -/
  modC : IntR → Int → IntR
  /-- Unary minus, the machine's `0 - v` reading. -/
  neg : IntR → IntR
  /-- `IntKind.normalize` lifted to the payload representation. -/
  norm : IntKind → IntR → IntR
  notB : BoolR → BoolR
  /-- Integer `==` as a stored value (`valueEq` int-arm reading). -/
  eqI : IntR → IntR → BoolR
  /-- Integer `<` as a stored value (`decide (· < ·)` reading). -/
  ltI : IntR → IntR → BoolR
  /-- Integer `≤` as a stored value (`decide (· ≤ ·)` reading). -/
  leI : IntR → IntR → BoolR
  /-- Partial inspection: the payload as a concrete `Int`, if decidable.
  `none` = the consuming machine site QUITS (never approximates). -/
  toInt? : IntR → Option Int
  /-- Partial inspection: the payload as a concrete `Bool`, if
  decidable. `none` = the consuming machine site QUITS. -/
  toBool? : BoolR → Option Bool

/-- THE SYMBOLIC INSTANCE — the evaluator's domain: payloads are deep
terms, constructors are term formers, inspections are the closedness
evaluators (so fully-concrete windows never quit where `rfl`
succeeds). -/
@[reducible] def symDom : ScalarDom where
  IntR := SymInt
  BoolR := SymBool
  Atom := Nat
  litI := .lit
  litB := .lit
  add := .add
  sub := .sub
  mul := .mul
  divC := .divC
  modC := .modC
  neg := .neg
  norm := .norm
  notB := .not
  eqI := .eqI
  ltI := .ltI
  leI := .leI
  toInt? := closedI?
  toBool? := closedB?

/-- THE CONCRETE INSTANCE — the drift theorem's domain: payloads are
the machine's own `Int`/`Bool`, every constructor is the machine's own
operation (spelled exactly as the corresponding `stepFn` site spells
it, so the drift arms are `rfl`-shaped), every inspection answers, and
no atoms exist (`Empty`). -/
@[reducible] def cdom : ScalarDom where
  IntR := Int
  BoolR := Bool
  Atom := Empty
  litI := id
  litB := id
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  divC := Int.tdiv
  modC := Int.tmod
  neg := (0 - ·)
  norm := IntKind.normalize
  notB := (!·)
  eqI := fun a b => a == b
  ltI := fun a b => decide (a < b)
  leI := fun a b => decide (a ≤ b)
  toInt? := some
  toBool? := some

/-! Definitional-collapse pins for the concrete instance: the drift
walk's arms rely on these being `rfl`; a reshaped instance fails HERE,
in the defining module. -/
example (a b : Int) : cdom.add a b = a + b := rfl
example (a : Int) (k : IntKind) : cdom.norm k a = k.normalize a := rfl
example (a b : Int) : cdom.ltI a b = decide (a < b) := rfl
example (a : Int) : cdom.toInt? a = some a := rfl
example (b : Bool) : cdom.toBool? b = some b := rfl
example (n : Int) : cdom.litI n = n := rfl

/-! And the symbolic instance's inspection contract: closed terms
answer, open terms refuse. -/
example : symDom.toInt? (.norm .int64 (.add (.lit 2) (.lit 3))) = some 5 := by
  decide
example : symDom.toInt? (.add (.var 0) (.lit 1)) = none := rfl
example : symDom.toBool? (.ltI (.lit 1) (.lit 2)) = some true := by decide
example : symDom.toBool? (.ltI (.var 2) (.var 0)) = none := rfl

end GoLean.Sym
