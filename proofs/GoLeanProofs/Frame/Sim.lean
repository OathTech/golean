import GoLeanProofs.Frame.Rename
import GoLean.GoCore.MachineSound

/-!
# The executable frame theorem, module 2: the simulation relation
(design of record `docs/2026-08-13_executable-frame-theorem.md` §1)

`FrameSim ρ na₀ na fr σ σF` is the state half of the design's
`SimState`: the framed state `σF` runs beside the canonical `σ` with

* equal static tables (types/functions/methods/methodSets — programs
  contain no renamable identity; function BODIES are additionally
  `ρ`-invariant, discharged at the seed from `locSup` bounds);
* the allocator tracked through `ρ` (`nextAddr` correspondence, with
  the canonical allocator at or above `na₀` so allocation commutes
  with the shift);
* the heap characterized POINTWISE at every `ρ`-image location
  (renamed canonical cell where the canonical heap answers; the frame's
  own cell — inert — where it does not), with every frame cell
  preserved verbatim and no frame cell sitting anywhere in `ρ`'s image
  on base addresses (`fr_avoid` — a CONSTANT clause, established once
  at the seed from `MachineWf` of the framed seed + input-disjointness,
  which is what makes canonical writes provably miss the frame).

`ExSim R` is the result-transfer relation the whole helper-commutation
layer is stated in: canonical `.ok` transfers to framed `.ok` (payloads
`R`-related), canonical panics transfer with the SAME message (panic
messages on success-reachable paths embed no addresses — checked
arm-by-arm downstream), and any other canonical error transfers
vacuously (the simulation is success-steps-only by design §3.5).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## `ExSim`: the Except-level transfer relation -/

def ExSim {α β : Type} (R : α → β → Prop) :
    Except GoError α → Except GoError β → Prop
  | .ok a, .ok b => R a b
  | .ok _, .error _ => False
  | .error (.panic m), y => y = .error (.panic m)
  | .error _, _ => True

namespace ExSim

variable {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}

theorem ok {a : α} {b : β} (h : R a b) : ExSim R (.ok a) (.ok b) := h

theorem pure' {a : α} {b : β} (h : R a b) :
    ExSim R (pure a) (pure b) := h

theorem panic {m : String} : ExSim R (.error (.panic m)) (.error (.panic m)) :=
  rfl

/-- A canonical error that is not a panic transfers vacuously. -/
theorem skip {e : GoError} (he : ∀ m, e ≠ .panic m) {y : Except GoError β} :
    ExSim R (.error e) y := by
  cases e with
  | panic m => exact absurd rfl (he m)
  | _ => trivial

theorem ok_inv {x : Except GoError α} {y : Except GoError β} {a : α}
    (h : ExSim R x y) (hx : x = .ok a) : ∃ b, y = .ok b ∧ R a b := by
  subst hx
  cases y with
  | ok b => exact ⟨b, rfl, h⟩
  | error e => exact absurd h (by simp [ExSim])

theorem panic_inv {x : Except GoError α} {y : Except GoError β} {m : String}
    (h : ExSim R x y) (hx : x = .error (.panic m)) : y = .error (.panic m) := by
  subst hx; exact h

/-- Monotonicity in the payload relation. -/
theorem weaken {R S : α → β → Prop} {x : Except GoError α}
    {y : Except GoError β}
    (h : ExSim R x y) (himp : ∀ a b, R a b → S a b) : ExSim S x y := by
  cases x with
  | ok a =>
      cases y with
      | ok b => exact himp _ _ h
      | error e => exact absurd h (by simp [ExSim])
  | error e =>
      cases e <;> first | exact h | trivial

/-- The bind rule: the whole monadic commutation layer composes through
this. -/
theorem bind {x : Except GoError α} {y : Except GoError β}
    {f : α → Except GoError γ} {g : β → Except GoError δ}
    (hxy : ExSim R x y) (hfg : ∀ a b, R a b → ExSim S (f a) (g b)) :
    ExSim S (x >>= f) (y >>= g) := by
  cases x with
  | ok a =>
      cases y with
      | ok b => simpa [Bind.bind, Except.bind] using hfg a b hxy
      | error e => exact absurd hxy (by simp [ExSim])
  | error e =>
      cases e with
      | panic m =>
          have hy : y = .error (.panic m) := hxy
          subst hy
          exact rfl
      | _ => trivial

/-- Reflexivity at equal computations (loc-free operations). -/
theorem refl (x : Except GoError α) : ExSim Eq x x := by
  cases x with
  | ok a => exact rfl
  | error e => cases e <;> first | exact rfl | trivial

/-- Same-condition `if` split. -/
theorem ite_congr {c : Prop} [Decidable c] {x₁ x₂ : Except GoError α}
    {y₁ y₂ : Except GoError β}
    (ht : c → ExSim R x₁ y₁) (he : ¬c → ExSim R x₂ y₂) :
    ExSim R (if c then x₁ else x₂) (if c then y₁ else y₂) := by
  split
  · exact ht ‹_›
  · exact he ‹_›

end ExSim

/-! ## Heap pointwise algebra -/

theorem Heap.lookup_set_self {h : Heap} {k : Loc} {c : HeapCell} :
    Heap.lookup (Heap.set h k c) k = some c := by
  induction h with
  | nil => simp [Heap.set, Heap.lookup]
  | cons p rest ih =>
      obtain ⟨loc, old⟩ := p
      simp only [Heap.set]
      cases hb : (loc == k) with
      | true => simp [Heap.lookup, eq_of_beq hb]
      | false => simp [Heap.lookup, hb, ih]

theorem Heap.lookup_set (h : Heap) (k l : Loc) (c : HeapCell) :
    Heap.lookup (Heap.set h k c) l =
      if l = k then some c else Heap.lookup h l := by
  by_cases hlk : l = k
  · subst hlk; simp [Heap.lookup_set_self]
  · simp [hlk, Machine.Heap.lookup_set_ne (Ne.symm hlk)]

/-! ## The state simulation relation -/

/-- The design's `SimState`, plus the seed-constant clauses that make
it inductive (see the module docstring). -/
structure FrameSim (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap)
    (σ σF : ExecState) : Prop where
  spec : ShiftSpec ρ na₀ na
  types_eq : σF.types = σ.types
  funcs_eq : σF.functions = σ.functions
  methods_eq : σF.methods = σ.methods
  methodSets_eq : σF.methodSets = σ.methodSets
  next_eq : σF.nextAddr = ρ σ.nextAddr
  alloc_reg : na₀ ≤ σ.nextAddr
  lookup_img : ∀ l : Loc, Heap.lookup σF.heap (renameLoc ρ l) =
      match Heap.lookup σ.heap l with
      | some c => some (renameCell ρ c)
      | none => Heap.lookup fr (renameLoc ρ l)
  frame_pres : ∀ l c, Heap.lookup fr l = some c →
      Heap.lookup σF.heap l = some c
  fr_avoid : ∀ a : Nat, Heap.lookup fr (.base ⟨ρ a⟩) = none
  bodies_inv : ∀ f ∈ σ.functions.toList, renameStmt ρ f.body = f.body

namespace FrameSim

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem hinj (h : FrameSim ρ na₀ na fr σ σF) :
    ∀ {x y : Nat}, ρ x = ρ y → x = y := h.spec.inj

theorem lookup_some (h : FrameSim ρ na₀ na fr σ σF) {l : Loc} {c : HeapCell}
    (hl : Heap.lookup σ.heap l = some c) :
    Heap.lookup σF.heap (renameLoc ρ l) = some (renameCell ρ c) := by
  have := h.lookup_img l
  rw [hl] at this
  exact this

theorem lookup_none_base (h : FrameSim ρ na₀ na fr σ σF) {a : Nat}
    (hl : Heap.lookup σ.heap (.base ⟨a⟩) = none) :
    Heap.lookup σF.heap (.base ⟨ρ a⟩) = none := by
  have himg := h.lookup_img (.base ⟨a⟩)
  rw [hl] at himg
  simpa [renameLoc, h.fr_avoid a] using himg

/-- Writing the same (renamed) cell at the same (renamed) BASE address
on both sides preserves the simulation. The base restriction is what
makes the frame provably untouched: `Heap.set` in the machine fires
only at `.base` keys (`storeLoc`'s base arm; allocation), and
`fr_avoid` excludes frame cells exactly there. -/
theorem setBase (h : FrameSim ρ na₀ na fr σ σF) (a : Nat) (c : HeapCell) :
    FrameSim ρ na₀ na fr
      { σ with heap := Heap.set σ.heap (.base ⟨a⟩) c }
      { σF with heap := Heap.set σF.heap (.base ⟨ρ a⟩) (renameCell ρ c) } where
  spec := h.spec
  types_eq := h.types_eq
  funcs_eq := h.funcs_eq
  methods_eq := h.methods_eq
  methodSets_eq := h.methodSets_eq
  next_eq := h.next_eq
  alloc_reg := h.alloc_reg
  lookup_img := by
    intro l
    by_cases hla : l = .base ⟨a⟩
    · subst hla
      simp [renameLoc, Heap.lookup_set_self]
    · have hrne : renameLoc ρ l ≠ .base ⟨ρ a⟩ := by
        intro hc
        exact hla (renameLoc_base_inv h.spec.inj hc)
      have h1 : Heap.lookup (Heap.set σF.heap (.base ⟨ρ a⟩) (renameCell ρ c))
          (renameLoc ρ l) = Heap.lookup σF.heap (renameLoc ρ l) :=
        Machine.Heap.lookup_set_ne (Ne.symm hrne)
      have h2 : Heap.lookup (Heap.set σ.heap (.base ⟨a⟩) c) l
          = Heap.lookup σ.heap l :=
        Machine.Heap.lookup_set_ne (Ne.symm hla)
      rw [h1, h2]
      exact h.lookup_img l
  frame_pres := by
    intro l c₀ hl
    have hne : (.base ⟨ρ a⟩ : Loc) ≠ l := by
      intro hc
      rw [← hc] at hl
      rw [h.fr_avoid a] at hl
      cases hl
    rw [Machine.Heap.lookup_set_ne hne]
    exact h.frame_pres l c₀ hl
  fr_avoid := h.fr_avoid
  bodies_inv := h.bodies_inv

/-- Allocation commutes on the fresh location: the framed run allocates
at the renamed fresh address. -/
theorem alloc_fst (h : FrameSim ρ na₀ na fr σ σF) (v : GoValue)
    (ty : Option Ty) :
    (ExecState.alloc σF (renameValue ρ v) ty).1 =
      renameLoc ρ (ExecState.alloc σ v ty).1 := by
  simp [ExecState.alloc, ExecState.freshLoc, h.next_eq, renameLoc]

/-- Allocation commutes on the successor states. This is where the
shift law (`ρ (x+1) = ρ x + 1` on the fresh region) earns its keep. -/
theorem alloc_snd (h : FrameSim ρ na₀ na fr σ σF) (v : GoValue)
    (ty : Option Ty) :
    FrameSim ρ na₀ na fr (ExecState.alloc σ v ty).2
      (ExecState.alloc σF (renameValue ρ v) ty).2 := by
  have hset := h.setBase σ.nextAddr { declaredTy := ty, value := v }
  refine ⟨h.spec, h.types_eq, h.funcs_eq, h.methods_eq, h.methodSets_eq,
    ?_, ?_, ?_, ?_, h.fr_avoid, h.bodies_inv⟩
  · show σF.nextAddr + 1 = ρ (σ.nextAddr + 1)
    rw [h.spec.succ h.alloc_reg, h.next_eq]
  · exact Nat.le_succ_of_le h.alloc_reg
  · intro l
    have himg := hset.lookup_img l
    simpa [ExecState.alloc, ExecState.freshLoc, h.next_eq, renameCell]
      using himg
  · intro l c hl
    have hfp := hset.frame_pres l c hl
    simpa [ExecState.alloc, ExecState.freshLoc, h.next_eq, renameCell]
      using hfp

end FrameSim

end GoLean.Frame
