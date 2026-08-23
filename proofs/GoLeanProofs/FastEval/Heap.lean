import GoLean.GoCore.StepFn

/-!
# FastEval — the trie heap and its abstraction (campaign Arc 2, U4)

Design: `docs/2026-08-22_fasteval-design.md`. FastEval is an
ACCELERATOR under the §3.1 template: **untrusted method — no name from
this directory may appear in any headline statement's closure** (Sym's
position). The refinement is ONE-DIRECTIONAL (fast `.ok` ⟹ slow
`.ok`), so nothing here needs completeness, and the abstraction `γH`
is TOTAL (holes dump a dummy cell) — the assembly's single
`γF σF₀ = s₃` kernel equality is what forces the trie to represent
the real state exactly; no carried well-formedness invariant.

All recursion is STRUCTURAL (bit lists + explicit fuel) — the kernel
does not usefully reduce `WellFounded.fix` (U3 finding, memo §6.5).
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore

/-- The trie heap: values at canonical bit paths. -/
inductive HeapT where
  | leaf
  | node (v : Option HeapCell) (l r : HeapT)

/-- Canonical LSB-first bits of `k` (no trailing `false`s), fuel-
structural; `fuel = k + 1` always suffices (`k < 2 ^ (k+1)`). -/
def keyBits : Nat → Nat → List Bool
  | 0, _ => []
  | fuel + 1, k =>
      if k == 0 then []
      else (k % 2 == 1) :: keyBits fuel (k / 2)

theorem lt_two_pow_succ (a : Nat) : a < 2 ^ (a + 1) := by
  induction a with
  | zero => decide
  | succ a ih => rw [Nat.pow_succ]; omega

/-- Decode — the injectivity witness for `keyBits`. -/
def unbits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * unbits bs

theorem unbits_keyBits : ∀ (fuel k : Nat), k < 2 ^ fuel →
    unbits (keyBits fuel k) = k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0; rfl
  | succ fuel ih =>
      intro k hk
      by_cases h0 : k = 0
      · subst h0; simp [keyBits, unbits]
      · have hk2 : k / 2 < 2 ^ fuel := by
          apply Nat.div_lt_of_lt_mul
          calc k < 2 ^ (fuel + 1) := hk
            _ = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
        have hk0 : (k == 0) = false := by simpa using h0
        simp only [keyBits, hk0, Bool.false_eq_true, if_false, unbits]
        rw [ih _ hk2]
        rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
          simp [h] <;> omega

theorem keyBits_inj {a b : Nat}
    (h : keyBits (a + 1) a = keyBits (b + 1) b) : a = b := by
  have ha := unbits_keyBits (a + 1) a (lt_two_pow_succ a)
  have hb := unbits_keyBits (b + 1) b (lt_two_pow_succ b)
  rw [← ha, ← hb, h]

def HeapT.getB : HeapT → List Bool → Option HeapCell
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l _, false :: bs => l.getB bs
  | .node _ _ r, true :: bs => r.getB bs

def HeapT.setB : HeapT → List Bool → HeapCell → HeapT
  | .leaf, [], c => .node (some c) .leaf .leaf
  | .node _ l r, [], c => .node (some c) l r
  | .leaf, false :: bs, c => .node none (HeapT.setB .leaf bs c) .leaf
  | .leaf, true :: bs, c => .node none .leaf (HeapT.setB .leaf bs c)
  | .node v l r, false :: bs, c => .node v (l.setB bs c) r
  | .node v l r, true :: bs, c => .node v l (r.setB bs c)

theorem HeapT.getB_setB_self : ∀ (bs : List Bool) (t : HeapT) (c : HeapCell),
    (t.setB bs c).getB bs = some c := by
  intro bs
  induction bs with
  | nil => intro t c; cases t <;> rfl
  | cons b bs ih => intro t c; cases t <;> cases b <;> simp [setB, getB, ih]

theorem HeapT.getB_setB_ne : ∀ (bs bs' : List Bool) (t : HeapT) (c : HeapCell),
    bs ≠ bs' → (t.setB bs c).getB bs' = t.getB bs' := by
  intro bs
  induction bs with
  | nil =>
      intro bs' t c hne
      cases bs' with
      | nil => exact absurd rfl hne
      | cons b' bs' => cases t <;> cases b' <;> simp [setB, getB]
  | cons b bs ih =>
      intro bs' t c hne
      cases bs' with
      | nil => cases t <;> cases b <;> simp [setB, getB]
      | cons b' bs' =>
          by_cases hb : b = b'
          · subst hb
            have : bs ≠ bs' := by intro h; exact hne (by rw [h])
            cases t <;> cases b <;> simp [setB, getB, ih _ _ _ this]
          · cases t <;> cases b <;> cases b' <;>
              simp_all [setB, getB]

/-- Point read. -/
def HeapT.get (t : HeapT) (a : Nat) : Option HeapCell :=
  t.getB (keyBits (a + 1) a)

/-- Point write (create-or-replace). -/
def HeapT.set (t : HeapT) (a : Nat) (c : HeapCell) : HeapT :=
  t.setB (keyBits (a + 1) a) c

theorem HeapT.get_set_self (t : HeapT) (a : Nat) (c : HeapCell) :
    (t.set a c).get a = some c := getB_setB_self ..

theorem HeapT.get_set_ne (t : HeapT) {a b : Nat} (c : HeapCell)
    (hne : a ≠ b) : (t.set a c).get b = t.get b :=
  getB_setB_ne _ _ _ _ (fun h => hne (keyBits_inj h))

/-- The hole dump — unreachable once the assembly's `γF σF₀ = s₃`
equality holds (a hole would surface there and fail the kernel
check); kept so `γH` is total. -/
def dummyCell : HeapCell := { value := .nil }

/-- THE ABSTRACTION: the address-ascending range dump. The machine's
own heap has exactly this shape at every reachable state — `alloc`
appends at ascending fresh addresses (`Heap.set` appends on a missing
key, `State.lean`), and nothing frees (probe C: `heapLen = nextAddr`
throughout the run). -/
def γH (t : HeapT) : Nat → Heap
  | 0 => []
  | n + 1 => γH t n ++ [(Loc.base ⟨n⟩, (t.get n).getD dummyCell)]

/-! ## List-side helpers (the only place list-vs-trie reasoning lives) -/

theorem heap_lookup_append (h₁ h₂ : Heap) (k : Loc) :
    Heap.lookup (h₁ ++ h₂) k =
      ((Heap.lookup h₁ k).or (Heap.lookup h₂ k)) := by
  induction h₁ with
  | nil => simp [Heap.lookup]
  | cons e h₁ ih =>
      obtain ⟨l, c⟩ := e
      by_cases hlk : (l == k) = true <;>
        simp [Heap.lookup, hlk, ih]

theorem heap_set_append_left (h₁ h₂ : Heap) (k : Loc) (c : HeapCell)
    (hmem : (Heap.lookup h₁ k).isSome) :
    Heap.set (h₁ ++ h₂) k c = Heap.set h₁ k c ++ h₂ := by
  induction h₁ with
  | nil => simp [Heap.lookup] at hmem
  | cons e h₁ ih =>
      obtain ⟨l, cl⟩ := e
      by_cases hlk : (l == k) = true
      · simp [Heap.set, hlk]
      · simp [Heap.lookup, hlk] at hmem
        simp [Heap.set, hlk, ih hmem]

theorem heap_set_append_right (h₁ h₂ : Heap) (k : Loc) (c : HeapCell)
    (hmiss : Heap.lookup h₁ k = none) :
    Heap.set (h₁ ++ h₂) k c = h₁ ++ Heap.set h₂ k c := by
  induction h₁ with
  | nil => simp
  | cons e h₁ ih =>
      obtain ⟨l, cl⟩ := e
      by_cases hlk : (l == k) = true
      · simp [Heap.lookup, hlk] at hmiss
      · simp [Heap.lookup, hlk] at hmiss
        simp [Heap.set, hlk, ih hmiss]

theorem heap_set_missing_append (h : Heap) (k : Loc) (c : HeapCell)
    (hmiss : Heap.lookup h k = none) :
    Heap.set h k c = h ++ [(k, c)] := by
  induction h with
  | nil => rfl
  | cons e h ih =>
      obtain ⟨l, cl⟩ := e
      by_cases hlk : (l == k) = true
      · simp [Heap.lookup, hlk] at hmiss
      · simp [Heap.lookup, hlk] at hmiss
        simp [Heap.set, hlk, ih hmiss]

/-- `Loc.base ⟨a⟩ == Loc.base ⟨b⟩` is address equality (the derived
`BEq` unfolds structurally). -/
theorem loc_base_beq (a b : Nat) :
    (Loc.base ⟨a⟩ == Loc.base ⟨b⟩) = (a == b) := rfl

/-! ## The γ lemmas -/

theorem γH_lookup (t : HeapT) : ∀ (n a : Nat),
    Heap.lookup (γH t n) (Loc.base ⟨a⟩) =
      if a < n then some ((t.get a).getD dummyCell) else none := by
  intro n
  induction n with
  | zero => intro a; simp [γH, Heap.lookup]
  | succ n ih =>
      intro a
      rw [γH, heap_lookup_append, ih]
      by_cases han : a < n
      · have h3 : a < n + 1 := by omega
        simp [han, h3]
      · by_cases han' : a = n
        · subst han'
          simp [han, Heap.lookup, loc_base_beq]
        · have h1 : ¬ a < n + 1 := by omega
          have h2 : (a == n) = false := by
            simp only [beq_eq_false_iff_ne]; omega
          simp [han, h1, Heap.lookup, loc_base_beq, h2]
          omega

theorem γH_congr {t t' : HeapT} : ∀ {n : Nat},
    (∀ a, a < n → t.get a = t'.get a) → γH t n = γH t' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [γH, γH, ih (fun a ha => h a (by omega)), h n (by omega)]

/-- Writes at live addresses commute with the dump. -/
theorem γH_set (t : HeapT) (c : HeapCell) : ∀ (n a : Nat), a < n →
    γH (t.set a c) n = Heap.set (γH t n) (Loc.base ⟨a⟩) c := by
  intro n
  induction n with
  | zero => intro a ha; omega
  | succ n ih =>
      intro a ha
      by_cases han : a = n
      · subst han
        rw [γH, γH,
          γH_congr (t := t.set a c) (t' := t)
            (fun b hb => HeapT.get_set_ne t c (by omega)),
          HeapT.get_set_self,
          heap_set_append_right _ _ _ _ (by simp [γH_lookup]),
          Heap.set]
        simp [loc_base_beq]
      · have ha' : a < n := by omega
        rw [γH, γH, ih a ha',
          HeapT.get_set_ne t c (fun h => han h),
          heap_set_append_left _ _ _ _ (by simp [γH_lookup, ha'])]

/-- Allocation at the frontier is the dump's append — matching the
machine's own `Heap.set`-on-missing append. -/
theorem γH_alloc (t : HeapT) (c : HeapCell) (n : Nat) :
    γH (t.set n c) (n + 1) = γH t n ++ [(Loc.base ⟨n⟩, c)] := by
  rw [γH,
    γH_congr (t := t.set n c) (t' := t)
      (fun b hb => HeapT.get_set_ne t c (by omega)),
    HeapT.get_set_self]
  simp [Option.getD]

/-- The slow side of allocation: setting a fresh key appends. -/
theorem γH_slow_alloc (t : HeapT) (c : HeapCell) (n : Nat) :
    Heap.set (γH t n) (Loc.base ⟨n⟩) c = γH (t.set n c) (n + 1) := by
  rw [heap_set_missing_append _ _ _ (by simp [γH_lookup]), γH_alloc]

end GoLean.FastEval
