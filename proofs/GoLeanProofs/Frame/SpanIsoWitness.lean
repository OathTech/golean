import GoLeanProofs.Frame.SpanIso

/-! # `SpanIso` occupation witnesses (CE1, 2026-08-27)

The relational face's own non-vacuity, proved DIRECTLY from the
definition (no canonicalizer, no iff): a pair of states genuinely
differing on ALL THREE erased axes' small forms — different slice
CAPS, different backing-array SIZES (zero-like tails of different
lengths), different allocation GARBAGE — witnessed span-isomorphic;
and a pair differing in KEPT content refuted. These are the smoke
tests that the definition's clauses are dischargeable and that the
relation distinguishes content — run before the iff is built on it
(the witness-with-its-law rule, applied to the relation itself).

The proofs work from a REACHABLE-VALUE INVENTORY lemma (every
`RVal`-derivable value on these tiny states is one of two listed
values), which is the small-scale template for how `SpanIso` premises
discharge: reachability inversion, then clause-by-clause. -/

namespace GoLean.Frame.ChoiceErase.SpanIsoWitness

open GoLean GoLean.GoCore GoLean.Frame.ChoiceErase

/-- Witness state A: cell 0 = the backing array `[1, 0, 0]` (size 3);
cell 1 = allocation GARBAGE (unreachable, value 99). -/
def wA : ExecState :=
  { heap := [ (.base ⟨0⟩, { value := .array #[.int 1 .int, .int 0 .int, .int 0 .int] }),
              (.base ⟨1⟩, { value := .int 99 .int }) ],
    nextAddr := 2 }

/-- Witness state B: cell 0 = the backing array `[1, 0]` (size 2 —
capacity slack realized as a different backing length); no garbage. -/
def wB : ExecState :=
  { heap := [ (.base ⟨0⟩, { value := .array #[.int 1 .int, .int 0 .int] }) ],
    nextAddr := 1 }

/-- Witness state C: B's shape with DIFFERENT KEPT CONTENT (`2`). -/
def wC : ExecState :=
  { heap := [ (.base ⟨0⟩, { value := .array #[.int 2 .int, .int 0 .int] }) ],
    nextAddr := 1 }

/-- Roots: one slice handle onto cell 0, window `[0,1)`, cap 3 / 2 /
2 respectively — the caps differ across the pair (the slack axis). -/
def rA : List GoValue := [.slice ⟨some (.base ⟨0⟩), 0, 1, 3⟩]
def rB : List GoValue := [.slice ⟨some (.base ⟨0⟩), 0, 1, 2⟩]

private def sliceA : GoValue := .slice ⟨some (.base ⟨0⟩), 0, 1, 3⟩
private def sliceB : GoValue := .slice ⟨some (.base ⟨0⟩), 0, 1, 2⟩

/-! ## The reachable-value inventories -/

/-- Everything `RVal`-reachable in A is the root handle or the kept
element `1`. (The garbage cell and the zero tail are NOT here — that
is the erasure, relationally.) -/
theorem inventoryA : ∀ v, RVal wA.heap [] rA v → v = sliceA ∨ v = .int 1 .int := by
  intro v hr
  induction hr with
  | root hv =>
      simp only [rA, List.mem_singleton] at hv
      exact Or.inl hv
  | structField hr hi hm ih => rcases ih with h | h <;> simp [sliceA] at h
  | arrayElem hr hi ih => rcases ih with h | h <;> simp [sliceA] at h
  | ifaceVal hr ih => rcases ih with h | h <;> simp [sliceA] at h
  | funcCap hr hv ih => rcases ih with h | h <;> simp [sliceA] at h
  | mapKey hr hi ih => rcases ih with h | h <;> simp [sliceA] at h
  | mapVal hr hi ih => rcases ih with h | h <;> simp [sliceA] at h
  | chanElem hr hi ih => rcases ih with h | h <;> simp [sliceA] at h
  | derefAddr hr hc ih => rcases ih with h | h <;> simp [sliceA] at h
  | derefMap hr hc ih => rcases ih with h | h <;> simp [sliceA] at h
  | derefChan hr hc ih => rcases ih with h | h <;> simp [sliceA] at h
  | sliceElem hr hc hval hw hi ih =>
      rename_i a off len cap cell vs i
      rcases ih with h | h
      · -- the handle is the root: base 0, window [0,1) — element 0 of
        -- the array cell, i.e. the kept `1`.
        simp only [sliceA, GoValue.slice.injEq, SliceValue.mk.injEq,
          Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
        obtain ⟨ha, hoff, hlen, -⟩ := h
        subst ha hoff hlen
        have hlook : Heap.lookup wA.heap (.base ⟨0⟩)
            = some { value := .array #[.int 1 .int, .int 0 .int, .int 0 .int] } := rfl
        rw [hlook] at hc
        obtain rfl := (Option.some.inj hc).symm
        simp only [GoValue.array.injEq] at hval
        subst hval
        have hi0 : i = 0 := by omega
        subst hi0
        exact Or.inr rfl
      · simp at h
  | sliceWhole hr hc hnv ih =>
      rename_i a off len cap cell
      rcases ih with h | h
      · simp only [sliceA, GoValue.slice.injEq, SliceValue.mk.injEq,
          Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
        obtain ⟨ha, -, -, -⟩ := h
        subst ha
        have hlook : Heap.lookup wA.heap (.base ⟨0⟩)
            = some { value := .array #[.int 1 .int, .int 0 .int, .int 0 .int] } := rfl
        rw [hlook] at hc
        obtain rfl := (Option.some.inj hc).symm
        exact absurd rfl (hnv #[.int 1 .int, .int 0 .int, .int 0 .int])
      · simp at h

/-- The B-side inventory (same script, size-2 backing). -/
theorem inventoryB : ∀ v, RVal wB.heap [] rB v → v = sliceB ∨ v = .int 1 .int := by
  intro v hr
  induction hr with
  | root hv =>
      simp only [rB, List.mem_singleton] at hv
      exact Or.inl hv
  | structField hr hi hm ih => rcases ih with h | h <;> simp [sliceB] at h
  | arrayElem hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | ifaceVal hr ih => rcases ih with h | h <;> simp [sliceB] at h
  | funcCap hr hv ih => rcases ih with h | h <;> simp [sliceB] at h
  | mapKey hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | mapVal hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | chanElem hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | derefAddr hr hc ih => rcases ih with h | h <;> simp [sliceB] at h
  | derefMap hr hc ih => rcases ih with h | h <;> simp [sliceB] at h
  | derefChan hr hc ih => rcases ih with h | h <;> simp [sliceB] at h
  | sliceElem hr hc hval hw hi ih =>
      rename_i a off len cap cell vs i
      rcases ih with h | h
      · simp only [sliceB, GoValue.slice.injEq, SliceValue.mk.injEq,
          Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
        obtain ⟨ha, hoff, hlen, -⟩ := h
        subst ha hoff hlen
        have hlook : Heap.lookup wB.heap (.base ⟨0⟩)
            = some { value := .array #[.int 1 .int, .int 0 .int] } := rfl
        rw [hlook] at hc
        obtain rfl := (Option.some.inj hc).symm
        simp only [GoValue.array.injEq] at hval
        subst hval
        have hi0 : i = 0 := by omega
        subst hi0
        exact Or.inr rfl
      · simp at h
  | sliceWhole hr hc hnv ih =>
      rename_i a off len cap cell
      rcases ih with h | h
      · simp only [sliceB, GoValue.slice.injEq, SliceValue.mk.injEq,
          Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
        obtain ⟨ha, -, -, -⟩ := h
        subst ha
        have hlook : Heap.lookup wB.heap (.base ⟨0⟩)
            = some { value := .array #[.int 1 .int, .int 0 .int] } := rfl
        rw [hlook] at hc
        obtain rfl := (Option.some.inj hc).symm
        exact absurd rfl (hnv #[.int 1 .int, .int 0 .int])
      · simp at h

/-- The C-side inventory (kept content `2`). -/
theorem inventoryC : ∀ v, RVal wC.heap [] rB v → v = sliceB ∨ v = .int 2 .int := by
  intro v hr
  induction hr with
  | root hv =>
      simp only [rB, List.mem_singleton] at hv
      exact Or.inl hv
  | structField hr hi hm ih => rcases ih with h | h <;> simp [sliceB] at h
  | arrayElem hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | ifaceVal hr ih => rcases ih with h | h <;> simp [sliceB] at h
  | funcCap hr hv ih => rcases ih with h | h <;> simp [sliceB] at h
  | mapKey hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | mapVal hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | chanElem hr hi ih => rcases ih with h | h <;> simp [sliceB] at h
  | derefAddr hr hc ih => rcases ih with h | h <;> simp [sliceB] at h
  | derefMap hr hc ih => rcases ih with h | h <;> simp [sliceB] at h
  | derefChan hr hc ih => rcases ih with h | h <;> simp [sliceB] at h
  | sliceElem hr hc hval hw hi ih =>
      rename_i a off len cap cell vs i
      rcases ih with h | h
      · simp only [sliceB, GoValue.slice.injEq, SliceValue.mk.injEq,
          Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
        obtain ⟨ha, hoff, hlen, -⟩ := h
        subst ha hoff hlen
        have hlook : Heap.lookup wC.heap (.base ⟨0⟩)
            = some { value := .array #[.int 2 .int, .int 0 .int] } := rfl
        rw [hlook] at hc
        obtain rfl := (Option.some.inj hc).symm
        simp only [GoValue.array.injEq] at hval
        subst hval
        have hi0 : i = 0 := by omega
        subst hi0
        exact Or.inr rfl
      · simp at h
  | sliceWhole hr hc hnv ih =>
      rename_i a off len cap cell
      rcases ih with h | h
      · simp only [sliceB, GoValue.slice.injEq, SliceValue.mk.injEq,
          Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
        obtain ⟨ha, -, -, -⟩ := h
        subst ha
        have hlook : Heap.lookup wC.heap (.base ⟨0⟩)
            = some { value := .array #[.int 2 .int, .int 0 .int] } := rfl
        rw [hlook] at hc
        obtain rfl := (Option.some.inj hc).symm
        exact absurd rfl (hnv #[.int 2 .int, .int 0 .int])
      · simp at h

/-! ## Derived span facts, per side -/

section Facts

private theorem notDirectA : ∀ a, ¬ DirectRef wA.heap [] rA a := by
  intro a h
  rcases h with h | h | h <;> rcases inventoryA _ h with h' | h' <;> simp [sliceA] at h'

private theorem notDirectB : ∀ a, ¬ DirectRef wB.heap [] rB a := by
  intro a h
  rcases h with h | h | h <;> rcases inventoryB _ h with h' | h' <;> simp [sliceB] at h'

private theorem notDirectC : ∀ a, ¬ DirectRef wC.heap [] rB a := by
  intro a h
  rcases h with h | h | h <;> rcases inventoryC _ h with h' | h' <;> simp [sliceB] at h'

private theorem viewedA : ∀ a w, ViewedAt wA.heap [] rA a w → a = 0 ∧ w = 1 := by
  intro a w ⟨off, len, cap, hr, hw⟩
  rcases inventoryA _ hr with h | h
  · simp only [sliceA, GoValue.slice.injEq, SliceValue.mk.injEq,
      Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
    obtain ⟨ha, hoff, hlen, -⟩ := h
    omega
  · simp at h

private theorem viewedB : ∀ a w, ViewedAt wB.heap [] rB a w → a = 0 ∧ w = 1 := by
  intro a w ⟨off, len, cap, hr, hw⟩
  rcases inventoryB _ hr with h | h
  · simp only [sliceB, GoValue.slice.injEq, SliceValue.mk.injEq,
      Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
    obtain ⟨ha, hoff, hlen, -⟩ := h
    omega
  · simp at h

private theorem viewedC : ∀ a w, ViewedAt wC.heap [] rB a w → a = 0 ∧ w = 1 := by
  intro a w ⟨off, len, cap, hr, hw⟩
  rcases inventoryC _ hr with h | h
  · simp only [sliceB, GoValue.slice.injEq, SliceValue.mk.injEq,
      Option.some.injEq, Loc.base.injEq, Addr.mk.injEq] at h
    obtain ⟨ha, hoff, hlen, -⟩ := h
    omega
  · simp at h

private theorem viewedA0 : ViewedAt wA.heap [] rA 0 1 :=
  ⟨0, 1, 3, RVal.root (by simp [rA]), rfl⟩

private theorem viewedB0 : ViewedAt wB.heap [] rB 0 1 :=
  ⟨0, 1, 2, RVal.root (by simp [rB]), rfl⟩

private theorem viewedC0 : ViewedAt wC.heap [] rB 0 1 :=
  ⟨0, 1, 2, RVal.root (by simp [rB]), rfl⟩

private theorem cellReachA : ∀ a, CellReach wA.heap [] rA a → a = 0 := by
  intro a h
  rcases h with h | ⟨w, h⟩
  · exact absurd h (notDirectA a)
  · exact (viewedA a w h).1

private theorem cellReachB : ∀ a, CellReach wB.heap [] rB a → a = 0 := by
  intro a h
  rcases h with h | ⟨w, h⟩
  · exact absurd h (notDirectB a)
  · exact (viewedB a w h).1

private theorem cellReachC : ∀ a, CellReach wC.heap [] rB a → a = 0 := by
  intro a h
  rcases h with h | ⟨w, h⟩
  · exact absurd h (notDirectC a)
  · exact (viewedC a w h).1

private theorem reachA0 : CellReach wA.heap [] rA 0 := Or.inr ⟨1, viewedA0⟩
private theorem reachB0 : CellReach wB.heap [] rB 0 := Or.inr ⟨1, viewedB0⟩

private theorem maxViewA0 : MaxView wA.heap [] rA 0 1 :=
  ⟨viewedA0, fun w h => (viewedA 0 w h).2 ▸ Nat.le_refl 1⟩

private theorem maxViewB0 : MaxView wB.heap [] rB 0 1 :=
  ⟨viewedB0, fun w h => (viewedB 0 w h).2 ▸ Nat.le_refl 1⟩

private theorem relCleanA : RelClean wA.heap [] rA where
  base_present a h := by
    obtain rfl := cellReachA a h
    exact ⟨_, rfl⟩
  no_mixed a w hd _ := absurd hd (notDirectA a)
  keys_scalar es hr := by rcases inventoryA _ hr with h | h <;> simp [sliceA] at h
  max_exists a w hv := by
    obtain ⟨rfl, -⟩ := viewedA a w hv
    exact ⟨1, maxViewA0⟩
  tails_zero a W c vs hnd hmv hl hval i hi hmin := by
    obtain ⟨rfl, rfl⟩ := viewedA a W hmv.1
    have hlook : Heap.lookup wA.heap (.base ⟨0⟩)
        = some { value := .array #[.int 1 .int, .int 0 .int, .int 0 .int] } := rfl
    rw [hlook] at hl
    obtain rfl := (Option.some.inj hl).symm
    simp only [GoValue.array.injEq] at hval
    subst hval
    have : i = 1 ∨ i = 2 := by simp at hi hmin ⊢; omega
    rcases this with rfl | rfl
    · exact ZeroLike.int
    · exact ZeroLike.int

private theorem relCleanB : RelClean wB.heap [] rB where
  base_present a h := by
    obtain rfl := cellReachB a h
    exact ⟨_, rfl⟩
  no_mixed a w hd _ := absurd hd (notDirectB a)
  keys_scalar es hr := by rcases inventoryB _ hr with h | h <;> simp [sliceB] at h
  max_exists a w hv := by
    obtain ⟨rfl, -⟩ := viewedB a w hv
    exact ⟨1, maxViewB0⟩
  tails_zero a W c vs hnd hmv hl hval i hi hmin := by
    obtain ⟨rfl, rfl⟩ := viewedB a W hmv.1
    have hlook : Heap.lookup wB.heap (.base ⟨0⟩)
        = some { value := .array #[.int 1 .int, .int 0 .int] } := rfl
    rw [hlook] at hl
    obtain rfl := (Option.some.inj hl).symm
    simp only [GoValue.array.injEq] at hval
    subst hval
    have : i = 1 := by simp at hi hmin ⊢; omega
    subst this
    exact ZeroLike.int

end Facts

/-! ## The positive witness: A ≃ B on all three erased axes -/

/-- **The occupation witness**: A and B — different slice caps (3 vs
2), different backing sizes (3 vs 2, zero-like tails), different
allocation garbage (cell 1 vs none) — are span-isomorphic at the
identity bijection. Every clause discharged directly from the
definition; no canonicalizer anywhere in this proof. -/
theorem spanIsoAt_wAB : SpanIsoAt [] wA rA wB rB (fun a => a) where
  clean := relCleanA
  clean' := relCleanB
  roots_len := rfl
  roots_corr i hi hi' := by
    have : i = 0 := by simp [rA] at hi; omega
    subst this
    exact VCorr.slice (a := 0) (off := 0) (len := 1) (cap := 3) (cap' := 2)
  reach_map a h := by
    obtain rfl := cellReachA a h
    exact reachB0
  reach_inj a b ha hb h := by
    obtain rfl := cellReachA a ha
    obtain rfl := cellReachA b hb
    rfl
  reach_surj a' h := by
    obtain rfl := cellReachB a' h
    exact ⟨0, reachA0, rfl⟩
  direct_iff a h :=
    iff_of_false (notDirectA a) (notDirectB _)
  viewed_iff a w h := by
    obtain rfl := cellReachA a h
    constructor
    · intro hv
      obtain ⟨-, rfl⟩ := viewedA 0 w hv
      exact viewedB0
    · intro hv
      obtain ⟨-, rfl⟩ := viewedB _ w hv
      exact viewedA0
  cells a h := by
    obtain rfl := cellReachA a h
    refine ⟨{ value := .array #[.int 1 .int, .int 0 .int, .int 0 .int] },
            { value := .array #[.int 1 .int, .int 0 .int] }, rfl, rfl,
            fun hd => absurd hd (notDirectA 0), fun _ => ?_⟩
    refine ⟨BackingTyCorr.none, fun hna => absurd rfl (hna _), ?_, ?_, ?_⟩
    · intro vs hvs
      exact ⟨#[.int 1 .int, .int 0 .int], rfl⟩
    · intro vs' hvs'
      exact ⟨#[.int 1 .int, .int 0 .int, .int 0 .int], rfl⟩
    · intro vs vs' hvs hvs'
      simp only [GoValue.array.injEq] at hvs hvs'
      subst hvs hvs'
      refine ⟨1, maxViewA0, rfl, ?_⟩
      intro i hi hi' hmin
      have : i = 0 := by simp at hmin; omega
      subst this
      exact VCorr.int

/-- **`SpanIso` is occupied** (the relation's non-vacuity, direct). -/
theorem spanIso_wAB : SpanIso [] wA rA wB rB := ⟨fun a => a, spanIsoAt_wAB⟩

/-! ## The negative witness: kept content distinguishes -/

/-- **The refutation**: A and C differ in the KEPT element (`1` vs
`2`) — no bijection makes them span-isomorphic (the window clause
forces `VCorr` on the kept prefix, and `VCorr` on ints is equality).
The erased axes are exactly the three witnessed above, nothing more. -/
theorem not_spanIso_wAC : ¬ SpanIso [] wA rA wC rB := by
  rintro ⟨φ, hiso⟩
  have hφ0 : φ 0 = 0 := cellReachC _ (hiso.reach_map 0 reachA0)
  obtain ⟨c, c', hl, hl', -, hnodir⟩ := hiso.cells 0 reachA0
  have hlookA : Heap.lookup wA.heap (.base ⟨0⟩)
      = some { value := .array #[.int 1 .int, .int 0 .int, .int 0 .int] } := rfl
  rw [hlookA] at hl
  obtain rfl := (Option.some.inj hl).symm
  rw [hφ0] at hl'
  have hlookC : Heap.lookup wC.heap (.base ⟨0⟩)
      = some { value := .array #[.int 2 .int, .int 0 .int] } := rfl
  rw [hlookC] at hl'
  obtain rfl := (Option.some.inj hl').symm
  obtain ⟨-, -, -, -, hwin⟩ := hnodir (notDirectA 0)
  obtain ⟨W, hmv, hmin, hpre⟩ := hwin _ _ rfl rfl
  obtain ⟨-, rfl⟩ := viewedA 0 W hmv.1
  have hv := hpre 0 (by show (0:Nat) < 3; omega) (by show (0:Nat) < 2; omega)
    (by show (0:Nat) < min 3 1; omega)
  cases hv
