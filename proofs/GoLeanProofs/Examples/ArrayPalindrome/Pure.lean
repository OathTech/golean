import GoLeanProofs.SliceMem

/-!
# ArrayPalindrome — Pure

The example's entire mathematical content: what "is a palindrome"
means, and the half-scan characterisation the Go loop actually decides.

`palinSpec` is STATEMENT vocabulary — the headline says the returned
verdict IS `palinSpec` of the returned data, and nothing else in this
module reaches the statement layer. Everything below `palinSpec` is
proof method: the Go subject walks two indices inward and stops at the
middle, so the machine-side invariant is "every pair checked SO FAR
matches", and `palin_iff_half` is the bridge from that half-scan
invariant to `pre.reverse = pre`.
-/

namespace GoLean.Examples.ArrayPalindrome

open GoLean

set_option maxRecDepth 1000000

/-! ## The specification function -/

/-- **The specification**: `1` when the list reads the same forwards
and backwards, `0` otherwise — Go's `isPalindrome` verdict, defined the
way a mathematician would write it (`xs.reverse = xs`), with no index
arithmetic anywhere in the statement. -/
def palinSpec (xs : List Int) : Int :=
  if xs.reverse = xs then 1 else 0

theorem palinSpec_eq_one {xs : List Int} (h : xs.reverse = xs) :
    palinSpec xs = 1 := by
  simp [palinSpec, h]

theorem palinSpec_eq_zero {xs : List Int} (h : ¬ xs.reverse = xs) :
    palinSpec xs = 0 := by
  simp [palinSpec, h]

/-! ## The half-scan characterisation

The Go loop runs `i` up from `0` and `j` down from `len-1`, comparing
`s[i]` with `s[j]` and stopping when `i ≥ j`. So it inspects exactly
the pairs `(t, len-1-t)` for `t < len/2` — the first half — and
`palin_iff_half` is the theorem that this is enough. -/

/-- The half-scan predicate: every pair the loop has checked up to `m`
matched. -/
def PalinUpTo (xs : List Int) (m : Nat) : Prop :=
  ∀ t : Nat, t < m → xs.getD t 0 = xs.getD (xs.length - 1 - t) 0

theorem palinUpTo_zero (xs : List Int) : PalinUpTo xs 0 := by
  intro t ht; omega

theorem palinUpTo_succ {xs : List Int} {m : Nat} (h : PalinUpTo xs m)
    (hm : xs.getD m 0 = xs.getD (xs.length - 1 - m) 0) :
    PalinUpTo xs (m + 1) := by
  intro t ht
  rcases Nat.lt_or_ge t m with hlt | hge
  · exact h t hlt
  · have : t = m := by omega
    subst this; exact hm

/-- The verdict is a machine integer. -/
theorem palinSpec_range (xs : List Int) :
    0 ≤ palinSpec xs ∧ palinSpec xs < 2 ^ 64 := by
  rw [palinSpec]; split <;> omega

/-- Indexing a list's reverse, in the `getD` spelling the machine
segments produce. -/
theorem getD_reverse (xs : List Int) {t : Nat} (ht : t < xs.length) :
    xs.reverse.getD t 0 = xs.getD (xs.length - 1 - t) 0 := by
  have h1 : t < xs.reverse.length := by rw [List.length_reverse]; omega
  have h2 : xs.length - 1 - t < xs.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    List.getElem_reverse]

/-- **The bridge**: scanning the first half is enough. `xs` is a
palindrome exactly when every pair `(t, len-1-t)` with `t < len/2`
matches — which is precisely the loop's exit invariant. -/
theorem palin_iff_half (xs : List Int) :
    xs.reverse = xs ↔ PalinUpTo xs (xs.length / 2) := by
  constructor
  · intro h t ht
    have htl : t < xs.length := by omega
    rw [← getD_reverse xs htl, h]
  · intro h
    apply List.ext_getElem (by rw [List.length_reverse])
    intro t h1 h2
    have htl : t < xs.length := h2
    have key : ∀ u : Nat, u < xs.length / 2 →
        xs.getD u 0 = xs.getD (xs.length - 1 - u) 0 := h
    have hgoal : xs.reverse.getD t 0 = xs.getD t 0 := by
      rw [getD_reverse xs htl]
      rcases Nat.lt_or_ge t (xs.length / 2) with hlt | hge
      · exact (key t hlt).symm
      · rcases Nat.lt_or_ge (xs.length - 1 - t) (xs.length / 2) with hlt2 | hge2
        · have := key (xs.length - 1 - t) hlt2
          rw [show xs.length - 1 - (xs.length - 1 - t) = t from by omega] at this
          exact this
        · -- the odd middle: `t` is its own mirror
          have : xs.length - 1 - t = t := by omega
          rw [this]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at hgoal
    exact hgoal

/-- The loop-exit reading: the full half scan certifies a palindrome. -/
theorem palinSpec_of_full {xs : List Int} (h : PalinUpTo xs (xs.length / 2)) :
    palinSpec xs = 1 :=
  palinSpec_eq_one ((palin_iff_half xs).mpr h)

/-- The early-return reading: ONE mismatched pair refutes it. Stated at
the index the Go loop is standing on when it returns `0`. -/
theorem palinSpec_of_mismatch {xs : List Int} {m : Nat} (hm : m < xs.length)
    (h : xs.getD m 0 ≠ xs.getD (xs.length - 1 - m) 0) :
    palinSpec xs = 0 := by
  refine palinSpec_eq_zero (fun hrev => h ?_)
  rw [← getD_reverse xs hm, hrev]

end GoLean.Examples.ArrayPalindrome
