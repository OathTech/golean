/-!
# Stein's binary gcd — the pure-`Nat` specification half

The mathematical side of the verified binary-GCD (Stein's algorithm)
example: three pure functions mirroring the Go program's three phases,
their branch equations in machine-consumable form (one lemma per
branch, explicit hypotheses), and the headline
`steinSpec_eq_gcd : steinSpec a b = Nat.gcd a b`.

The Go program's shape (the machine half is proved elsewhere, phase by
phase against exactly these equations):

* the FIRST loop strips the factors of two shared by `a` and `b`,
  counting them in `shift` — `commonTwos`;
* the SECOND loop strips the remaining twos from `a` — `stripTwos`;
* the SUBTRACT loop repeats { strip twos from `b`; order the pair so
  `a ≤ b`; `b := b - a` } until `b = 0` — `steinSub`;
* the result is `a << shift` — reassembled by `steinSpec`.

Core Lean only — no Mathlib, no `partial`, no `sorry`. The headline is
proved by well-founded recursion on `a + b` directly against
`commonTwos`'s branch structure (one shared factor of two peeled per
step via `Nat.gcd_mul_left`), which avoids any `2 ^ k ∣ a` bookkeeping.

(Gallery campaign unit G2.E3/stein, 2026-08-15. `#eval`-checked against
`Nat.gcd` on all of `[0,64]²` plus large spot pairs before the proofs
were trusted — the #eval-before-decide habit, applied to specs.)
-/

namespace GoLean.Examples.Stein

/-! ## The three phases -/

/-- The FIRST loop's count: how many shared factors of two the loop
strips from the pair before one component goes odd. The `a ≠ 0` guard
exists only to make the recursion well-founded; on the used domain
(`a ≥ 1`) it never fires differently from the program. -/
def commonTwos (a b : Nat) : Nat :=
  if a ≠ 0 ∧ a % 2 = 0 ∧ b % 2 = 0 then commonTwos (a / 2) (b / 2) + 1
  else 0
termination_by a
decreasing_by omega

/-- The SECOND loop (and the subtract loop's inner strip): divide by
two until the value is odd (or zero, which the loop leaves alone). -/
def stripTwos (n : Nat) : Nat :=
  if n ≠ 0 ∧ n % 2 = 0 then stripTwos (n / 2) else n
termination_by n
decreasing_by omega

/-- `stripTwos` never grows its argument (needed to found `steinSub`'s
recursion). -/
theorem stripTwos_le (n : Nat) : stripTwos n ≤ n := by
  by_cases h : n ≠ 0 ∧ n % 2 = 0
  · rw [stripTwos.eq_def, if_pos h]
    have := stripTwos_le (n / 2)
    omega
  · rw [stripTwos.eq_def, if_neg h]
    exact Nat.le_refl n
termination_by n
decreasing_by omega

/-- The SUBTRACT loop on the odd cores: strip twos from `b`, order the
pair, subtract, stop when the difference is zero. The `lo = 0` branch
is the loop's `b = 0` exit read gcd-faithfully (`gcd 0 x = x`); in the
recursive branch `lo ≥ 1`, so the measure `a + b` strictly decreases
to `hi ≤ a + stripTwos b - 1 < a + b`.

Written with the `min`/`max` terms inline (no `let`s) so each branch
equation below is a plain `if_pos`/`if_neg` rewrite of `.eq_def`. -/
def steinSub (a b : Nat) : Nat :=
  if min a (stripTwos b) = 0 then max a (stripTwos b)
  else if max a (stripTwos b) - min a (stripTwos b) = 0 then
    min a (stripTwos b)
  else
    steinSub (min a (stripTwos b))
      (max a (stripTwos b) - min a (stripTwos b))
termination_by a + b
decreasing_by
  have := stripTwos_le b
  omega

/-- The whole program: the trivial-input exits, then the three phases
reassembled — count the shared twos, run the subtract loop on the
stripped cores, shift the count back in. Value-identical to the Go
program on every input. -/
def steinSpec (a b : Nat) : Nat :=
  if a = 0 then b
  else if b = 0 then a
  else
    2 ^ commonTwos a b
      * steinSub (stripTwos (a / 2 ^ commonTwos a b))
          (b / 2 ^ commonTwos a b)

/-! ## Branch equations (the machine-correspondence proof consumes
these step by step) -/

/-- `commonTwos`, stepping branch. -/
theorem commonTwos_even (a b : Nat) (ha : a ≠ 0) (h2 : a % 2 = 0)
    (hb : b % 2 = 0) : commonTwos a b = commonTwos (a / 2) (b / 2) + 1 := by
  rw [commonTwos.eq_def, if_pos ⟨ha, h2, hb⟩]

/-- `commonTwos`, stop branch (general form). -/
theorem commonTwos_stop (a b : Nat)
    (h : ¬(a ≠ 0 ∧ a % 2 = 0 ∧ b % 2 = 0)) : commonTwos a b = 0 := by
  rw [commonTwos.eq_def, if_neg h]

/-- `commonTwos`, stop branch: first argument odd. -/
theorem commonTwos_odd_left (a b : Nat) (h : a % 2 = 1) :
    commonTwos a b = 0 :=
  commonTwos_stop a b (by omega)

/-- `commonTwos`, stop branch: second argument odd. -/
theorem commonTwos_odd_right (a b : Nat) (h : b % 2 = 1) :
    commonTwos a b = 0 :=
  commonTwos_stop a b (by omega)

/-- `stripTwos`, stepping branch. -/
theorem stripTwos_even (n : Nat) (h0 : n ≠ 0) (h2 : n % 2 = 0) :
    stripTwos n = stripTwos (n / 2) := by
  rw [stripTwos.eq_def, if_pos ⟨h0, h2⟩]

/-- `stripTwos`, stop branch (general form). -/
theorem stripTwos_stop (n : Nat) (h : ¬(n ≠ 0 ∧ n % 2 = 0)) :
    stripTwos n = n := by
  rw [stripTwos.eq_def, if_neg h]

/-- `stripTwos`, stop branch: zero. -/
theorem stripTwos_zero : stripTwos 0 = 0 :=
  stripTwos_stop 0 (by simp)

/-- `stripTwos`, stop branch: odd input. -/
theorem stripTwos_odd (n : Nat) (h : n % 2 = 1) : stripTwos n = n :=
  stripTwos_stop n (by omega)

/-- `steinSub`, `lo = 0` exit branch. -/
theorem steinSub_stop_zero (a b : Nat) (h : min a (stripTwos b) = 0) :
    steinSub a b = max a (stripTwos b) := by
  rw [steinSub.eq_def, if_pos h]

/-- `steinSub`, `hi - lo = 0` exit branch. -/
theorem steinSub_stop_eq (a b : Nat) (h0 : ¬min a (stripTwos b) = 0)
    (h : max a (stripTwos b) - min a (stripTwos b) = 0) :
    steinSub a b = min a (stripTwos b) := by
  rw [steinSub.eq_def, if_neg h0, if_pos h]

/-- `steinSub`, subtract-and-loop branch. -/
theorem steinSub_step (a b : Nat) (h0 : ¬min a (stripTwos b) = 0)
    (h : ¬max a (stripTwos b) - min a (stripTwos b) = 0) :
    steinSub a b
      = steinSub (min a (stripTwos b))
          (max a (stripTwos b) - min a (stripTwos b)) := by
  rw [steinSub.eq_def, if_neg h0, if_neg h]

/-! ## `stripTwos` support facts -/

/-- Stripping a nonzero value lands on an odd value. -/
theorem stripTwos_odd_result (n : Nat) (h : n ≠ 0) :
    stripTwos n % 2 = 1 := by
  by_cases h2 : n % 2 = 0
  · rw [stripTwos_even n h h2]
    exact stripTwos_odd_result (n / 2) (by omega)
  · rw [stripTwos_odd n (by omega)]
    omega
termination_by n
decreasing_by omega

/-- Stripping a nonzero value stays nonzero. -/
theorem stripTwos_ne_zero (n : Nat) (h : n ≠ 0) : stripTwos n ≠ 0 := by
  have := stripTwos_odd_result n h
  omega

/-! ## gcd support lemmas -/

/-- Divisors of odd numbers are odd. -/
theorem odd_of_dvd_odd {d a : Nat} (hdvd : d ∣ a) (ha : a % 2 = 1) :
    d % 2 = 1 := by
  obtain ⟨c, rfl⟩ := hdvd
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · exfalso
    rw [Nat.mul_mod, h] at ha
    simp at ha
  · exact h

/-- An odd divisor of `2 * m` divides `m`: `d` divides both `2 * m`
and `d * m`, hence their gcd `gcd 2 d * m = m` (`gcd 2 d = 1` for odd
`d` via `Nat.gcd_rec`). -/
theorem odd_dvd_of_dvd_two_mul {d m : Nat} (hd : d % 2 = 1)
    (h : d ∣ 2 * m) : d ∣ m := by
  have h1 : d ∣ Nat.gcd (2 * m) (d * m) := Nat.dvd_gcd h ⟨m, rfl⟩
  rw [Nat.gcd_mul_right 2 m d] at h1
  have h2 : Nat.gcd 2 d = 1 := by
    rw [Nat.gcd_rec 2 d, hd]
    exact Nat.gcd_one_left 2
  rwa [h2, Nat.one_mul] at h1

/-- One shared factor of two comes out of the gcd. -/
theorem gcd_two_two (a b : Nat) :
    Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b :=
  Nat.gcd_mul_left 2 a b

/-- Halving the even side of an odd/even pair preserves the gcd. -/
theorem gcd_odd_halve (a b : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) :
    Nat.gcd a (b / 2) = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left a (b / 2))
    exact Nat.dvd_trans (Nat.gcd_dvd_right a (b / 2)) ⟨2, by omega⟩
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left a b)
    apply odd_dvd_of_dvd_two_mul (odd_of_dvd_odd (Nat.gcd_dvd_left a b) ha)
    have h2 : 2 * (b / 2) = b := by omega
    rw [h2]
    exact Nat.gcd_dvd_right a b

/-- The subtract step preserves the gcd. -/
theorem gcd_sub (a b : Nat) (h : a ≤ b) :
    Nat.gcd a (b - a) = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left a (b - a))
    have hsum := Nat.dvd_add (Nat.gcd_dvd_right a (b - a))
      (Nat.gcd_dvd_left a (b - a))
    rwa [Nat.sub_add_cancel h] at hsum
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left a b)
      (Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b))

/-- Ordering the pair preserves the gcd. -/
theorem gcd_min_max (a b : Nat) :
    Nat.gcd (min a b) (max a b) = Nat.gcd a b := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right h, Nat.max_eq_left h, Nat.gcd_comm]

/-- Stripping twos beside an odd partner preserves the gcd (covers
`b = 0` via the stop branch: `stripTwos 0 = 0`). -/
theorem gcd_stripTwos (a b : Nat) (ha : a % 2 = 1) :
    Nat.gcd a (stripTwos b) = Nat.gcd a b := by
  by_cases h : b ≠ 0 ∧ b % 2 = 0
  · rw [stripTwos_even b h.1 h.2, gcd_stripTwos a (b / 2) ha,
      gcd_odd_halve a b ha h.2]
  · rw [stripTwos_stop b h]
termination_by b
decreasing_by omega

/-- Mirror of `gcd_stripTwos` for the first argument. -/
theorem gcd_stripTwos_left (a b : Nat) (hb : b % 2 = 1) :
    Nat.gcd (stripTwos a) b = Nat.gcd a b := by
  rw [Nat.gcd_comm (stripTwos a) b, gcd_stripTwos b a hb, Nat.gcd_comm b a]

/-! ## The subtract loop computes the gcd -/

/-- The SUBTRACT loop computes the gcd of its inputs, for odd `a` (the
loop is only ever entered on an odd core; `b` is unconstrained — the
`b = 0` and `b ≠ 0` entries both land right). Well-founded recursion
on `a + b`. -/
theorem steinSub_eq_gcd (a b : Nat) (ha : a % 2 = 1) :
    steinSub a b = Nat.gcd a b := by
  have hsle := stripTwos_le b
  by_cases hlo : min a (stripTwos b) = 0
  · -- `a` is odd hence ≥ 1, so the vanishing min forces `b = 0`
    have hs0 : stripTwos b = 0 := by omega
    have hb0 : b = 0 := by
      rcases Nat.eq_zero_or_pos b with h | hpos
      · exact h
      · exact absurd hs0 (stripTwos_ne_zero b (by omega))
    subst hb0
    rw [steinSub_stop_zero a 0 hlo, stripTwos_zero, Nat.gcd_zero_right]
    omega
  · have hs0 : stripTwos b ≠ 0 := by omega
    have hb0 : b ≠ 0 := by
      intro h
      subst h
      exact hs0 stripTwos_zero
    have hsodd : stripTwos b % 2 = 1 := stripTwos_odd_result b hb0
    have hg : Nat.gcd a (stripTwos b) = Nat.gcd a b := gcd_stripTwos a b ha
    by_cases hd : max a (stripTwos b) - min a (stripTwos b) = 0
    · -- equal cores: the loop returns them
      rw [steinSub_stop_eq a b hlo hd]
      have heq : a = stripTwos b := by omega
      rw [← hg, ← heq]
      simp [Nat.gcd_self]
    · -- subtract and recurse at the strictly smaller measure
      rw [steinSub_step a b hlo hd]
      have hlodd : min a (stripTwos b) % 2 = 1 := by omega
      rw [steinSub_eq_gcd (min a (stripTwos b))
          (max a (stripTwos b) - min a (stripTwos b)) hlodd,
        gcd_sub (min a (stripTwos b)) (max a (stripTwos b)) (by omega),
        gcd_min_max a (stripTwos b), hg]
termination_by a + b
decreasing_by omega

/-! ## The headline -/

/-- **Stein's algorithm computes the gcd**: the pure specification of
the Go program agrees with `Nat.gcd` on every input. Well-founded
recursion on `a + b` against `commonTwos`'s branches: in the both-even
branch one shared factor of two is peeled (`gcd_two_two`) and the
claim recurses at `(a / 2, b / 2)`; otherwise `commonTwos a b = 0` and
the subtract-loop theorem finishes through the odd side. -/
theorem steinSpec_eq_gcd (a b : Nat) : steinSpec a b = Nat.gcd a b := by
  by_cases ha : a = 0
  · subst ha
    simp [steinSpec]
  by_cases hb : b = 0
  · subst hb
    simp [steinSpec, ha]
  unfold steinSpec
  rw [if_neg ha, if_neg hb]
  by_cases hae : a % 2 = 0
  · by_cases hbe : b % 2 = 0
    · -- both even: peel one shared factor of two, recurse on the halves
      have h2a : ¬(a / 2 = 0) := by omega
      have h2b : ¬(b / 2 = 0) := by omega
      have hIH := steinSpec_eq_gcd (a / 2) (b / 2)
      unfold steinSpec at hIH
      rw [if_neg h2a, if_neg h2b] at hIH
      rw [commonTwos_even a b ha hae hbe]
      have hdiv : ∀ n : Nat,
          n / 2 ^ (commonTwos (a / 2) (b / 2) + 1)
            = n / 2 / 2 ^ commonTwos (a / 2) (b / 2) := by
        intro n
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ,
          Nat.mul_comm (2 ^ commonTwos (a / 2) (b / 2)) 2]
      rw [hdiv a, hdiv b, Nat.pow_succ,
        Nat.mul_comm (2 ^ commonTwos (a / 2) (b / 2)) 2, Nat.mul_assoc,
        hIH]
      have ha2 : 2 * (a / 2) = a := by omega
      have hb2 : 2 * (b / 2) = b := by omega
      rw [← gcd_two_two, ha2, hb2]
    · -- `a` even, `b` odd: no shared twos; strip `a`, pass the odd `b`
      rw [commonTwos_odd_right a b (by omega)]
      simp only [Nat.pow_zero, Nat.div_one, Nat.one_mul]
      rw [steinSub_eq_gcd (stripTwos a) b (stripTwos_odd_result a ha),
        gcd_stripTwos_left a b (by omega)]
  · -- `a` odd: no shared twos, stripping `a` is the identity
    rw [commonTwos_odd_left a b (by omega)]
    simp only [Nat.pow_zero, Nat.div_one, Nat.one_mul]
    rw [stripTwos_odd a (by omega)]
    exact steinSub_eq_gcd a b (by omega)
termination_by a + b
decreasing_by omega

end GoLean.Examples.Stein
