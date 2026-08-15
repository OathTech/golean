import GoLeanProofs.Examples.SieveProgram

/-!
# Sieve — Pure

The specification layer of the sieve example (Gallery Campaign G1, hard
lane). The spec is trial-division primality — `isPrime` and
`primeCount`, first-order functions a reader checks by eye; no Mathlib,
primality is built from scratch. Alongside them live the executable
mirrors of the program's three loops (`markFrom` / `sieveOuter` /
`countFrom`, recursion structure matching the Go loops one-for-one) and
the bridge theorems: the sieve table records exactly non-primality
(`sieveTable_spec`) and the counted answer is the prime count
(`sieveAnswer_eq`). Every well-founded definition ships isolated
equation lemmas (`*_step` / `*_stop`); consumers rewrite with those,
never by unfolding.
-/

namespace GoLean.Examples.Sieve

/-! ## The statement vocabulary: trial-division primality -/

/-- Trial-division primality: `2 ≤ k` and no divisor `d` with `2 ≤ d < k`. -/
def isPrime (k : Nat) : Bool :=
  decide (2 ≤ k) && (List.range k).all (fun d => decide (d < 2) || decide (k % d ≠ 0))

/-- The number of primes ≤ `n` — the obvious spec the headline states. -/
def primeCount (n : Nat) : Nat := ((List.range (n + 1)).filter isPrime).length

/-! ## The executable mirrors of the program's three loops -/

set_option linter.unusedVariables false in
/-- The inner marking loop's mirror: mark `j, j+i, j+2i, …` while `≤ n`.
(The named hypothesis `h` is part of the pinned recursion structure the
machine half mirrors; the unused-variable linter is silenced for it.) -/
def markFrom (n i : Nat) (B : List Bool) (j : Nat) : List Bool :=
  if h : j ≤ n ∧ 0 < i then markFrom n i (B.set j true) (j + i) else B
termination_by n + 1 - j
decreasing_by omega

/-- The outer loop's mirror: for `i` while `i*i ≤ n`, mark multiples of
unmarked `i`. -/
def sieveOuter (n : Nat) (B : List Bool) (i : Nat) : List Bool :=
  if h : i * i ≤ n ∧ 2 ≤ i then
    sieveOuter n (if B.getD i false then B else markFrom n i B (i * i)) (i + 1)
  else B
termination_by n + 1 - i
decreasing_by
  have hii : i * 1 ≤ i * i := Nat.mul_le_mul (Nat.le_refl i) (by omega)
  simp only [Nat.mul_one] at hii
  omega

/-- The whole sieve: a fresh `n+1`-entry table, outer loop from `2`. -/
def sieveTable (n : Nat) : List Bool := sieveOuter n (List.replicate (n + 1) false) 2

/-- The count loop's mirror: count `k` in `[i..n]` with
`B.getD k false = false`. -/
def countFrom (B : List Bool) (n i : Nat) : Nat :=
  if i ≤ n then (if B.getD i false then 0 else 1) + countFrom B n (i + 1) else 0
termination_by n + 1 - i
decreasing_by omega

/-- The program's answer: `0` below `2`, else the unmarked count over
`[2..n]`. -/
def sieveAnswer (n : Nat) : Nat := if n < 2 then 0 else countFrom (sieveTable n) n 2

/-! ## Equation lemmas (consumers rewrite with these, never unfold) -/

/-- `markFrom` steps: in range, set the slot and advance by `i`. -/
theorem markFrom_step (n i : Nat) (B : List Bool) (j : Nat) (hj : j ≤ n)
    (hi : 0 < i) : markFrom n i B j = markFrom n i (B.set j true) (j + i) := by
  rw [markFrom]; rw [dif_pos ⟨hj, hi⟩]

/-- `markFrom` stops past `n`. -/
theorem markFrom_stop (n i : Nat) (B : List Bool) (j : Nat) (hj : n < j) :
    markFrom n i B j = B := by
  rw [markFrom]; rw [dif_neg (by omega)]

/-- `sieveOuter` steps while `i * i ≤ n`. -/
theorem sieveOuter_step (n : Nat) (B : List Bool) (i : Nat) (h : i * i ≤ n)
    (hi : 2 ≤ i) :
    sieveOuter n B i
      = sieveOuter n (if B.getD i false then B else markFrom n i B (i * i)) (i + 1) := by
  rw [sieveOuter]; rw [dif_pos ⟨h, hi⟩]

/-- `sieveOuter` stops once `n < i * i`. -/
theorem sieveOuter_stop (n : Nat) (B : List Bool) (i : Nat) (h : n < i * i) :
    sieveOuter n B i = B := by
  rw [sieveOuter]; rw [dif_neg (by omega)]

/-- `countFrom` steps while `i ≤ n`. -/
theorem countFrom_step (B : List Bool) (n i : Nat) (h : i ≤ n) :
    countFrom B n i = (if B.getD i false then 0 else 1) + countFrom B n (i + 1) := by
  rw [countFrom]; rw [if_pos h]

/-- `countFrom` stops past `n`. -/
theorem countFrom_stop (B : List Bool) (n i : Nat) (h : n < i) :
    countFrom B n i = 0 := by
  rw [countFrom]; rw [if_neg (by omega)]

/-! ## Small arithmetic and list helpers -/

private theorem le_mul_self {i : Nat} (h : 1 ≤ i) : i ≤ i * i := by
  have := Nat.mul_le_mul (Nat.le_refl i) h
  simpa using this

private theorem mod_eq_zero_of_dvd {a b : Nat} (h : a ∣ b) : b % a = 0 := by
  obtain ⟨c, rfl⟩ := h
  exact Nat.mul_mod_right a c

private theorem getD_set_self {l : List Bool} {j : Nat} (h : j < l.length)
    (a : Bool) : (l.set j a).getD j false = a := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem getD_set_ne {l : List Bool} {j x : Nat} (h : j ≠ x) (a : Bool) :
    (l.set j a).getD x false = l.getD x false := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem getD_replicate {m x : Nat} :
    (List.replicate m false).getD x false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-! ## Length preservation -/

/-- Marking never changes the table length. -/
theorem markFrom_length (n i : Nat) (B : List Bool) (j : Nat) :
    (markFrom n i B j).length = B.length := by
  by_cases h : j ≤ n ∧ 0 < i
  · rw [markFrom_step n i B j h.1 h.2,
      markFrom_length n i (B.set j true) (j + i)]
    simp
  · rw [markFrom]; rw [dif_neg h]
termination_by n + 1 - j
decreasing_by omega

/-- The outer loop never changes the table length. -/
theorem sieveOuter_length (n : Nat) (B : List Bool) (i : Nat) :
    (sieveOuter n B i).length = B.length := by
  by_cases h : i * i ≤ n ∧ 2 ≤ i
  · rw [sieveOuter_step n B i h.1 h.2,
      sieveOuter_length n (if B.getD i false then B else markFrom n i B (i * i)) (i + 1)]
    split
    · rfl
    · exact markFrom_length n i B (i * i)
  · rw [sieveOuter]; rw [dif_neg h]
termination_by n + 1 - i
decreasing_by
  have hii : i * 1 ≤ i * i := Nat.mul_le_mul (Nat.le_refl i) (by omega)
  simp only [Nat.mul_one] at hii
  omega

/-- The sieve table has `n + 1` entries. -/
theorem sieveTable_length (n : Nat) : (sieveTable n).length = n + 1 := by
  rw [sieveTable, sieveOuter_length]
  simp

/-! ## Bounds -/

/-- The count over `[i..n]` is at most the window size. -/
theorem countFrom_le (B : List Bool) (n i : Nat) : countFrom B n i ≤ n + 1 - i := by
  by_cases h : i ≤ n
  · rw [countFrom_step B n i h]
    have ih := countFrom_le B n (i + 1)
    split <;> omega
  · rw [countFrom_stop B n i (by omega)]
    omega
termination_by n + 1 - i
decreasing_by omega

private theorem isPrime_zero : isPrime 0 = false := rfl

private theorem isPrime_one : isPrime 1 = false := rfl

/-- At most `n` primes are ≤ `n` (`0` is never prime). -/
theorem primeCount_le (n : Nat) : primeCount n ≤ n := by
  cases n with
  | zero => decide
  | succ m =>
    unfold primeCount
    rw [List.range_eq_range', List.range'_succ, List.filter_cons, isPrime_zero]
    simp only [Bool.false_eq_true, if_false]
    calc (List.filter isPrime (List.range' 1 (m + 1))).length
        ≤ (List.range' 1 (m + 1)).length := List.length_filter_le _ _
      _ = m + 1 := by simp

/-! ## Primality facts, from scratch (no Mathlib in this build) -/

/-- Unfolding `isPrime` to its arithmetic content. -/
theorem isPrime_iff (k : Nat) :
    isPrime k = true ↔ 2 ≤ k ∧ ∀ d, 2 ≤ d → d < k → k % d ≠ 0 := by
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun d hd2 hdk hmod => ?_⟩
    rcases hall d hdk with h | h
    · omega
    · exact h hmod
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun d hdk => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · exact Or.inr (hall d (by omega) hdk)

/-- A non-prime `k ≥ 2` has a divisor `d` with `2 ≤ d < k`. -/
private theorem exists_divisor_of_not_prime {k : Nat} (h2 : 2 ≤ k)
    (h : isPrime k = false) : ∃ d, 2 ≤ d ∧ d < k ∧ k % d = 0 := by
  have hnot : ¬(2 ≤ k ∧ ∀ d, 2 ≤ d → d < k → k % d ≠ 0) := by
    rw [← isPrime_iff, h]; simp
  have hnall : ¬∀ d, 2 ≤ d → d < k → k % d ≠ 0 := fun hall => hnot ⟨h2, hall⟩
  obtain ⟨d, hd⟩ := Classical.not_forall.mp hnall
  refine ⟨d, ?_⟩
  by_cases h1 : 2 ≤ d
  · by_cases hlt : d < k
    · by_cases hm : k % d = 0
      · exact ⟨h1, hlt, hm⟩
      · exact absurd (fun _ _ => hm) hd
    · exact absurd (fun _ hlt' => absurd hlt' hlt) hd
  · exact absurd (fun h1' => absurd h1' h1) hd

/-- Every `k ≥ 2` has a prime factor. -/
theorem exists_prime_factor (k : Nat) (h2 : 2 ≤ k) :
    ∃ p, isPrime p = true ∧ p ∣ k ∧ p ≤ k := by
  by_cases hp : isPrime k = true
  · exact ⟨k, hp, Nat.dvd_refl k, Nat.le_refl k⟩
  · have hp' : isPrime k = false := by
      cases hpk : isPrime k
      · rfl
      · exact absurd hpk hp
    obtain ⟨d, hd2, hdk, hmod⟩ := exists_divisor_of_not_prime h2 hp'
    obtain ⟨p, hpp, hpd, hple⟩ := exists_prime_factor d hd2
    exact ⟨p, hpp, Nat.dvd_trans hpd (Nat.dvd_of_mod_eq_zero hmod), by omega⟩
termination_by k
decreasing_by omega

/-- A composite `k ≥ 2` has a prime factor `p` with `p * p ≤ k` — the fact
that makes stopping the outer loop at `i * i ≤ n` sound. -/
theorem exists_small_prime_factor (k : Nat) (h2 : 2 ≤ k)
    (h : isPrime k = false) : ∃ p, isPrime p = true ∧ p ∣ k ∧ p * p ≤ k := by
  obtain ⟨d, hd2, hdk, hmod⟩ := exists_divisor_of_not_prime h2 h
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc; omega
    · simp at hc; omega
    · omega
  by_cases hdc : d ≤ c
  · obtain ⟨p, hpp, hpd, hple⟩ := exists_prime_factor d hd2
    refine ⟨p, hpp, Nat.dvd_trans hpd ⟨c, hc⟩, ?_⟩
    calc p * p ≤ d * d := Nat.mul_le_mul hple hple
      _ ≤ d * c := Nat.mul_le_mul (Nat.le_refl d) hdc
      _ = k := hc.symm
  · have hcdvd : c ∣ k := ⟨d, by rw [hc, Nat.mul_comm]⟩
    obtain ⟨p, hpp, hpc, hple⟩ := exists_prime_factor c hc2
    refine ⟨p, hpp, Nat.dvd_trans hpc hcdvd, ?_⟩
    calc p * p ≤ c * c := Nat.mul_le_mul hple hple
      _ ≤ d * c := Nat.mul_le_mul (by omega) (Nat.le_refl c)
      _ = k := hc.symm

/-- A prime square-divisor witness makes `x` composite (the prime is a
proper divisor). -/
theorem isPrime_eq_false_of_factor {p x : Nat} (hp : isPrime p = true)
    (hdvd : p ∣ x) (hsq : p * p ≤ x) : isPrime x = false := by
  have hp2 : 2 ≤ p := ((isPrime_iff p).mp hp).1
  have h4 : 4 ≤ x := by
    have : 2 * 2 ≤ p * p := Nat.mul_le_mul hp2 hp2
    omega
  have hmod : x % p = 0 := mod_eq_zero_of_dvd hdvd
  have hpx : p < x := by
    have hple : p ≤ x := Nat.le_of_dvd (by omega) hdvd
    rcases Nat.lt_or_ge p x with h | h
    · exact h
    · exfalso
      have hpe : p = x := Nat.le_antisymm hple h
      have hsq' : p * p = x * x := by rw [hpe]
      have h2x : 2 * x ≤ x * x := Nat.mul_le_mul (by omega) (Nat.le_refl x)
      omega
  cases hx : isPrime x
  · rfl
  · exact absurd hmod (((isPrime_iff x).mp hx).2 p hp2 hpx)

/-! ## The marking characterization -/

/-- What `markFrom` writes: an in-range slot `x` ends marked iff it was
already marked or is one of `j, j+i, j+2i, …` up to `n`. The `j ≤ x`
conjunct is load-bearing: `x - j` is truncated subtraction, so it alone
rules out `x < j`. -/
theorem markFrom_getD (n i : Nat) (B : List Bool) (j x : Nat) (hi : 0 < i)
    (hx : x < B.length) :
    (markFrom n i B j).getD x false
      = (B.getD x false || decide (j ≤ x ∧ x ≤ n ∧ (x - j) % i = 0)) := by
  by_cases hj : j ≤ n
  · rw [markFrom_step n i B j hj hi,
      markFrom_getD n i (B.set j true) (j + i) x hi (by simpa using hx)]
    by_cases hxj : x = j
    · subst hxj
      rw [getD_set_self hx]
      have hcond : decide (x ≤ x ∧ x ≤ n ∧ (x - x) % i = 0) = true :=
        decide_eq_true ⟨Nat.le_refl x, hj, by simp⟩
      rw [hcond]
      simp
    · rw [getD_set_ne (fun hc => hxj hc.symm)]
      congr 1
      rw [decide_eq_decide]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, ?_⟩
        rw [show x - j = (x - (j + i)) + i by omega, Nat.add_mod_right]
        exact h3
      · rintro ⟨h1, h2, h3⟩
        have hdvd : i ∣ x - j := Nat.dvd_of_mod_eq_zero h3
        have hpos : 0 < x - j := by omega
        have hile : i ≤ x - j := Nat.le_of_dvd hpos hdvd
        refine ⟨by omega, h2, ?_⟩
        have hsub : i ∣ (x - j) - i := Nat.dvd_sub hdvd (Nat.dvd_refl i)
        rw [show x - (j + i) = (x - j) - i by omega]
        exact mod_eq_zero_of_dvd hsub
  · rw [markFrom_stop n i B j (by omega)]
    have hcond : ¬(j ≤ x ∧ x ≤ n ∧ (x - j) % i = 0) := by
      rintro ⟨h1, h2, _⟩; omega
    simp [hcond]
termination_by n + 1 - j
decreasing_by omega

/-! ## The outer-loop invariant -/

/-- The outer loop's invariant: the table has `n + 1` slots, and a slot
`x ≤ n` is marked iff some already-processed prime `p < i` divides `x`
with `p * p ≤ x`. -/
private def Inv (n : Nat) (B : List Bool) (i : Nat) : Prop :=
  B.length = n + 1 ∧
    ∀ x, x ≤ n →
      (B.getD x false = true ↔ ∃ p, isPrime p = true ∧ p < i ∧ p ∣ x ∧ p * p ≤ x)

private theorem inv_init (n : Nat) : Inv n (List.replicate (n + 1) false) 2 := by
  refine ⟨by simp, fun x hx => ?_⟩
  rw [getD_replicate]
  constructor
  · intro h; simp at h
  · rintro ⟨p, hpp, hp2, _, _⟩
    have := ((isPrime_iff p).mp hpp).1
    exfalso; omega

private theorem inv_step {n : Nat} {B : List Bool} {i : Nat} (h2i : 2 ≤ i)
    (hle : i * i ≤ n) (hinv : Inv n B i) :
    Inv n (if B.getD i false then B else markFrom n i B (i * i)) (i + 1) := by
  obtain ⟨hlen, hB⟩ := hinv
  have hin : i ≤ n := Nat.le_trans (le_mul_self (by omega)) hle
  by_cases hmk : B.getD i false = true
  · rw [if_pos hmk]
    refine ⟨hlen, fun x hx => ?_⟩
    rw [hB x hx]
    constructor
    · rintro ⟨p, hpp, hpi, hpd, hppx⟩
      exact ⟨p, hpp, by omega, hpd, hppx⟩
    · rintro ⟨p, hpp, hpi, hpd, hppx⟩
      by_cases hpi' : p < i
      · exact ⟨p, hpp, hpi', hpd, hppx⟩
      · have hpe : p = i := by omega
        obtain ⟨q, hqp, hqi, hqd, hqq⟩ := (hB i hin).mp hmk
        refine ⟨q, hqp, hqi, Nat.dvd_trans hqd (hpe ▸ hpd), ?_⟩
        have hii : i ≤ i * i := le_mul_self (by omega)
        have hsq : p * p = i * i := by rw [hpe]
        omega
  · rw [if_neg hmk]
    have hmk' : B.getD i false = false := by
      cases h : B.getD i false
      · rfl
      · exact absurd h hmk
    have hip : isPrime i = true := by
      cases hnp : isPrime i
      · exfalso
        obtain ⟨p, hpp, hpd, hppi⟩ := exists_small_prime_factor i h2i hnp
        have hp2 : 2 ≤ p := ((isPrime_iff p).mp hpp).1
        have hpl : p ≤ p * p := le_mul_self (by omega)
        have hpi : p < i := by
          rcases Nat.lt_or_ge p i with h | h
          · exact h
          · exfalso
            have hpe : p = i := by omega
            have hsq : p * p = i * i := by rw [hpe]
            have h2p : 2 * i ≤ i * i := Nat.mul_le_mul h2i (Nat.le_refl i)
            omega
        have hmark := (hB i hin).mpr ⟨p, hpp, hpi, hpd, hppi⟩
        rw [hmk'] at hmark
        exact Bool.noConfusion hmark
      · rfl
    refine ⟨by rw [markFrom_length]; exact hlen, fun x hx => ?_⟩
    rw [markFrom_getD n i B (i * i) x (by omega) (by omega)]
    rw [Bool.or_eq_true, decide_eq_true_eq, hB x hx]
    constructor
    · rintro (⟨p, hpp, hpi, hpd, hppx⟩ | ⟨hix, hxn, hmod⟩)
      · exact ⟨p, hpp, by omega, hpd, hppx⟩
      · have hdvd : i ∣ x := by
          have h1 : i ∣ x - i * i := Nat.dvd_of_mod_eq_zero hmod
          have h2 : i ∣ i * i := Nat.dvd_mul_left i i
          have h3 := Nat.dvd_add h1 h2
          rwa [Nat.sub_add_cancel hix] at h3
        exact ⟨i, hip, by omega, hdvd, hix⟩
    · rintro ⟨p, hpp, hpi, hpd, hppx⟩
      by_cases hpi' : p < i
      · exact Or.inl ⟨p, hpp, hpi', hpd, hppx⟩
      · have hpe : p = i := by omega
        have hsq : p * p = i * i := by rw [hpe]
        have hpd' : i ∣ x := hpe ▸ hpd
        refine Or.inr ⟨by omega, hx, ?_⟩
        exact mod_eq_zero_of_dvd (Nat.dvd_sub hpd' (Nat.dvd_mul_left i i))

private theorem sieveOuter_marks (n : Nat) (B : List Bool) (i : Nat)
    (h2i : 2 ≤ i) (hinv : Inv n B i) (x : Nat) (hx : x ≤ n) :
    ((sieveOuter n B i).getD x false = true)
      ↔ ∃ p, isPrime p = true ∧ p ∣ x ∧ p * p ≤ x := by
  by_cases hc : i * i ≤ n
  · rw [sieveOuter_step n B i hc h2i]
    exact sieveOuter_marks n _ (i + 1) (by omega) (inv_step h2i hc hinv) x hx
  · rw [sieveOuter_stop n B i (by omega)]
    rw [hinv.2 x hx]
    constructor
    · rintro ⟨p, hpp, _, hpd, hppx⟩
      exact ⟨p, hpp, hpd, hppx⟩
    · rintro ⟨p, hpp, hpd, hppx⟩
      refine ⟨p, hpp, ?_, hpd, hppx⟩
      rcases Nat.lt_or_ge p i with hlt | hge
      · exact hlt
      · exfalso
        have h2 : i * i ≤ p * p := Nat.mul_le_mul hge hge
        omega
termination_by n + 1 - i
decreasing_by
  have hii : i * 1 ≤ i * i := Nat.mul_le_mul (Nat.le_refl i) (by omega)
  simp only [Nat.mul_one] at hii
  omega

/-! ## The correctness core -/

/-- **The sieve computes primality**: for `2 ≤ k ≤ n`, slot `k` of the
finished table is marked exactly when `k` is composite. -/
theorem sieveTable_spec (n k : Nat) (h2 : 2 ≤ k) (hk : k ≤ n) :
    (sieveTable n).getD k false = !isPrime k := by
  have h : (sieveTable n).getD k false = true
      ↔ ∃ p, isPrime p = true ∧ p ∣ k ∧ p * p ≤ k := by
    unfold sieveTable
    exact sieveOuter_marks n _ 2 (Nat.le_refl 2) (inv_init n) k hk
  cases hp : isPrime k
  · rw [Bool.not_false]
    exact h.mpr (exists_small_prime_factor k h2 hp)
  · rw [Bool.not_true]
    cases hg : (sieveTable n).getD k false
    · rfl
    · exfalso
      obtain ⟨p, hpp, hpd, hppk⟩ := h.mp hg
      have hfalse := isPrime_eq_false_of_factor hpp hpd hppk
      rw [hp] at hfalse
      exact Bool.noConfusion hfalse

/-! ## The counting bridge -/

/-- `countFrom` counts exactly the unmarked slots of the window `[i..n]`. -/
theorem countFrom_eq (B : List Bool) (n i : Nat) :
    countFrom B n i
      = ((List.range' i (n + 1 - i)).filter (fun x => !B.getD x false)).length := by
  by_cases h : i ≤ n
  · rw [countFrom_step B n i h]
    have hrec := countFrom_eq B n (i + 1)
    rw [show n + 1 - i = (n + 1 - (i + 1)) + 1 by omega, List.range'_succ,
      List.filter_cons]
    cases hB : B.getD i false
    · simp [hrec] <;> omega
    · simp [hrec] <;> omega
  · rw [countFrom_stop B n i (by omega), show n + 1 - i = 0 by omega]
    rfl
termination_by n + 1 - i
decreasing_by omega

/-- **The headline bridge**: the program's answer is the prime count. -/
theorem sieveAnswer_eq (n : Nat) : sieveAnswer n = primeCount n := by
  by_cases hn : n < 2
  · unfold sieveAnswer
    rw [if_pos hn]
    have h01 : n = 0 ∨ n = 1 := by omega
    rcases h01 with rfl | rfl <;> rfl
  · unfold sieveAnswer
    rw [if_neg hn, countFrom_eq, show n + 1 - 2 = n - 1 by omega]
    have hcong :
        List.filter (fun x => !(sieveTable n).getD x false) (List.range' 2 (n - 1))
          = List.filter isPrime (List.range' 2 (n - 1)) := by
      apply List.filter_congr
      intro x hx
      have hmem : 2 ≤ x ∧ x < 2 + (n - 1) := by
        simpa [List.mem_range'_1] using hx
      rw [sieveTable_spec n x hmem.1 (by omega), Bool.not_not]
    rw [hcong]
    unfold primeCount
    have hdecomp : List.range (n + 1) = 0 :: 1 :: List.range' 2 (n - 1) := by
      rw [List.range_eq_range', show n + 1 = (n - 1) + 1 + 1 by omega,
        List.range'_succ, List.range'_succ]
    rw [hdecomp, List.filter_cons, List.filter_cons, isPrime_zero, isPrime_one]
    simp

end GoLean.Examples.Sieve
