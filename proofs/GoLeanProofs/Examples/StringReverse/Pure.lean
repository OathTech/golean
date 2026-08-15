import GoLeanProofs.SliceMem

/-!
# StringReverse — Pure

The example's entire mathematical content, at the type the machine
actually observes: `List UInt8`, the BYTES of a Go string. Three
statement-vocabulary pieces reach the headline:

* `palinSpec` — `1` when the byte list reads the same both ways,
  `0` otherwise (the `isStringPalindrome` verdict);
* `List.reverse` — the `reverseString` postcondition is just
  `post = pre.reverse`, with no function of ours in the way;
* the family `strFamily n seed` — the bytes `buildStr` produces —
  which is PROOF vocabulary only (the ∃-witness), never part of the
  claim.

Everything else is proof method: the prefix lemma the build loop's
invariant consumes (`strFamily_succ`), the suffix-reversal invariant
of the reverse loop (`revPre`), and the half-scan characterisation
`palin_iff_half` — the same theorem `ArrayPalindrome.palin_iff_half`
proves one type over (`List Int`), re-derived here at `List UInt8`
because examples do not import each other.
-- KIT-GAP WITNESS (see .tmp/kitgaps-strrev.md): the half-scan bridge
-- is type-generic and belongs in a kit module at `List α`.
-/

namespace GoLean.Examples.StringReverse

open GoLean

set_option maxRecDepth 1000000

/-! ## The specification function -/

/-- **The specification**: `1` when the byte list reads the same
forwards and backwards, `0` otherwise — defined the way a
mathematician would write it (`xs.reverse = xs`), with no index
arithmetic anywhere in the statement. -/
def palinSpec (xs : List UInt8) : Int :=
  if xs.reverse = xs then 1 else 0

theorem palinSpec_eq_one {xs : List UInt8} (h : xs.reverse = xs) :
    palinSpec xs = 1 := by
  simp [palinSpec, h]

theorem palinSpec_eq_zero {xs : List UInt8} (h : ¬ xs.reverse = xs) :
    palinSpec xs = 0 := by
  simp [palinSpec, h]

/-- The verdict is a machine integer. -/
theorem palinSpec_range (xs : List UInt8) :
    0 ≤ palinSpec xs ∧ palinSpec xs < 2 ^ 64 := by
  rw [palinSpec]; split <;> omega

/-! ## The build family

`buildStr` computes `out += string(rune(97 + (seed+i)%26))` at uint64
arguments, so the byte at position `i` is `97 + ((seed+i) mod 2^64)
mod 26` — the inner wrap is Go's own uint64 addition, kept HONESTLY
(for `seed + i ≥ 2^64` the wrap changes the letter, and the family
says so rather than pretending `%` distributes). -/

/-- The byte value at position `i` (a `Nat` in `97…122`). -/
def strByte (seed i : Nat) : Nat :=
  97 + ((seed + i) % 2 ^ 64) % 26

/-- The bytes `buildStr n seed` produces. -/
def strFamily (n seed : Nat) : List UInt8 :=
  (List.range n).map (fun i => UInt8.ofNat (strByte seed i))

theorem strByte_lt (seed i : Nat) : strByte seed i < 128 := by
  have : ((seed + i) % 2 ^ 64) % 26 < 26 := Nat.mod_lt _ (by omega)
  unfold strByte
  omega

theorem strFamily_length (n seed : Nat) :
    (strFamily n seed).length = n := by
  simp [strFamily]

theorem strFamily_zero (seed : Nat) : strFamily 0 seed = [] := rfl

/-- The prefix step the build loop's invariant consumes. -/
theorem strFamily_succ (n seed : Nat) :
    strFamily (n + 1) seed
      = strFamily n seed ++ [UInt8.ofNat (strByte seed n)] := by
  simp [strFamily, List.range_succ]

/-- Every family byte is ASCII (`< 128`) — what lets `string(rune(b))`
in `reverseString` emit ONE byte back. UTF-8 is modeled faithfully by
the machine (a byte `≥ 128` would come back as a two-byte encoding),
so the reverse loop's invariant carries exactly this fact. -/
theorem strFamily_ascii {n seed : Nat} :
    ∀ b ∈ strFamily n seed, b.toNat < 128 := by
  intro b hb
  simp only [strFamily, List.mem_map] at hb
  obtain ⟨i, _, rfl⟩ := hb
  have h := strByte_lt seed i
  have : (UInt8.ofNat (strByte seed i)).toNat = strByte seed i % 256 := by
    simp
  omega

/-! ## The reverse loop's invariant

`reverseString` walks `i` DOWN from `len-1`, appending `s[i]`; after
`m` iterations the accumulator holds the reversal of the LAST `m`
bytes. -/

/-- The accumulator after `m` reverse iterations. -/
def revPre (l : List UInt8) (m : Nat) : List UInt8 :=
  (l.drop (l.length - m)).reverse

theorem revPre_zero (l : List UInt8) : revPre l 0 = [] := by
  simp [revPre]

theorem revPre_full (l : List UInt8) : revPre l l.length = l.reverse := by
  simp [revPre]

/-- One reverse step: appending `l[len-1-m]` extends the reversed
suffix by one. -/
theorem revPre_succ {l : List UInt8} {m : Nat} (hm : m < l.length) :
    revPre l (m + 1) = revPre l m ++ [l.getD (l.length - 1 - m) 0] := by
  have hidx : l.length - (m + 1) < l.length := by omega
  have hdrop : l.drop (l.length - (m + 1))
      = l[l.length - (m + 1)] :: l.drop (l.length - (m + 1) + 1) :=
    List.drop_eq_getElem_cons hidx
  have hsucc : l.length - (m + 1) + 1 = l.length - m := by omega
  have hgd : l.getD (l.length - 1 - m) 0 = l[l.length - (m + 1)] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by omega : l.length - 1 - m < l.length)]
    simp only [Option.getD_some]
    congr 1
    omega
  rw [revPre, hdrop, hsucc, List.reverse_cons, hgd]
  rfl

/-! ## The half-scan characterisation

The palindrome loop inspects exactly the pairs `(t, len-1-t)` for
`t < len/2`; `palin_iff_half` is the theorem that this is enough —
`ArrayPalindrome.palin_iff_half` one type over. -/

/-- The half-scan predicate: every pair the loop has checked up to `m`
matched. -/
def PalinUpTo (xs : List UInt8) (m : Nat) : Prop :=
  ∀ t : Nat, t < m → xs.getD t 0 = xs.getD (xs.length - 1 - t) 0

theorem palinUpTo_zero (xs : List UInt8) : PalinUpTo xs 0 := by
  intro t ht; omega

theorem palinUpTo_succ {xs : List UInt8} {m : Nat} (h : PalinUpTo xs m)
    (hm : xs.getD m 0 = xs.getD (xs.length - 1 - m) 0) :
    PalinUpTo xs (m + 1) := by
  intro t ht
  rcases Nat.lt_or_ge t m with hlt | hge
  · exact h t hlt
  · have : t = m := by omega
    subst this; exact hm

/-- Indexing a list's reverse, in the `getD` spelling the machine
segments produce. -/
theorem getD_reverse (xs : List UInt8) {t : Nat} (ht : t < xs.length) :
    xs.reverse.getD t 0 = xs.getD (xs.length - 1 - t) 0 := by
  have h1 : t < xs.reverse.length := by rw [List.length_reverse]; omega
  have h2 : xs.length - 1 - t < xs.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    List.getElem_reverse]

/-- **The bridge**: scanning the first half is enough. -/
theorem palin_iff_half (xs : List UInt8) :
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
          rw [show xs.length - 1 - (xs.length - 1 - t) = t from by omega]
            at this
          exact this
        · -- the odd middle: `t` is its own mirror
          have : xs.length - 1 - t = t := by omega
          rw [this]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at hgoal
    exact hgoal

/-- The loop-exit reading: the full half scan certifies a palindrome. -/
theorem palinSpec_of_full {xs : List UInt8}
    (h : PalinUpTo xs (xs.length / 2)) : palinSpec xs = 1 :=
  palinSpec_eq_one ((palin_iff_half xs).mpr h)

/-- The early-return reading: ONE mismatched pair refutes it. -/
theorem palinSpec_of_mismatch {xs : List UInt8} {m : Nat}
    (hm : m < xs.length)
    (h : xs.getD m 0 ≠ xs.getD (xs.length - 1 - m) 0) :
    palinSpec xs = 0 := by
  refine palinSpec_eq_zero (fun hrev => h ?_)
  rw [← getD_reverse xs hm, hrev]

/-- `getD` of an in-range index is a member — `SliceMem.getD_mem` one
type over (that kit lemma is fixed at `List Int`).
-- KIT-GAP WITNESS (see .tmp/kitgaps-strrev.md) -/
theorem getD_mem_u8 {xs : List UInt8} {k : Nat} (hk : k < xs.length) :
    xs.getD k 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

/-! ## The `!=` verdict bridge

The machine compares the two bytes as `Int`s (`.int ↑b.toNat .uint8`),
so the loop lemmas need the boolean at that spelling. -/

theorem byteInt_beq_of_eq {a b : UInt8} (h : a = b) :
    ((a.toNat : Int) == (b.toNat : Int)) = true := by
  subst h; simp

theorem byteInt_beq_of_ne {a b : UInt8} (h : a ≠ b) :
    ((a.toNat : Int) == (b.toNat : Int)) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_inj]
  exact fun hn => h (UInt8.toNat_inj.mp hn)

end GoLean.Examples.StringReverse
