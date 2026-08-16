/-!
# WordFreq — Pure

The `wordfreq` example's entire mathematical content, at the type the
machine actually observes: `List UInt8`, the BYTES of a Go string
(`GoString` wraps `Array UInt8`; the proofs speak lists). Three
statement-vocabulary pieces reach the headline:

* `wordsOf` — THE `strings.Fields` specification: the maximal
  separator-free chunks of the byte list, scanning left to right,
  where a separator is any member of the full Unicode White_Space
  class as UTF-8 byte patterns (`sepWidth`, exactly the injected shim
  `goleanShimStringsFields`'s class — see
  `tools/nativefrontend/stdlibshim.go`);
* `multiplicity` / `maxMultiplicity` — the queried word's count and
  the maximum count over all words (`WordCount`'s statement functions,
  one key type over: `List UInt8` words instead of `Int`s);
* the family `textFamily n seed` / `qWord qsel` — the bytes
  `buildText`/the query build produce — which is PROOF vocabulary only
  (the ∃-witness), never part of the claim.

Everything else is proof method: the byte-granularity step equations
of the `wordsOfCarry` scan (the machine loop's invariant drives on
these), the family-split bridge `wordsOf_textFamily`, and the counting
fold `bumpW`/`countsFoldW` — `GoLeanProofs.MapMem`'s count layer
mirrored one key type over.

Conformance: the `#guard`s at the bottom pin `wordsOf` against the
go-run-confirmed splits of
`Corpus/coverage/exec/strings/fields-conformance/cases.tsv` (all 8
rows), byte-exactly.
-/

namespace GoLean.Examples.WordFreq

set_option maxRecDepth 1000000

/-! ## The separator class

`sepWidth l` is the width in bytes of the white-space separator at the
HEAD of `l` (`0` = the head starts no separator). EXACTLY the shim's
class — the full Unicode White_Space set as UTF-8 byte patterns:

* 1 byte : `20` (space), `09`–`0D` (TAB LF VT FF CR);
* 2 bytes: `C2 85` (U+0085 NEL), `C2 A0` (U+00A0 NBSP);
* 3 bytes: `E1 9A 80` (U+1680); `E2 80 80`–`8A` (U+2000–200A);
  `E2 80 A8`/`A9` (U+2028/2029); `E2 80 AF` (U+202F);
  `E2 81 9F` (U+205F); `E3 80 80` (U+3000).

A multi-byte pattern only fires when ALL its bytes are present — a
truncated prefix at end of input (e.g. a trailing `E2 80`) is field
content, exactly the shim's `i+1 < len(s)` / `i+2 < len(s)` guards. -/
def sepWidth : List UInt8 → Nat
  | [] => 0
  | [c] =>
      if c.toNat = 32 ∨ (9 ≤ c.toNat ∧ c.toNat ≤ 13) then 1 else 0
  | [c, c1] =>
      if c.toNat = 32 ∨ (9 ≤ c.toNat ∧ c.toNat ≤ 13) then 1
      else if c.toNat = 0xC2 ∧ (c1.toNat = 0x85 ∨ c1.toNat = 0xA0) then 2
      else 0
  | c :: c1 :: c2 :: _ =>
      if c.toNat = 32 ∨ (9 ≤ c.toNat ∧ c.toNat ≤ 13) then 1
      else if c.toNat = 0xC2 ∧ (c1.toNat = 0x85 ∨ c1.toNat = 0xA0) then 2
      else if (c.toNat = 0xE1 ∧ c1.toNat = 0x9A ∧ c2.toNat = 0x80)
          ∨ (c.toNat = 0xE2 ∧ c1.toNat = 0x80 ∧
              ((0x80 ≤ c2.toNat ∧ c2.toNat ≤ 0x8A)
                ∨ c2.toNat = 0xA8 ∨ c2.toNat = 0xA9 ∨ c2.toNat = 0xAF))
          ∨ (c.toNat = 0xE2 ∧ c1.toNat = 0x81 ∧ c2.toNat = 0x9F)
          ∨ (c.toNat = 0xE3 ∧ c1.toNat = 0x80 ∧ c2.toNat = 0x80) then 3
      else 0

theorem sepWidth_nil : sepWidth [] = 0 := rfl

/-- A 1-byte white-space head is a width-1 separator REGARDLESS of
what follows (the first pattern wins) — this is why a two-space
separator is two 1-byte steps. -/
theorem sepWidth_ws1 {c : UInt8}
    (h : c.toNat = 32 ∨ (9 ≤ c.toNat ∧ c.toNat ≤ 13)) (r : List UInt8) :
    sepWidth (c :: r) = 1 := by
  rcases r with _ | ⟨c1, r⟩
  · simp only [sepWidth]; rw [if_pos h]
  · rcases r with _ | ⟨c2, r⟩
    · simp only [sepWidth]; rw [if_pos h]
    · simp only [sepWidth]; rw [if_pos h]

theorem sepWidth_space (r : List UInt8) : sepWidth (32 :: r) = 1 :=
  sepWidth_ws1 (Or.inl (by decide)) r

theorem sepWidth_tab (r : List UInt8) : sepWidth (9 :: r) = 1 :=
  sepWidth_ws1 (Or.inr (by decide)) r

/-- A letter head starts no separator: every separator head byte is
`9`–`13`, `32`, `C2`, `E1`, `E2` or `E3`, and `97 ≤ c ≤ 122` excludes
them all. -/
theorem sepWidth_letter {c : UInt8}
    (h1 : 97 ≤ c.toNat) (h2 : c.toNat ≤ 122) (r : List UInt8) :
    sepWidth (c :: r) = 0 := by
  rcases r with _ | ⟨c1, r⟩
  · simp only [sepWidth]; rw [if_neg (by omega)]
  · rcases r with _ | ⟨c2, r⟩
    · simp only [sepWidth]; rw [if_neg (by omega), if_neg (by omega)]
    · simp only [sepWidth]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## The Fields scan

`wordsOfCarry l carry` scans `l` left to right with `carry` the OPEN
field (the shim's `s[start:i]`): at a separator head it consumes
`sepWidth l` bytes and closes the open field (if any); at any other
byte it moves that byte into the carry. `wordsOf` is the scan from an
empty carry — THE `strings.Fields` spec. -/

def wordsOfCarry : List UInt8 → List UInt8 → List (List UInt8)
  | [], carry => if carry = [] then [] else [carry]
  | c :: rest, carry =>
      if _h : 0 < sepWidth (c :: rest) then
        if carry = [] then
          wordsOfCarry ((c :: rest).drop (sepWidth (c :: rest))) []
        else
          carry :: wordsOfCarry ((c :: rest).drop (sepWidth (c :: rest))) []
      else
        wordsOfCarry rest (carry ++ [c])
termination_by l _ => l.length
decreasing_by
  all_goals simp only [List.length_drop, List.length_cons]
  all_goals omega

/-- **THE Fields spec**: the maximal separator-free chunks of `l`. -/
def wordsOf (l : List UInt8) : List (List UInt8) :=
  wordsOfCarry l []

/-! ### The step equations (the machine loop's invariant drives on
these — byte granularity, one per byte class × carry state) -/

/-- Exhausted input, no open field: no more words. -/
theorem wordsOfCarry_nil_nil : wordsOfCarry [] [] = [] := by
  simp [wordsOfCarry]

/-- Exhausted input closes the open field (the shim's trailing
`if inField` append). -/
theorem wordsOfCarry_nil_ne {carry : List UInt8} (hc : carry ≠ []) :
    wordsOfCarry [] carry = [carry] := by
  simp only [wordsOfCarry]
  rw [if_neg hc]

/-- The letter step: a non-separator byte joins the open field. -/
theorem wordsOfCarry_letter {c : UInt8} {rest carry : List UInt8}
    (h : sepWidth (c :: rest) = 0) :
    wordsOfCarry (c :: rest) carry = wordsOfCarry rest (carry ++ [c]) := by
  simp only [wordsOfCarry]
  rw [dif_neg (by omega)]

/-- The separator step at an empty carry: consume the separator,
emit nothing. -/
theorem wordsOfCarry_sep_nil {c : UInt8} {rest : List UInt8}
    (h : 0 < sepWidth (c :: rest)) :
    wordsOfCarry (c :: rest) []
      = wordsOfCarry ((c :: rest).drop (sepWidth (c :: rest))) [] := by
  simp only [wordsOfCarry]
  rw [dif_pos h]
  simp

/-- The separator step at a nonempty carry: the open field closes. -/
theorem wordsOfCarry_sep_cons {c : UInt8} {rest carry : List UInt8}
    (h : 0 < sepWidth (c :: rest)) (hc : carry ≠ []) :
    wordsOfCarry (c :: rest) carry
      = carry :: wordsOfCarry ((c :: rest).drop (sepWidth (c :: rest))) [] := by
  simp only [wordsOfCarry]
  rw [dif_pos h, if_neg hc]

/-- The width-1 separator step at an empty carry, drop resolved. -/
theorem wordsOfCarry_sep1_nil {c : UInt8} {rest : List UInt8}
    (h : sepWidth (c :: rest) = 1) :
    wordsOfCarry (c :: rest) [] = wordsOfCarry rest [] := by
  have h0 := wordsOfCarry_sep_nil (c := c) (rest := rest) (by omega)
  rw [h] at h0
  simpa using h0

/-- The width-1 separator step at a nonempty carry, drop resolved. -/
theorem wordsOfCarry_sep1_cons {c : UInt8} {rest carry : List UInt8}
    (h : sepWidth (c :: rest) = 1) (hc : carry ≠ []) :
    wordsOfCarry (c :: rest) carry = carry :: wordsOfCarry rest [] := by
  have h0 := wordsOfCarry_sep_cons (c := c) (rest := rest) (by omega) hc
  rw [h] at h0
  simpa using h0

/-! ## The input family (proof vocabulary — the ∃-witness, never in
the claim)

`buildText n seed` emits a leading space, then per word `i < n` the
letter `'a' + (seed+i)%3` (Go's own uint64 wrap in `seed+i` kept
honestly) followed by a separator VARIED by position: one space, two
spaces, or a tab. `qWord qsel` is the queried one-letter word. -/

/-- The letter byte of word `i` (a value in `97…99`, i.e. `a`–`c`). -/
def letterByte (seed i : Nat) : UInt8 :=
  UInt8.ofNat (97 + ((seed + i) % 2 ^ 64) % 3)

/-- The separator AFTER word `i`: space, two spaces, or tab. -/
def sepBytes (i : Nat) : List UInt8 :=
  if i % 3 = 0 then [32] else if i % 3 = 1 then [32, 32] else [9]

/-- The bytes `buildText n seed` produces. -/
def textFamily (n seed : Nat) : List UInt8 :=
  32 :: ((List.range n).map (fun i => letterByte seed i :: sepBytes i)).flatten

/-- The bytes of the queried word (`string(rune(97 + qsel%3))`). -/
def qWord (qsel : Nat) : List UInt8 :=
  [UInt8.ofNat (97 + qsel % 3)]

/-- The words of the built text: `n` one-letter words. -/
def letterWords (n seed : Nat) : List (List UInt8) :=
  (List.range n).map (fun i => [letterByte seed i])

theorem letterByte_toNat (seed i : Nat) :
    (letterByte seed i).toNat = 97 + ((seed + i) % 2 ^ 64) % 3 := by
  have h3 : ((seed + i) % 2 ^ 64) % 3 < 3 := Nat.mod_lt _ (by omega)
  have h : (UInt8.ofNat (97 + ((seed + i) % 2 ^ 64) % 3)).toNat
      = (97 + ((seed + i) % 2 ^ 64) % 3) % 256 := by simp
  simp only [letterByte, h]
  omega

theorem letterByte_ge (seed i : Nat) : 97 ≤ (letterByte seed i).toNat := by
  rw [letterByte_toNat]; omega

theorem letterByte_le (seed i : Nat) : (letterByte seed i).toNat ≤ 99 := by
  have h3 : ((seed + i) % 2 ^ 64) % 3 < 3 := Nat.mod_lt _ (by omega)
  rw [letterByte_toNat]; omega

theorem letterWords_length (n seed : Nat) :
    (letterWords n seed).length = n := by
  simp [letterWords]

theorem letterWords_zero (seed : Nat) : letterWords 0 seed = [] := rfl

/-- The prefix step the build loop's invariant consumes (words side). -/
theorem letterWords_succ (n seed : Nat) :
    letterWords (n + 1) seed
      = letterWords n seed ++ [[letterByte seed n]] := by
  simp [letterWords, List.range_succ]

theorem textFamily_zero (seed : Nat) : textFamily 0 seed = [32] := rfl

/-- The prefix step the build loop's invariant consumes (bytes side):
one iteration appends the letter then its separator. -/
theorem textFamily_succ (n seed : Nat) :
    textFamily (n + 1) seed
      = textFamily n seed ++ (letterByte seed n :: sepBytes n) := by
  simp [textFamily, List.range_succ]

/-! ## The family split (theorem A — the load-bearing bridge)

After the leading space the text is a concatenation of
`letter :: sepBytes i` blocks; the scan peels one block per word. -/

/-- One block's separator closes the open field, whatever its shape:
`[32]` is one width-1 step, `[32, 32]` is TWO width-1 steps (bytes
`32`/`9` are width-1 REGARDLESS of what follows), `[9]` one. -/
theorem wordsOfCarry_sepBytes (i : Nat) (rest : List UInt8)
    {carry : List UInt8} (hc : carry ≠ []) :
    wordsOfCarry (sepBytes i ++ rest) carry
      = carry :: wordsOfCarry rest [] := by
  unfold sepBytes
  split
  · simp only [List.cons_append, List.nil_append]
    rw [wordsOfCarry_sep1_cons (sepWidth_space rest) hc]
  · split
    · simp only [List.cons_append, List.nil_append]
      rw [wordsOfCarry_sep1_cons (sepWidth_space (32 :: rest)) hc,
        wordsOfCarry_sep1_nil (sepWidth_space rest)]
    · simp only [List.cons_append, List.nil_append]
      rw [wordsOfCarry_sep1_cons (sepWidth_tab rest) hc]

/-- The scan over the block concatenation, generalized over the start
index `j` (the separator shape depends on the ABSOLUTE word index, so
the induction carries it). -/
private theorem wordsOfCarry_blocks (seed : Nat) :
    ∀ n j : Nat,
      wordsOfCarry
        (((List.range' j n).map
          (fun i => letterByte seed i :: sepBytes i)).flatten) []
      = (List.range' j n).map (fun i => [letterByte seed i]) := by
  intro n
  induction n with
  | zero => intro j; simp [wordsOfCarry_nil_nil]
  | succ n ih =>
      intro j
      rw [List.range'_succ]
      simp only [List.map_cons, List.flatten_cons, List.cons_append]
      rw [wordsOfCarry_letter (sepWidth_letter (letterByte_ge seed j)
        (by have := letterByte_le seed j; omega) _)]
      simp only [List.nil_append]
      rw [wordsOfCarry_sepBytes j _ (by simp)]
      rw [ih (j + 1)]

/-- **The family split**: the words of the built text are exactly the
`n` one-letter words. The leading space is a width-1 separator at an
empty carry; each block then peels one word. -/
theorem wordsOf_textFamily (n seed : Nat) :
    wordsOf (textFamily n seed) = letterWords n seed := by
  simp only [wordsOf, textFamily, letterWords]
  rw [wordsOfCarry_sep1_nil (sepWidth_space _), List.range_eq_range']
  exact wordsOfCarry_blocks seed n 0

/-! ## The specification layer (order-independent)

`WordCount`'s statement functions, one key type over: words are
`List UInt8`, not `Int`.
-- KIT-GAP WITNESS: key-generic MapMem/count-layer (3rd key type:
-- Int, and now List UInt8); promotion candidate, ≥2 consumers. -/

/-- Occurrences of the word `w` in `ws`. -/
def multiplicity (w : List UInt8) (ws : List (List UInt8)) : Nat :=
  (ws.filter (· = w)).length

/-- The largest multiplicity any word attains in `ws` (`0` for `[]`) —
a commutative-idempotent max-fold, so it is invariant under iteration
order: the shape the ∀-choices quantifier forces. -/
def maxMultiplicity (ws : List (List UInt8)) : Nat :=
  ws.foldl (fun acc w => max acc (multiplicity w ws)) 0

/-! ## The abstract counts model, `List UInt8` keys

`GoLeanProofs.MapMem`'s `idxOf?`/`cnt`/`setk` association-list model
mirrored one key type over — the abstract content of the
`map[string]uint64` data cell.
-- KIT-GAP WITNESS: key-generic MapMem/count-layer (3rd key type:
-- Int, and now List UInt8); promotion candidate, ≥2 consumers. -/

/-- First index of key `w` (the machine's entry-scan order). -/
def idxOfW? : List (List UInt8 × Nat) → List UInt8 → Option Nat
  | [], _ => none
  | (k, _) :: rest, w =>
      if k = w then some 0 else (idxOfW? rest w).map (· + 1)

/-- Assoc lookup at the FIRST occurrence, `0` when absent — exactly a
Go map read's zero-value semantics on this fragment. -/
def cntW : List (List UInt8 × Nat) → List UInt8 → Nat
  | [], _ => 0
  | (k, c) :: rest, w => if k = w then c else cntW rest w

/-- Update the first occurrence of `w`, or append — exactly the map
write's update-or-insert on the entry list. -/
def setkW : List (List UInt8 × Nat) → List UInt8 → Nat → List (List UInt8 × Nat)
  | [], w, v => [(w, v)]
  | (k, c) :: rest, w, v =>
      if k = w then (k, v) :: rest else (k, c) :: setkW rest w v

theorem idxOfW?_none_cnt {kvs : List (List UInt8 × Nat)} {w : List UInt8}
    (h : idxOfW? kvs w = none) : cntW kvs w = 0 := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOfW?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [cntW, if_neg hk]
        exact ih (by cases hidx : idxOfW? rest w <;> simp [hidx] at h ⊢)

theorem idxOfW?_none_setk {kvs : List (List UInt8 × Nat)} {w : List UInt8}
    (h : idxOfW? kvs w = none) (v : Nat) :
    kvs ++ [(w, v)] = setkW kvs w v := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOfW?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [List.cons_append, setkW, if_neg hk]
        exact congrArg _
          (ih (by cases hidx : idxOfW? rest w <;> simp [hidx] at h ⊢))

theorem idxOfW?_some_snd {kvs : List (List UInt8 × Nat)} {w : List UInt8}
    {j : Nat} (h : idxOfW? kvs w = some j) :
    kvs[j]? = some (w, cntW kvs w) := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOfW?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [cntW, hk]
      · simp only [if_neg hk] at h
        cases hidx : idxOfW? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.getElem?_cons_succ, cntW, if_neg hk]
            exact ih hidx

theorem idxOfW?_some_setk {kvs : List (List UInt8 × Nat)} {w : List UInt8}
    {j : Nat} (h : idxOfW? kvs w = some j) (v : Nat) :
    kvs.set j (w, v) = setkW kvs w v := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOfW?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [setkW, hk, List.set]
      · simp only [if_neg hk] at h
        cases hidx : idxOfW? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.set, setkW, if_neg hk]
            exact congrArg _ (ih hidx)

/-! ## The counting fold, `List UInt8` keys

`GoLeanProofs.MapMem`'s `bump`/`countsFold` chain mirrored one key
type over — the abstract content of the counting map (`m[w]++` folded
over the word list).
-- KIT-GAP WITNESS: key-generic MapMem/count-layer (3rd key type:
-- Int, and now List UInt8); promotion candidate, ≥2 consumers. -/

/-- One word lands in the counts list: increment the first occurrence
of the key, or append `(w, 1)` — first-occurrence insertion order,
matching the machine's map write. -/
def bumpW : List (List UInt8 × Nat) → List UInt8 → List (List UInt8 × Nat)
  | [], w => [(w, 1)]
  | (k, c) :: rest, w =>
      if k = w then (k, c + 1) :: rest else (k, c) :: bumpW rest w

/-- The counts list after processing `ws`, in first-occurrence
insertion order — the abstract content of the map data cell. -/
def countsFoldW (ws : List (List UInt8)) : List (List UInt8 × Nat) :=
  ws.foldl bumpW []

/-- What the machine's write computes is `bumpW`: the value written is
`counts[w] + 1` at the first occurrence (or `0 + 1` fresh). -/
theorem setkW_cnt_succ :
    ∀ (kvs : List (List UInt8 × Nat)) (w : List UInt8),
    setkW kvs w (cntW kvs w + 1) = bumpW kvs w := by
  intro kvs
  induction kvs with
  | nil => intro w; rfl
  | cons kv rest ih =>
      intro w
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp [setkW, cntW, bumpW, hk]
      · simp [setkW, cntW, bumpW, hk, ih w]

theorem countsFoldW_nil : countsFoldW [] = [] := rfl

/-- The one-word step of the counting loop's invariant. -/
theorem countsFoldW_append (p : List (List UInt8)) (w : List UInt8) :
    countsFoldW (p ++ [w]) = bumpW (countsFoldW p) w := by
  simp [countsFoldW, List.foldl_append]

/-- `cntW` after a `bumpW`. -/
private theorem cnt_bumpW (kvs : List (List UInt8 × Nat))
    (w x : List UInt8) :
    cntW (bumpW kvs w) x
      = if x = w then cntW kvs w + 1 else cntW kvs x := by
  induction kvs with
  | nil =>
      by_cases hx : x = w
      · simp [bumpW, cntW, hx]
      · simp [bumpW, cntW, hx, Ne.symm hx]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · subst hk
        by_cases hx : x = k
        · simp [bumpW, cntW, hx]
        · simp [bumpW, cntW, Ne.symm hx, hx]
      · by_cases hxk : k = x
        · subst hxk
          simp [bumpW, cntW, hk]
        · simp [bumpW, cntW, hk, hxk, ih]

private theorem filter_len_cons (v w : List UInt8)
    (l : List (List UInt8)) :
    ((w :: l).filter (· = v)).length
      = (if w = v then 1 else 0) + (l.filter (· = v)).length := by
  simp only [List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

private theorem cnt_countsFoldW_aux (l : List (List UInt8)) :
    ∀ (kvs : List (List UInt8 × Nat)) (x : List UInt8),
    cntW (List.foldl bumpW kvs l) x
      = cntW kvs x + (l.filter (· = x)).length := by
  induction l with
  | nil => intro kvs x; simp
  | cons w rest ih =>
      intro kvs x
      simp only [List.foldl_cons, ih, cnt_bumpW, filter_len_cons]
      by_cases hx : x = w
      · subst hx
        have h1 : (if x = x then cntW kvs x + 1 else cntW kvs x)
            = cntW kvs x + 1 := if_pos rfl
        have h2 : (if x = x then 1 else 0) = 1 := if_pos rfl
        omega
      · have h1 : (if x = w then cntW kvs w + 1 else cntW kvs x)
            = cntW kvs x := if_neg hx
        have h2 : (if w = x then 1 else 0) = 0 := if_neg (Ne.symm hx)
        omega

/-- **The counting-fold invariant**: the fold's count at any key is
that key's `multiplicity` (0 on both sides for an absent key — Go's
zero-value read is exactly the absent case). -/
theorem cnt_countsFoldW (ws : List (List UInt8)) (w : List UInt8) :
    cntW (countsFoldW ws) w = multiplicity w ws := by
  simpa [countsFoldW, cntW, multiplicity]
    using cnt_countsFoldW_aux ws [] w

/-- Every entry of a `bumpW` has its key at the bumped value or in the
seed. -/
private theorem mem_bumpW {kvs : List (List UInt8 × Nat)} {w : List UInt8}
    {p : List UInt8 × Nat} (h : p ∈ bumpW kvs w) :
    p.1 = w ∨ p ∈ kvs := by
  induction kvs with
  | nil =>
      simp only [bumpW, List.mem_singleton] at h
      exact .inl (by rw [h])
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp only [bumpW, if_pos hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inl (by rw [h1]; exact hk)
        · exact .inr (List.mem_cons.mpr (.inr h1))
      · simp only [bumpW, if_neg hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inr (List.mem_cons.mpr (.inl h1))
        · rcases ih h1 with h2 | h2
          · exact .inl h2
          · exact .inr (List.mem_cons.mpr (.inr h2))

private theorem countsFoldW_key_mem_aux (l : List (List UInt8)) :
    ∀ (kvs : List (List UInt8 × Nat)) (p : List UInt8 × Nat),
    p ∈ List.foldl bumpW kvs l → p.1 ∈ l ∨ p ∈ kvs := by
  induction l with
  | nil => intro kvs p h; exact .inr h
  | cons w rest ih =>
      intro kvs p h
      simp only [List.foldl_cons] at h
      rcases ih (bumpW kvs w) p h with h | h
      · exact .inl (by simp [h])
      · rcases mem_bumpW h with h | h
        · exact .inl (by simp [h])
        · exact .inr h

/-- Every key of the fold occurs in the folded word list. -/
theorem countsFoldW_key_mem {l : List (List UInt8)}
    {p : List UInt8 × Nat} (hp : p ∈ countsFoldW l) : p.1 ∈ l := by
  rcases countsFoldW_key_mem_aux l [] p hp with h | h
  · exact h
  · cases h

/-- Distinct keys (`Nodup` on the key column) — `bumpW` preserves
it. -/
private theorem nodup_keys_bumpW {kvs : List (List UInt8 × Nat)}
    {w : List UInt8} (h : (kvs.map Prod.fst).Nodup) :
    ((bumpW kvs w).map Prod.fst).Nodup := by
  induction kvs with
  | nil => simp [bumpW]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at h
      by_cases hk : k = w
      · simpa [bumpW, hk, List.nodup_cons] using h
      · simp only [bumpW, if_neg hk, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih h.2⟩
        intro hc
        rcases List.mem_map.mp hc with ⟨p, hp, hpk⟩
        rcases mem_bumpW hp with h1 | h1
        · exact hk (hpk ▸ h1)
        · exact h.1 (List.mem_map.mpr ⟨p, h1, hpk⟩)

private theorem countsFoldW_nodup_keys_aux (l : List (List UInt8)) :
    ∀ kvs : List (List UInt8 × Nat), (kvs.map Prod.fst).Nodup →
    ((List.foldl bumpW kvs l).map Prod.fst).Nodup := by
  induction l with
  | nil => intro kvs h; exact h
  | cons w rest ih =>
      intro kvs h
      exact ih (bumpW kvs w) (nodup_keys_bumpW h)

/-- The fold's key column is duplicate-free. -/
theorem countsFoldW_nodup_keys (l : List (List UInt8)) :
    ((countsFoldW l).map Prod.fst).Nodup :=
  countsFoldW_nodup_keys_aux l [] (by simp)

/-- With distinct keys, membership pins the count: `(k, c) ∈ kvs →
cntW kvs k = c`. -/
theorem cntW_of_mem_nodup :
    ∀ {kvs : List (List UInt8 × Nat)} {k : List UInt8} {c : Nat},
    (kvs.map Prod.fst).Nodup → (k, c) ∈ kvs → cntW kvs k = c := by
  intro kvs
  induction kvs with
  | nil => intro k c _ h; cases h
  | cons kv rest ih =>
      intro k c hnd h
      obtain ⟨k', c'⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with h | h
      · injection h with h1 h2
        subst h1; subst h2
        simp [cntW]
      · have hk : k' ≠ k := by
          intro hc
          subst hc
          exact hnd.1 (List.mem_map.mpr ⟨(k', c), h, rfl⟩)
        simp only [cntW, if_neg hk]
        exact ih hnd.2 h

/-- Positive `cntW` means the key is present. -/
theorem cntW_pos_mem {kvs : List (List UInt8 × Nat)} {x : List UInt8}
    (h : 0 < cntW kvs x) : (x, cntW kvs x) ∈ kvs := by
  induction kvs with
  | nil => simp [cntW] at h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = x
      · subst hk
        simp only [cntW] at h ⊢
        exact List.mem_cons.mpr (.inl rfl)
      · simp only [cntW, if_neg hk] at h ⊢
        exact List.mem_cons.mpr (.inr (ih h))

/-- Value bound: no count exceeds the number of words folded. -/
theorem countsFoldW_val_le (l : List (List UInt8))
    {p : List UInt8 × Nat} (hp : p ∈ countsFoldW l) : p.2 ≤ l.length := by
  obtain ⟨k, c⟩ := p
  have hnd := countsFoldW_nodup_keys l
  have hcnt : cntW (countsFoldW l) k = c := cntW_of_mem_nodup hnd hp
  have := cnt_countsFoldW l k
  rw [hcnt] at this
  have hle : (l.filter (· = k)).length ≤ l.length :=
    List.length_filter_le _ _
  simp only [multiplicity] at this
  omega

/-- The running count is bounded by the number of words folded so far
(the counting loop's no-overflow bound). -/
theorem cntW_take_le {ws : List (List UInt8)} {i : Nat} (w : List UInt8) :
    cntW (countsFoldW (ws.take i)) w ≤ i := by
  rw [cnt_countsFoldW]
  have h1 : ((ws.take i).filter (· = w)).length ≤ (ws.take i).length :=
    List.length_filter_le _ _
  have h2 : (ws.take i).length ≤ i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  simp only [multiplicity]
  omega

/-! ## The max fold

`WordCount`'s max layer, mirrored (`maxOf` itself is key-type
independent; the bridges below are one key type over).
-- KIT-GAP WITNESS: key-generic MapMem/count-layer (3rd key type:
-- Int, and now List UInt8); promotion candidate, ≥2 consumers. -/

/-- Max over a `Nat` list (base 0) — the value-column aggregate. -/
def maxOf (l : List Nat) : Nat := l.foldr max 0

theorem maxOf_nil : maxOf [] = 0 := rfl

theorem maxOf_cons (a : Nat) (l : List Nat) :
    maxOf (a :: l) = max a (maxOf l) := rfl

theorem mem_le_maxOf {l : List Nat} {c : Nat} (h : c ∈ l) :
    c ≤ maxOf l := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
      rcases List.mem_cons.mp h with h | h
      · rw [maxOf_cons, h]
        exact Nat.le_max_left _ _
      · simp only [maxOf_cons]
        exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxOf_le {l : List Nat} {B : Nat} (h : ∀ c ∈ l, c ≤ B) :
    maxOf l ≤ B := by
  induction l with
  | nil => simp [maxOf_nil]
  | cons a rest ih =>
      simp only [maxOf_cons, Nat.max_le]
      exact ⟨h a (by simp), ih (fun c hc => h c (by simp [hc]))⟩

/-- **The pick-and-erase law**: removing the picked entry and maxing
it back in recovers the whole fold — the per-iteration invariant step
of the range-over-map loop, invariant under EVERY pick. -/
theorem maxOf_eraseIdx :
    ∀ (l : List Nat) (i : Nat), i < l.length →
    max l[i]! (maxOf (l.eraseIdx i)) = maxOf l := by
  intro l
  induction l with
  | nil => intro i h; cases h
  | cons a rest ih =>
      intro i hi
      cases i with
      | zero =>
          show max (a :: rest)[0]! (maxOf rest) = maxOf (a :: rest)
          rw [show (a :: rest)[0]! = a from by simp, maxOf_cons]
      | succ n =>
          have hn : n < rest.length := by simpa using hi
          simp only [List.eraseIdx_cons_succ, maxOf_cons]
          rw [show (a :: rest)[n + 1]! = rest[n]! from by simp]
          rw [← ih n hn]
          omega

/-! ### The spec bridge: `maxOf` of the counts equals
`maxMultiplicity`
-- KIT-GAP WITNESS: key-generic MapMem/count-layer (3rd key type:
-- Int, and now List UInt8); promotion candidate, ≥2 consumers. -/

private theorem foldl_max_le {f : List UInt8 → Nat} {B : Nat} :
    ∀ (l : List (List UInt8)) (a : Nat), a ≤ B → (∀ v ∈ l, f v ≤ B) →
    l.foldl (fun acc v => max acc (f v)) a ≤ B := by
  intro l
  induction l with
  | nil => intro a ha _; simpa using ha
  | cons v rest ih =>
      intro a ha h
      simp only [List.foldl_cons]
      exact ih _ (Nat.max_le.mpr ⟨ha, h v (by simp)⟩)
        (fun x hx => h x (by simp [hx]))

private theorem foldl_max_ge_init {f : List UInt8 → Nat} :
    ∀ (l : List (List UInt8)) (a : Nat),
    a ≤ l.foldl (fun acc v => max acc (f v)) a := by
  intro l
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons w rest ih =>
      intro a
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem le_foldl_max {f : List UInt8 → Nat} :
    ∀ (l : List (List UInt8)) (a : Nat) {v : List UInt8}, v ∈ l →
    f v ≤ l.foldl (fun acc v => max acc (f v)) a := by
  intro l
  induction l with
  | nil => intro a v h; cases h
  | cons w rest ih =>
      intro a v h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init rest _)
      · exact ih _ h

theorem mult_le_maxMult {ws : List (List UInt8)} {v : List UInt8}
    (h : v ∈ ws) : multiplicity v ws ≤ maxMultiplicity ws :=
  le_foldl_max (f := fun v => multiplicity v ws) ws 0 h

theorem maxMult_le {ws : List (List UInt8)} {B : Nat}
    (h : ∀ v ∈ ws, multiplicity v ws ≤ B) : maxMultiplicity ws ≤ B :=
  foldl_max_le (f := fun v => multiplicity v ws) ws 0 (Nat.zero_le _) h

private theorem multiplicity_cons (v w : List UInt8)
    (ws : List (List UInt8)) :
    multiplicity v (w :: ws)
      = (if w = v then 1 else 0) + multiplicity v ws := by
  simp only [multiplicity, List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

private theorem mem_mult_pos {ws : List (List UInt8)} {v : List UInt8}
    (h : v ∈ ws) : 0 < multiplicity v ws := by
  induction ws with
  | nil => cases h
  | cons w rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [multiplicity_cons]
        have h1 : (if v = v then 1 else 0) = 1 := if_pos rfl
        omega
      · rw [multiplicity_cons]
        have := ih h
        omega

/-- **The spec bridge**: the max over the counts-list value column IS
`maxMultiplicity`. -/
theorem maxOf_countsFoldW (ws : List (List UInt8)) :
    maxOf ((countsFoldW ws).map Prod.snd) = maxMultiplicity ws := by
  have hnd : ((countsFoldW ws).map Prod.fst).Nodup :=
    countsFoldW_nodup_keys ws
  apply Nat.le_antisymm
  · -- every count is some key's multiplicity, ≤ the max
    apply maxOf_le
    intro c hc
    rcases List.mem_map.mp hc with ⟨⟨k, c'⟩, hp, hsnd⟩
    have hkey : k ∈ ws := countsFoldW_key_mem hp
    have hcnt : cntW (countsFoldW ws) k = c' := cntW_of_mem_nodup hnd hp
    have : c' = multiplicity k ws := by
      rw [← hcnt, cnt_countsFoldW ws k]
    subst hsnd
    show c' ≤ maxMultiplicity ws
    rw [this]
    exact mult_le_maxMult hkey
  · -- the max multiplicity is attained by some entry's count
    apply maxMult_le
    intro v hv
    have hpos : 0 < multiplicity v ws := mem_mult_pos hv
    have hcnt : cntW (countsFoldW ws) v = multiplicity v ws :=
      cnt_countsFoldW ws v
    have hmem : (v, cntW (countsFoldW ws) v) ∈ countsFoldW ws :=
      cntW_pos_mem (by omega)
    have : cntW (countsFoldW ws) v
        ∈ (countsFoldW ws).map Prod.snd :=
      List.mem_map.mpr ⟨(v, cntW (countsFoldW ws) v), hmem, rfl⟩
    rw [← hcnt]
    exact mem_le_maxOf this

/-! ## Conformance pins

The 8 go-run-confirmed splits of
`Corpus/coverage/exec/strings/fields-conformance/cases.tsv`, as byte
lists (each `#guard` is an EVALUATION — the compiled scan — never a
kernel `decide` on an unevaluated proposition). -/

-- empty: no fields.
#guard wordsOf ([] : List UInt8) = []
-- all-space " \t\n\v\f\r ": no fields.
#guard wordsOf [32, 9, 10, 11, 12, 13, 32] = []
-- single "abc": one field, the whole string.
#guard wordsOf [97, 98, 99] = [[97, 98, 99]]
-- lead-trail "  ab  cd  ": "ab" | "cd".
#guard wordsOf [32, 32, 97, 98, 32, 32, 99, 100, 32, 32]
  = [[97, 98], [99, 100]]
-- consec-mixed "a\t\tb \n c\r\vd": "a" | "b" | "c" | "d".
#guard wordsOf [97, 9, 9, 98, 32, 10, 32, 99, 13, 11, 100]
  = [[97], [98], [99], [100]]
-- unicode-space "a bcd d　e": "a"|"bc"|"d"|"d"|"e".
#guard wordsOf [97, 0xC2, 0xA0, 98, 99, 0xC2, 0x85, 100,
    0xE2, 0x80, 0x83, 100, 0xE3, 0x80, 0x80, 101]
  = [[97], [98, 99], [100], [100], [101]]
-- unicode-non-space "a​b ÿc": ZWSP and ÿ do NOT split.
#guard wordsOf [97, 0xE2, 0x80, 0x8B, 98, 32, 0xC3, 0xBF, 99]
  = [[97, 0xE2, 0x80, 0x8B, 98], [0xC3, 0xBF, 99]]
-- invalid-utf8 "\xffa b\xe2\x80": undecodable bytes are field
-- content; the trailing truncated E2 80 is NOT a separator.
#guard wordsOf [0xFF, 97, 32, 98, 0xE2, 0x80]
  = [[0xFF, 97], [98, 0xE2, 0x80]]

-- The truncated-separator widths, pinned directly.
#guard sepWidth [0xE2, 0x80] = 0
#guard sepWidth [0xC2] = 0
#guard sepWidth [0xE2, 0x80, 0x8B] = 0
#guard sepWidth [0xE2, 0x80, 0x8A] = 3

-- Family spot checks (the bridge, evaluated at small inputs).
#guard wordsOf (textFamily 0 0) = letterWords 0 0
#guard wordsOf (textFamily 5 1) = letterWords 5 1
#guard wordsOf (textFamily 7 3) = letterWords 7 3

end GoLean.Examples.WordFreq
