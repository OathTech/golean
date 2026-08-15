import GoLeanProofs.Examples.Targets
import GoLeanProofs.MapMem

/-!
# FibMemo — Pure

The specification-side vocabulary of the `fibmemo` example (Gallery
Campaign G1, hard lane): the wrapped Fibonacci values the machine's
uint64 arithmetic produces, and the MEMO TABLE MODEL `mtbl` — the
association list the machine's `map[uint64]uint64` holds after the
memoized recursion has computed keys `2..j`.

The specification function itself is `fibSpec` (the designated
statement vocabulary of the existing `fib` example, imported from
`Examples/Targets.lean` — one definition, so the gallery's "Fibonacci"
means one thing). This module adds only:

* `fibW m = fibSpec m % 2^64` — the wrapped value that actually
  crosses the machine's uint64 cells (machine-integer honesty, the
  `fib` example's boundary treatment);
* `mtbl j` — the memo table with keys `2..j` in INSERTION order (the
  machine appends `k` after computing `k`, and the up-chain computes
  keys in increasing order, so the entry list is exactly this);
* the `idxOf?`/`setk` facts the machine proof consumes: a key above
  the table's ceiling misses, a key inside hits at its position with
  the wrapped value, and inserting `k` into `mtbl (k-1)` appends to
  form `mtbl k`.
-/

namespace GoLean.Examples.FibMemo

open GoLean GoLean.MapMem
open GoLean.Examples.Fib (fibSpec)

/-- The wrapped Fibonacci value: what the Go program's uint64 cells
hold. `fibSpec` is the mathematical function (designated vocabulary of
the `fib` example); the machine wraps every addition mod `2^64`, and
one reduction of the true value equals the composition of the wrapped
additions (`fibW_rec`). -/
def fibW (m : Nat) : Nat := fibSpec m % 2 ^ 64

theorem fibW_lt (m : Nat) : fibW m < 2 ^ 64 :=
  Nat.mod_lt _ (by decide)

theorem fibW_zero : fibW 0 = 0 := rfl

theorem fibW_one : fibW 1 = 1 := rfl

/-- `fibW`'s base cases in the machine's shape: below the `n < 2`
guard the returned value IS the argument. -/
theorem fibW_small {m : Nat} (h : m ≤ 1) : fibW m = m := by
  match m, h with
  | 0, _ => rfl
  | 1, _ => rfl

/-- The wrapped recurrence: one mod of the true sum equals the sum of
the wrapped summands, re-wrapped — which is exactly the machine's
`$c0 + $c1` normalization. -/
theorem fibW_rec {k : Nat} (h : 2 ≤ k) :
    fibW k = (fibW (k - 1) + fibW (k - 2)) % 2 ^ 64 := by
  match k, h with
  | n + 2, _ =>
    show fibSpec (n + 2) % 2 ^ 64 = _
    simp only [show n + 2 - 1 = n + 1 from rfl, show n + 2 - 2 = n from rfl,
      fibW, fibSpec]
    rw [Nat.add_mod (fibSpec n) (fibSpec (n + 1)), Nat.add_comm]

/-- The memo table after the recursion has computed keys `2..j`
(`j = 1` or `j = 0` means empty), in insertion order. -/
def mtbl (j : Nat) : List (Int × Nat) :=
  (List.range' 2 (j - 1)).map fun (m : Nat) => ((m : Int), fibW m)

theorem mtbl_nil {j : Nat} (h : j ≤ 1) : mtbl j = [] := by
  match j, h with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Every key in `mtbl j` lies in `[2, j]`. -/
theorem mtbl_key_lt {j : Nat} {p : Int × Nat} (hp : p ∈ mtbl j) :
    2 ≤ p.1 ∧ p.1 ≤ (j : Int) := by
  simp only [mtbl, List.mem_map] at hp
  obtain ⟨m, hm, rfl⟩ := hp
  rw [List.mem_range'] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  constructor
  · show (2 : Int) ≤ ((2 + 1 * i : Nat) : Int)
    have : (2 : Nat) ≤ 2 + 1 * i := by omega
    exact_mod_cast this
  · show ((2 + 1 * i : Nat) : Int) ≤ (j : Int)
    have : 2 + 1 * i ≤ j := by omega
    exact_mod_cast this

/-- A key ABOVE the table's ceiling misses (the down-chain's lookup). -/
theorem idxOf?_mtbl_none {j k : Nat} (h : j < k) :
    idxOf? (mtbl j) (k : Int) = none := by
  have hgen : ∀ (l : List (Int × Nat)), (∀ p ∈ l, p.1 ≠ (k : Int)) →
      idxOf? l (k : Int) = none := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p rest ih =>
        intro hall
        simp only [idxOf?, if_neg (hall p (by simp)),
          ih (fun q hq => hall q (by simp [hq]))]
        rfl
  refine hgen _ (fun p hp => ?_)
  have := mtbl_key_lt hp
  have hk : (j : Int) < (k : Int) := by exact_mod_cast h
  omega

/-- A key inside `[2, j]` hits at position `i - 2`, holding the
wrapped value (the up-chain's memo hit). -/
theorem idxOf?_mtbl_some {i j : Nat} (h2 : 2 ≤ i) (hij : i ≤ j) :
    idxOf? (mtbl j) (i : Int) = some (i - 2)
      ∧ (mtbl j)[i - 2]? = some ((i : Int), fibW i) := by
  -- generalize: scanning a range'-table starting at `s` for key `i ≥ s`
  have hgen : ∀ (len s : Nat), s ≤ i → i < s + len →
      idxOf? ((List.range' s len).map fun (m : Nat) => ((m : Int), fibW m)) (i : Int)
          = some (i - s)
        ∧ ((List.range' s len).map fun (m : Nat) => ((m : Int), fibW m))[i - s]?
          = some ((i : Int), fibW i) := by
    intro len
    induction len with
    | zero => intro s h1 h2; omega
    | succ l ih =>
        intro s hs hlt
        rw [List.range'_succ]
        by_cases hsi : s = i
        · subst hsi
          simp [idxOf?]
        · have hs' : s + 1 ≤ i := by omega
          have hlt' : i < (s + 1) + l := by omega
          obtain ⟨hidx, hget⟩ := ih (s + 1) hs' hlt'
          have hne : ¬ ((s : Int) = (i : Int)) := by
            intro hc
            exact hsi (by exact_mod_cast hc)
          constructor
          · simp only [List.map_cons, idxOf?, if_neg hne, hidx,
              Option.map_some]
            congr 1
            omega
          · simp only [List.map_cons]
            rw [show i - s = (i - (s + 1)) + 1 from by omega]
            simpa using hget
  have := hgen (j - 1) 2 h2 (by omega)
  exact this

/-- Inserting the freshly computed `k` appends: the machine's
`memo[n] = r` on `mtbl (k-1)` yields `mtbl k`. -/
theorem setk_mtbl {k : Nat} (h : 2 ≤ k) :
    setk (mtbl (k - 1)) (k : Int) (fibW k) = mtbl k := by
  have hmiss : idxOf? (mtbl (k - 1)) (k : Int) = none :=
    idxOf?_mtbl_none (by omega)
  rw [← idxOf?_none_setk hmiss]
  show _ = (List.range' 2 (k - 1)).map fun (m : Nat) => ((m : Int), fibW m)
  rw [show k - 1 = (k - 2) + 1 from by omega, List.range'_concat,
    List.map_append, show 2 + 1 * (k - 2) = k from by omega]
  show mtbl (k - 2 + 1) ++ _ = _
  rw [show mtbl (k - 2 + 1)
      = (List.range' 2 (k - 2)).map fun (m : Nat) => ((m : Int), fibW m) from by
    simp [mtbl]]
  rfl

/-- The memo-hit VALUE read back out of the table is `fibW i` — stated
at the `toEntries` encoding the machine holds. -/
theorem toEntries_mtbl_get {i j : Nat} (h2 : 2 ≤ i) (hij : i ≤ j) :
    (toEntries (mtbl j))[i - 2]?
      = some (.int (i : Int) .uint64, .int ((fibW i : Nat) : Int) .uint64) := by
  obtain ⟨_, hget⟩ := idxOf?_mtbl_some h2 hij
  rw [show (toEntries (mtbl j))[i - 2]?
      = ((mtbl j)[i - 2]?).map (fun kv => (.int kv.1 .uint64, .int (kv.2 : Int) .uint64))
    from by simp [toEntries, List.getElem?_map]]
  rw [hget]
  rfl

end GoLean.Examples.FibMemo
