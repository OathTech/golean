import GoLeanProofs.Examples.TwoSum.Subject

/-!
# TwoSum — the `twosum` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/twosum/main.go`
(differentially green against `go run`, 14 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/twosum-lowered.repr`
and carried in `GoLeanProofs.Examples.TwoSumProgram`.

The subject `twoSum` is the O(n²) double loop: outer `i` ascending,
inner `j` from `i+1` ascending, returning the FIRST pair in scan order
whose wrapping uint64 sum hits the target — or the out-of-range
sentinel `(len(s), len(s))` when no pair does. The harness is the S3
RELATIONAL style: it returns the searched array (as a fixed-cap
`[8]uint64`) alongside both indices, so the postcondition is a
relation over the RETURNED DATA — `(i, j) = twoSumSpec vals target` —
with no family function re-describing the setup inside the claim.

**What the NESTED loop costs the proof, and why it is worth saying.**
Each outer iteration of `twoSum` declares a fresh inner `j` and loop
flag, so the machine allocates two new cells per outer round and the
inner loop's live state sits at SYMBOLIC addresses past a growing
region of dead cells. The proof threads an abstract dead-region
parameter (with `StepKit.DeadFrom` freshness) through every
subject-phase segment — the raw `rfl` segments resolve only concrete
front addresses, and the per-iteration accesses to the live pair go
through conditioned kit steps. The early `return` out of the INNER
loop is the palindrome exemplar's shape one level deeper: the hit path
runs to the DRIVER TERMINAL through both loop continuations, and the
outer induction existentially forgets the dead region, the final
`nextAddr` and the outer counter — nothing returned depends on them.

The per-phase shards:

* `TwoSum.Pure` — `twoSumSpec` and its `findFrom`/`findPair`
  recursions with full first-order characterisations, and the setup
  family `tsFamily` (`s[i] = seed + i`, a recorded KIT-GAP witness).
* `TwoSum.Machine` — the two pinned `Func`s, the address layout, the
  continuations (inner ones parameterized by the live-pair address),
  the heap fronts, the live-cell lookup/set facts.
* `TwoSum.HarnessR` — entry, setup loop, copy loop, call boundary,
  subject prologue.
* `TwoSum.Subject` — the nested loop's segments, the two inductions,
  and the end-to-end run.

THE HEADLINE is stated HERE, in the root, so the aggregator's
`import GoLeanProofs.Examples.TwoSum` reaches it by name — the
C-H4/C-H5 shape, adopted from birth.
-/

namespace GoLean.Examples.TwoSum

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8`, `seed < 2^64` and `target < 2^64`, running the Go harness
`twosum_harness_r(n, seed, target)` through the machine's native
function entry — empty-heap state, all three arguments at the call
boundary — completes normally past one fuel bound, at every
nondeterminism-choice stream, and returns THREE values: a length-`n`
list `vals` as the fixed-cap array the Go returns, and the index pair
`twoSumSpec vals target` — the FIRST pair `(i, j)` in scan order
(outer index ascending, inner ascending, `i < j`) with
`(vals[i] + vals[j]) % 2^64 = target`, or the sentinel `(n, n)` when
no pair hits. The postcondition is a relation over the RETURNED DATA;
no family function appears in it.

Honesty clauses, all recorded rather than hidden:

* **`twoSumSpec` is a first-search recursion**, shaped like the scan
  it specifies; the genuinely first-order content — "the returned
  pair hits and nothing scan-earlier does, or nothing hits at all" —
  is `twoSumSpec_char`, and `twosum_first_pair` below restates the
  theorem through it with no reference to `twoSumSpec`.
* **The wrapped sum is the claim's arithmetic.** `%(2^64)` is Go's
  uint64 addition on this fragment, written with `Int.emod`; it comes
  from the program's own arithmetic, not from a proof convenience.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[twosumCapN]uint64` with `twosumCapN = 8` (visible in the corpus
  Go) and the copy loop plus zero-padding exist ONLY so the searched
  array can cross the observation boundary.
* **`∃ vals` is still family-determined.** The witness is
  `tsFamily n seed` — the strictly-ascending-modulo-wrap family
  `s[i] = seed + i`, which the corpus rows exercise at both outcomes
  (adjacent hits, interior hits, the no-pair sentinel, `n = 0/1`
  degenerate rows). The statement merely avoids SAYING so. Making the
  input genuine ∀-data needs the ghost rung-1 annotation, which is
  designed and not built.
* **`n = 0` and `n = 1` are included**, and are not degenerate holes:
  no pair exists, both loops fall through, and the sentinel `(n, n)`
  is returned — pinned against `go run` by the corpus rows.
* **Machine idealization** as in the other entries: entry from an
  empty heap, an unbounded heap, allocation always succeeds — the
  per-outer-iteration allocation of the inner counter cells (the
  nested loop's machine cost) never fails.

Fuel bound `N = 57·n² + 212·n + 303` — QUADRATIC, the nested loop's
honest shape, and branch-uniform: `53` per setup iteration, `53` per
copy iteration, at most `n` outer rows of at most `57·(n−1) + 106`
steps each (charged uniformly as `57·n + 106`), the fixed entry/call/
prologue/epilogue overheads, and the found-return tail (`101` from the
hitting test's delivery) absorbed by the row bound. The MEASURED
counts, recorded separately and NOT presented as the bound (the exact
no-pair law is `303 + 206·n + 57·n·(n−1)/2`): `303` at `n = 0`; `509`
at `n = 1`; `772`/`1469`/`3547` at the no-pair rows `n = 2/4/8`; `607`
at `n = 2` hit at `(0,1)`; `713` at `n = 3` hit at `(0,1)`; `933` at
`n = 4` hit at `(0,3)`; `1243` at `n = 8` hit at `(0,1)`. The
measurement depends on WHERE the first hit sits, because the early
return skips everything after it. -/
theorem twosum_ok (n seed target : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (htgt : target < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel twosumLowered.typeDefs.toList
            twosumLowered.funcs twosumHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (target : Int) .uint64]
            twosumLowered.methods ch
          = .ok { values := #[tsArr8 vals,
              .int (twoSumSpec vals (target : Int)).1 .uint64,
              .int (twoSumSpec vals (target : Int)).2 .uint64] } := by
  refine ⟨tsFamily n seed, tsFamily_length n seed,
    57 * n ^ 2 + 212 * n + 303, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, hk, Dr, nar, oiv, hrun⟩ :=
    ts_runT tProg n seed target hcap hseed htgt
      (t_enterFrame_fact n seed target) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  -- the recorded show-bridge (structural: record updates of `tProg`)
  have hst : tHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      ((target : Nat) : Int)
      = tSt tProg (tsHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)
          ((target : Nat) : Int)) 6 := rfl
  rw [tH_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega)
      (by exact_mod_cast hseed),
    unorm_of_range (v := (target : Int)) (by omega)
      (by exact_mod_cast htgt),
    hst, hfold, runConfig_next_stop]
  show (Except.ok { values := #[.array _, .int _ .uint64,
      .int _ .uint64] } : Except GoError Result) = _
  rw [tsArr8, tsPre_full, twoSumSpec_eq_ansF]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those three values. -/
theorem twosum_readout (n seed target : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (htgt : target < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel twosumLowered.typeDefs.toList
            twosumLowered.funcs twosumHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (target : Int) .uint64]
            twosumLowered.methods ch
          = .ok r →
        r = { values := #[tsArr8 vals,
              .int (twoSumSpec vals (target : Int)).1 .uint64,
              .int (twoSumSpec vals (target : Int)).2 .uint64] } := by
  obtain ⟨vals, hlen, htot⟩ := twosum_ok n seed target hcap hseed htgt
  exact ⟨vals, hlen, harness_readout_of_total htot⟩

/-- **The first-order readout of the pair** (statement-TCB doctrine: a
headline ships a corollary a reader can check against the Go without
unfolding `twoSumSpec`): the returned indices are either a genuine
first hit — `i < j < n`, the wrapped sum equals the target, and no
scan-earlier pair hits — or both equal `n` and NO pair hits at all. -/
theorem twosum_first_pair (n seed target : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (htgt : target < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ i j : Int,
          runFunctionWithContextM fuel twosumLowered.typeDefs.toList
              twosumLowered.funcs twosumHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
                .int (target : Int) .uint64]
              twosumLowered.methods ch
            = .ok { values := #[tsArr8 vals, .int i .uint64,
                .int j .uint64] }
          ∧ ((∃ a b : Nat, i = (a : Int) ∧ j = (b : Int)
                ∧ a < b ∧ b < n
                ∧ (vals.getD a 0 + vals.getD b 0) % 2 ^ 64
                    = (target : Int)
                ∧ ∀ a' b' : Nat, a' < b' → b' < n →
                    (a' < a ∨ (a' = a ∧ b' < b)) →
                    ¬ (vals.getD a' 0 + vals.getD b' 0) % 2 ^ 64
                        = (target : Int))
            ∨ (i = (n : Int) ∧ j = (n : Int)
                ∧ ∀ a b : Nat, a < b → b < n →
                    ¬ (vals.getD a 0 + vals.getD b 0) % 2 ^ 64
                        = (target : Int))) := by
  obtain ⟨vals, hlen, N, htot⟩ := twosum_ok n seed target hcap hseed htgt
  refine ⟨vals, hlen, N, fun fuel hfuel ch =>
    ⟨(twoSumSpec vals (target : Int)).1,
     (twoSumSpec vals (target : Int)).2, htot fuel hfuel ch, ?_⟩⟩
  rcases twoSumSpec_char vals ((target : Nat) : Int) with
    ⟨a, b, hspec, hab, hbl, hsum, hmin⟩ | ⟨hspec, hnone⟩
  · exact .inl ⟨a, b, by rw [hspec], by rw [hspec], hab, by omega, hsum,
      fun a' b' h1 h2 h3 => hmin a' b' h1 (by omega) h3⟩
  · exact .inr ⟨by rw [hspec, hlen], by rw [hspec, hlen],
      fun a b h1 h2 => hnone a b h1 (by omega)⟩

end GoLean.Examples.TwoSum
