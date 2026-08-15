import GoLeanProofs.Examples.ArrayPalindrome.HarnessR

/-!
# ArrayPalindrome — the `palin` example (Gallery Campaign G1)

Go source: `Corpus/coverage/exec/examples/palin/main.go`
(differentially green against `go run`, 14 rows). Lowering pinned by
`scripts/check-golden` against `baselines/golden/palin-lowered.repr`
and carried in `GoLeanProofs.Examples.ArrayPalindromeProgram`.

The subject `isPalindrome` walks two indices inward — `i` up from `0`,
`j` down from `len(s)-1` — returning `0` at the FIRST mismatched pair
and `1` if the walk meets in the middle. The harness is the S3
RELATIONAL style: it returns the array it checked (as a fixed-cap
`[8]uint64`) alongside the verdict, so the postcondition is a relation
over the RETURNED DATA — `verdict = palinSpec pre`, where
`palinSpec xs = if xs.reverse = xs then 1 else 0` — with no family
function re-describing the setup inside the claim.

**What the early return costs the proof, and why it is worth saying.**
The subject can leave the loop from two different places, and they are
not symmetric: one is the loop's exit test, the other is a `return`
from inside the body. So the loop induction here does not stop at a
loop head — it runs all the way to the driver terminal, and the theorem
that both exits land on the same observable is the content. That is
also why `i`/`j` are existentially quantified inside the run lemma: the
two exits stop at different indices and nothing the harness returns
depends on which.

The per-phase shards:

* `ArrayPalindrome.Pure` — `palinSpec` and the half-scan bridge
  (`palin_iff_half`): scanning pairs `(t, len−1−t)` for `t < len/2`
  decides `xs.reverse = xs`, which is exactly what the Go loop does.
* `ArrayPalindrome.Machine` — the two pinned `Func`s, the address
  layout, the continuations and the heap fronts.
* `ArrayPalindrome.HarnessR` — the raw segments, the three loop
  inductions and the end-to-end run.

THE HEADLINE is stated HERE, in the root, so that the aggregator's
`import GoLeanProofs.Examples.ArrayPalindrome` reaches it by name — the
C-H4/C-H5 shape the 2026-08-15 audit asked for, adopted from birth.
-/

namespace GoLean.Examples.ArrayPalindrome

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- **THE HEADLINE (§11 harness form, S3 RELATIONAL)**: for every
`n ≤ 8` and every `seed < 2^64`, running the Go harness
`palin_harness_r(n, seed)` through the machine's native function entry
— empty-heap state, both arguments at the call boundary — completes
normally past one fuel bound, at every nondeterminism-choice stream,
and returns TWO values: a length-`n` list `pre` as the fixed-cap array
the Go returns, and the verdict `palinSpec pre` — `1` exactly when
`pre.reverse = pre`. The postcondition is a relation over the RETURNED
DATA; no family function and no index arithmetic appears in it.

Honesty clauses, all recorded rather than hidden:

* **The claim is an equation on the verdict, and `palinSpec` is the
  whole mathematical content.** `palinSpec xs = if xs.reverse = xs then
  1 else 0` — list reversal, defined the way a mathematician would
  write it. The Go program decides it by scanning half the array; that
  half-scan is proof method (`palin_iff_half`), not part of the claim.
* **The cap `n ≤ 8` is a toy bound.** Go's pass-by-value fragment
  cannot return unbounded data, so the harness returns
  `[palinCapN]uint64` with `palinCapN = 8` (visible in the corpus Go)
  and the copy loop plus zero-padding exist ONLY so the checked array
  can cross the observation boundary.
* **`∃ pre` is still family-determined.** The witness is
  `familyMod 2 n seed` — the alternating family `s[i] = seed + i%2`,
  which the corpus rows exercise at BOTH outcomes (verdict `1` for
  `n ≤ 1` and odd `n`, verdict `0` for even `n ≥ 2`). The statement
  merely avoids SAYING so. Making the input genuine ∀-data needs the
  ghost rung-1 annotation, which is designed and not built.
* **`n = 0` is included**, and it is not a degenerate hole: the Go sets
  `j = -1`, the loop never runs, and the empty list IS a palindrome.
  The corpus row `harness-r-empty` pins that against `go run`.
* **Machine idealization** as in the other entries: entry from an empty
  heap, an unbounded heap, allocation always succeeds.

Fuel bound `N = 144·n + 298` — the branch-UNIFORM worst case: `57` per
setup iteration, `53` per copy iteration, `68` per full subject
iteration (of which there are at most `n/2`, charged as `34·n`), plus
the fixed `298` of entry, the three loop exits, the one `enterFrame`,
the subject prologue and the epilogue. The MEASURED counts, recorded
separately and NOT presented as the bound: `277` at `n = 0`, `387` at
`n = 1`, `518`/`738`/`1178` at the even `n = 2/4/8` (a mismatch at the
first pair), `675`/`963` at the odd `n = 3/5` (the walk completes).
The measurement is not affine in `n`, because how far the walk gets
depends on the data. -/
theorem palin_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel palinLowered.typeDefs.toList
            palinLowered.funcs palinHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            palinLowered.methods ch
          = .ok { values := #[palArr8 pre,
                              .int (palinSpec pre) .uint64] } := by
  refine ⟨palFamily n seed, familyMod_length 2 n seed, 144 * n + 298,
    fun fuel hfuel ch => ?_⟩
  obtain ⟨k, iv, jv, hk, hrun⟩ :=
    p_runs_generic pProg n seed hcap (p_enterFrame_fact n seed) ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  -- the recorded show-bridge (structural: record updates of `pProg`)
  have hst : pHSeed ((n : Nat) : Int) ((seed : Nat) : Int)
      = pSt pProg (pHeap0 ((n : Nat) : Int) ((seed : Nat) : Int)) 4 := rfl
  rw [pH_entry_eq, unorm_of_range (v := (n : Int)) (by omega) (by omega),
    unorm_of_range (v := (seed : Int)) (by omega) (by omega),
    hst, hfold, runConfig_next_stop]
  show (Except.ok { values := #[.array _, .int _ .uint64] } :
      Except GoError Result) = _
  rw [palArr8, palPre_full,
    unorm_of_range (palinSpec_range (palFamily n seed)).1
      (palinSpec_range (palFamily n seed)).2]

/-- **The D1 run-conditioned twin**: any successful completion of the
harness entry returns those two values. -/
theorem palin_readout (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel palinLowered.typeDefs.toList
            palinLowered.funcs palinHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            palinLowered.methods ch
          = .ok r →
        r = { values := #[palArr8 pre, .int (palinSpec pre) .uint64] } := by
  obtain ⟨pre, hlen, htot⟩ := palin_ok n seed hcap hseed
  exact ⟨pre, hlen, harness_readout_of_total htot⟩

/-- **The first-order readout of the verdict** (statement-TCB doctrine:
a headline ships a corollary a reader can check against the Go without
unfolding `palinSpec`): the second returned value is `1` exactly when
the first reads the same forwards and backwards. -/
theorem palin_verdict_iff (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ v : Int,
          runFunctionWithContextM fuel palinLowered.typeDefs.toList
              palinLowered.funcs palinHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              palinLowered.methods ch
            = .ok { values := #[palArr8 pre, .int v .uint64] }
          ∧ (v = 1 ↔ pre.reverse = pre) := by
  obtain ⟨pre, hlen, N, htot⟩ := palin_ok n seed hcap hseed
  refine ⟨pre, hlen, N, fun fuel hfuel ch => ⟨palinSpec pre,
    htot fuel hfuel ch, ?_⟩⟩
  rw [palinSpec]
  split <;> simp_all

end GoLean.Examples.ArrayPalindrome
